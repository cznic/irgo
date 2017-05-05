// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package irgo

import (
	"fmt"
	"go/token"
	"io"
	"os"
	"path"
	"path/filepath"
	"runtime"

	"github.com/cznic/internal/buffer"
	"github.com/cznic/ir"
	"github.com/cznic/xc"
)

var (
	// Testing amends things for tests.
	Testing bool

	dict = xc.Dict
)

//TODO remove me.
func TODO(msg string, more ...interface{}) string { //TODOOK
	_, fn, fl, _ := runtime.Caller(1)
	fmt.Fprintf(os.Stderr, "%s:%d: %v\n", path.Base(fn), fl, fmt.Sprintf(msg, more...))
	os.Stderr.Sync()
	panic(fmt.Errorf("%s:%d: TODO %v", path.Base(fn), fl, fmt.Sprintf(msg, more...)))
}

type cname struct {
	ir.NameID
	exported bool
}

type fn struct {
	f             *ir.FunctionDefinition
	t             *ir.FunctionType
	varDeclScopes []int
	varDecls      []*ir.VariableDeclaration
}

func newFn(tc ir.TypeCache, f *ir.FunctionDefinition) *fn {
	t := tc.MustType(f.TypeID).(*ir.FunctionType)
	varDecls, varDeclScopes := varInfo(f.Body)
	return &fn{
		f:             f,
		t:             t,
		varDeclScopes: varDeclScopes,
		varDecls:      varDecls,
	}
}

type gen struct {
	builtins  map[int]string // Object#: qualifier.
	f         *fn
	mangled   map[cname]ir.NameID
	obj       []ir.Object
	out       *buffer.Bytes
	qualifier func(*ir.FunctionDefinition) string
	tc        ir.TypeCache
}

func newGen(obj []ir.Object, qualifier func(*ir.FunctionDefinition) string) *gen {
	return &gen{
		builtins:  map[int]string{},
		mangled:   map[cname]ir.NameID{},
		obj:       obj,
		out:       &buffer.Bytes{},
		qualifier: qualifier,
		tc:        ir.TypeCache{},
	}
}

func (g *gen) mangle(nm ir.NameID, exported bool, index int) ir.NameID {
	k := cname{nm, exported}
	if x, ok := g.mangled[k]; ok {
		return x
	}

	var buf buffer.Bytes

	defer buf.Close()

	switch {
	case exported:
		if index >= 0 {
			panic("internal error")
		}

		buf.WriteByte('X')
	default:
		if index >= 0 {
			fmt.Fprintf(&buf, "_%v", index)
		}
		buf.WriteByte('_')
	}

	for _, v := range dict.S(int(nm)) {
		switch {
		case v < ' ' || v >= 0x7f:
			fmt.Fprintf(&buf, "Ø%02x", v)
		default:
			buf.WriteByte(v)
		}
	}
	id := ir.NameID(dict.ID(buf.Bytes()))
	g.mangled[k] = id
	return id
}

func (g *gen) w(msg string, arg ...interface{}) {
	if _, err := fmt.Fprintf(g.out, msg, arg...); err != nil {
		panic(err)
	}
}

func (g *gen) typ0(buf *buffer.Bytes, t ir.Type) {
	switch t.Kind() {
	case ir.Int8:
		buf.WriteString("int8 ")
	case ir.Int32:
		buf.WriteString("int32 ")
	case ir.Uint64:
		buf.WriteString("uint64 ")
	case ir.Float32:
		buf.WriteString("float32 ")
	case ir.Float64:
		buf.WriteString("float64 ")
	case ir.Pointer:
		buf.WriteString("uintptr ")
	case ir.Array:
		at := t.(*ir.ArrayType)
		fmt.Fprintf(buf, "[%v]", at.Items)
		g.typ0(buf, at.Item)
	default:
		TODO("%v", t.Kind())
	}
}

func (g *gen) typ(t ir.Type) ir.NameID {
	var buf buffer.Bytes

	defer buf.Close()

	g.typ0(&buf, t)
	return ir.NameID(dict.ID(buf.Bytes()))
}

func (g *gen) typ2(t ir.TypeID) ir.NameID { return g.typ(g.tc.MustType(t)) }

func (g *gen) isBuiltin(i int) (string, bool) {
	if s, ok := g.builtins[i]; ok {
		return s, ok
	}

	f := g.obj[i]
	if x, ok := f.(*ir.FunctionDefinition); ok && len(x.Body) == 1 {
		if _, ok := x.Body[0].(*ir.Panic); ok {
			s := g.qualifier(x)
			g.builtins[i] = s
			return s, true
		}
	}

	return "", false
}

func (g *gen) pos(p token.Position) token.Position {
	if p.Filename != "" {
		p.Filename = filepath.Base(p.Filename)
	}
	return p
}

func (g *gen) expression(p, n *exprNode) {
	switch x := n.Op.(type) {
	case *ir.Argument:
		if x.Address {
			TODO("%s", x.Pos())
		}

		g.w(" %s", g.mangle(g.f.f.Arguments[x.Index], false, -1))
	case *ir.Call:
		f := g.obj[x.Index].(*ir.FunctionDefinition)
		if q, ok := g.isBuiltin(x.Index); ok {
			g.w(" %s.", q)
		}
		g.w(" %s(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
		for _, v := range n.Childs {
			g.expression(n, v)
			g.w(", ")
		}
		g.w(")")
	case *ir.Const32:
		g.w(" %v ", x.Value)
	case *ir.CallFP:
		g.expression(n, n.Childs[0])
		g.w("(")
		for _, v := range n.Childs[1:] {
			g.expression(n, v)
			g.w(", ")
		}
		g.w(")")
	case *ir.Convert:
		if x, ok := n.Childs[0].Op.(*ir.Global); ok && x.NameID == idMain {
			g.expression(n, n.Childs[0])
			break
		}

		g.w(" %v(", g.typ2(x.TypeID))
		g.expression(n, n.Childs[0])
		g.w(")")
	case *ir.Drop:
		switch ch := n.Childs[0]; x := ch.Op.(type) {
		case
			*ir.Call,
			*ir.Store:
			g.expression(n, ch)
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	case *ir.Global:
		g.w(" %s", g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1))
	case *ir.Result:
		if x.Index != 0 {
			TODO("%s", x.Pos())
		}

		if x.Address {
			if p != nil {
				if _, ok := p.Op.(*ir.Store); ok {
					g.w(" r")
					break
				}
			}
			TODO("%s", x.Pos())
		}

		TODO("%s", x.Pos())
	case *ir.Store:
		if p != nil {
			if _, ok := p.Op.(*ir.Drop); ok { // Plain assignment.
				g.expression(n, n.Childs[0])
				g.w(" = ")
				g.expression(n, n.Childs[1])
				break
			}
		}

		TODO("%s", x.Pos())
	case *ir.StringConst:
		g.w(` 0 /*TODO258*/ `)
	case *ir.Variable:
		sc := g.f.varDeclScopes[x.Index]
		if sc == 0 {
			sc = -1
		}
		nm := g.mangle(g.f.varDecls[x.Index].NameID, false, sc)
		if x.Address {
			if p != nil {
				if _, ok := p.Op.(*ir.Store); ok {
					g.w(" %s", nm)
					break
				}
			}
			TODO("%s", x.Pos())
		}

		g.w(" %s", nm)
	default:
		TODO("%s: %T", x.Pos(), x)
	}
}

func (g *gen) emit(m map[*codeNode]struct{}, n *codeNode) {
	if _, ok := m[n]; ok {
		return
	}

	m[n] = struct{}{}
	for _, op := range n.Ops {
		switch x := op.(type) {
		case *expr:
			g.expression(nil, x.Expr)
			g.w("\n")
		case *ir.Return:
			g.w("return\n")
		case *ir.VariableDeclaration:
			if x.Value == nil {
				break
			}

			sc := g.f.varDeclScopes[x.Index]
			if sc == 0 {
				sc = -1
			}
			nm := g.mangle(x.NameID, false, sc)
			g.w("%s = ", nm)
			g.value(x.Value)
			g.w("\n")
		case
			*ir.AllocResult,
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope:
			// nop
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	}
}

func (g *gen) functionDefinition(oi int, f *ir.FunctionDefinition) {
	if _, ok := g.isBuiltin(oi); ok {
		return
	}

	g.f = newFn(g.tc, f)
	ft := g.f.t

	var buf buffer.Bytes

	defer buf.Close()

	g.w("func %v(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
	switch {
	case f.NameID == idMain && len(ft.Arguments) != 2:
		g.w("int32, uintptr) (r int32)")
	default:
		for i, v := range ft.Arguments {
			if i < len(f.Arguments) {
				g.w("%v ", g.mangle(f.Arguments[i], false, -1))
			}
			g.w("%s,", g.typ(v))
		}
		g.w(")")
		if len(ft.Results) != 0 {
			//TODO support multiple results.
			g.w("(r %s)", g.typ(ft.Results[0]))
		}
	}
	g.w("{ // %v\n", g.pos(f.Position))
	for i, v := range g.f.varDecls {
		sc := g.f.varDeclScopes[i]
		if sc == 0 {
			sc = -1
		}
		nm := g.mangle(v.NameID, false, sc)
		g.w("var %v %v\n", nm, g.typ2(v.TypeID))
	}
	root := newCodeGraph(g, f.Body)
	switch root.size() {
	case 0:
		panic("internal error")
	case 1:
		g.emit(map[*codeNode]struct{}{}, root)
	default:
		TODO("")
	}
	if len(ft.Results) != 0 {
		//TODO support multiple results.
		g.w("return r\n")
	}
	g.w("}\n\n")
}

func (g *gen) value(v ir.Value) {
	switch x := v.(type) {
	case *ir.AddressValue:
		if x.Label != 0 {
			TODO("")
			break
		}

		g.w(" (uintptr(unsafe.Pointer(&%v))+%v)", g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1), x.Offset)
	case *ir.Int32Value:
		g.w(" %v ", x.Value)
	default:
		TODO("%T", x)
	}
}

func (g *gen) dataDefinition(d *ir.DataDefinition) {
	nm := g.mangle(d.NameID, d.Linkage == ir.ExternalLinkage, -1)
	g.w("var %s %s // %s\n\n", nm, g.typ2(d.TypeID), g.pos(d.Position))
	if d.Value == nil {
		return
	}

	g.w("func init() {\n")
	g.w("%s = ", nm)
	g.value(d.Value)
	g.w("\n}\n\n")
}

func (g *gen) gen() error {
	for i, v := range g.obj {
		switch x := v.(type) {
		case *ir.FunctionDefinition:
			g.functionDefinition(i, x)
		case *ir.DataDefinition:
			g.dataDefinition(x)
		default:
			panic("internal error")
		}
	}
	return nil
}

// New writes Go code generated from obj to out. No package clause is
// generated.  The result is not formatted. The qualifier function is called
// for implementation defined functions.  It must return the package qualifier,
// if any, that should be used to call the implementation defined function.
func New(obj []ir.Object, out io.Writer, qualifier func(*ir.FunctionDefinition) string) (err error) {
	var g *gen
	if !Testing {
		defer func() {
			switch x := recover().(type) {
			case nil:
				_, err = g.out.WriteTo(out)
			case error:
				err = x
			default:
				err = fmt.Errorf("irgo.New: PANIC: %v", x)
			}
			if e := g.out.Close(); e != nil && err == nil {
				err = e
			}
		}()
	}

	g = newGen(obj, qualifier)
	return g.gen()

}
