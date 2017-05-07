// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package irgo translates intermediate representations to Go. (Work In Progress)
package irgo

import (
	"fmt"
	"go/token"
	"io"
	"os"
	"path"
	"path/filepath"
	"runtime"
	"sort"

	"github.com/cznic/internal/buffer"
	"github.com/cznic/ir"
	"github.com/cznic/mathutil"
	"github.com/cznic/xc"
)

const (
	mallocAllign = 2 * ptrSize
	ptrSize      = mathutil.UintPtrBits / 8
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

type typeNfo struct {
	ir.TypeID
	string
}

type cname struct {
	ir.NameID
	exported bool
}

type fn struct {
	f             *ir.FunctionDefinition
	labelsUsed    map[int]struct{}
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
	drops     map[ir.TypeID]struct{}
	f         *fn
	mangled   map[cname]ir.NameID
	obj       []ir.Object
	out       *buffer.Bytes
	postIncs  map[ir.TypeID]struct{}
	qualifier func(*ir.FunctionDefinition) string
	stores    map[ir.TypeID]struct{}
	strTab    map[ir.StringID]int
	strings   buffer.Bytes
	tc        ir.TypeCache
}

func newGen(obj []ir.Object, qualifier func(*ir.FunctionDefinition) string) *gen {
	return &gen{
		builtins:  map[int]string{},
		drops:     map[ir.TypeID]struct{}{},
		mangled:   map[cname]ir.NameID{},
		obj:       obj,
		out:       &buffer.Bytes{},
		postIncs:  map[ir.TypeID]struct{}{},
		qualifier: qualifier,
		stores:    map[ir.TypeID]struct{}{},
		strTab:    map[ir.StringID]int{},
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
	case ir.Struct:
		buf.WriteString("struct{")
		for i, v := range t.(*ir.StructOrUnionType).Fields {
			fmt.Fprintf(buf, "X%v ", i)
			g.typ0(buf, v)
			buf.WriteByte(';')
		}
		buf.WriteString("}")
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

func (g *gen) string(n ir.StringID) int {
	if x, ok := g.strTab[n]; ok {
		return x
	}

	x := roundup(g.strings.Len(), mallocAllign)
	for g.strings.Len() < x {
		g.strings.WriteByte(0)
	}
	g.strTab[n] = x
	g.strings.Write(dict.S(int(n)))
	g.strings.WriteByte(0)
	return x
}

func (g *gen) binop(n *exprNode) {
	g.expression(n.Childs[0])
	switch x := n.Op.(type) {
	case *ir.Add:
		g.w("+")
	case *ir.Geq:
		g.w(">=")
	case *ir.Leq:
		g.w("<=")
	case *ir.Lt:
		g.w("<")
	case *ir.Mul:
		g.w("*")
	case *ir.Sub:
		g.w("-")
	default:
		TODO("%s: %T", n.Op.Pos(), x)
	}
	g.expression(n.Childs[1])
}

func (g *gen) expression(n *exprNode) {
	switch n.Op.(type) {
	case
		*ir.Jnz,
		*ir.Jz,
		*ir.Switch:
		// nop
	default:
		g.w("(")
		defer g.w(")")
	}
	//p := n.Parent
	for _, v := range n.Childs {
		v.Parent = n
	}
	switch x := n.Op.(type) {
	case *ir.Argument:
		if x.Address {
			TODO("%s", x.Pos())
		}

		g.w("(%s)", g.mangle(g.f.f.Arguments[x.Index], false, -1))
	case *ir.Call:
		f := g.obj[x.Index].(*ir.FunctionDefinition)
		if q, ok := g.isBuiltin(x.Index); ok {
			g.w("%s.", q)
		}
		g.w("%s(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
		for _, v := range n.Childs {
			g.expression(v)
			g.w(", ")
		}
		g.w(")")
	case *ir.Const32:
		g.w("int32(%v) ", x.Value)
	case *ir.CallFP:
		g.expression(n.Childs[0])
		g.w("(")
		for _, v := range n.Childs[1:] {
			g.expression(v)
			g.w(", ")
		}
		g.w(")")
	case *ir.Convert:
		if x, ok := n.Childs[0].Op.(*ir.Global); ok && x.NameID == idMain {
			g.expression(n.Childs[0])
			return
		}

		g.w("%v(", g.typ2(x.TypeID))
		g.expression(n.Childs[0])
		g.w(")")
	case *ir.Drop:
		g.drops[x.TypeID] = struct{}{}
		g.w("drop_%d(", x.TypeID)
		g.expression(n.Childs[0])
		g.w(")")
	case *ir.Element:
		if x.Address {
			g.w("&")
		}

		g.w("(")
		g.expression(n.Childs[0])
		g.w("[")
		g.expression(n.Childs[1])
		g.w("]")
		g.w(")")
	case *ir.Field:
		if x.Address {
			g.w("&")
		}

		g.w("(")
		g.expression(n.Childs[0])
		g.w(".X%v)", x.Index)
	case *ir.Global:
		nm := g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1)
		if x.Address {
			switch t := g.tc.MustType(x.TypeID); t.Kind() {
			case ir.Pointer:
				if t.(*ir.PointerType).Element.Kind() == ir.Function {
					g.w("%s", nm)
					return
				}

				g.w("&%s", nm)
				return
			default:
				TODO("%s: %T\n%s", x.Pos(), x, x.TypeID)
			}
		}

		g.w("%s", nm)
	case *ir.Jnz:
		g.w("if")
		g.expression(n.Childs[0])
		g.w("{ goto ")
		switch {
		case x.NameID != 0:
			TODO("%s", x.Pos())
		default:
			g.w("_%v", x.Number)
		}
		g.w("}\n")
	case *ir.Jz:
		g.w("if !(")
		g.expression(n.Childs[0])
		if len(n.Childs[0].Childs) == 0 {
			g.w("!= 0")
		}
		g.w(") { goto ")
		switch {
		case x.NameID != 0:
			TODO("%s", x.Pos())
		default:
			g.w("_%v", x.Number)
		}
		g.w("}\n")
	case *ir.Load:
		g.w("*")
		g.expression(n.Childs[0])
	case
		*ir.Add,
		*ir.Geq,
		*ir.Leq,
		*ir.Lt,
		*ir.Mul,
		*ir.Sub:

		g.binop(n)
	case *ir.PostIncrement:
		g.postIncs[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("postInc_%d(", x.TypeID)
		g.expression(n.Childs[0])
		g.w(", %v(%v))", g.typ2(x.TypeID), x.Delta)
	case *ir.Result:
		if x.Address {
			g.w("&")
		}

		g.w("(r%v)", x.Index)
	case *ir.Store:
		g.stores[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("store_%d(", x.TypeID)
		g.expression(n.Childs[0])
		g.w(", ")
		g.expression(n.Childs[1])
		g.w(")")
	case *ir.StringConst:
		g.w("uintptr(unsafe.Pointer(&strTab[%v]))", g.string(x.Value))
	case *ir.Switch:
		var a switchPairs
		for i, v := range x.Values {
			a = append(a, switchPair{v, &x.Labels[i]})
		}
		sort.Sort(a)
		g.w("switch")
		g.expression(n.Childs[0])
		g.w("{\n")
		for _, v := range a {
			g.w("case ")
			g.value(v.Value)
			g.w(": goto ")
			switch l := v.Label; {
			case l.NameID != 0:
				TODO("%s", x.Pos())
			default:
				g.w("_%v\n", l.Number)
			}
		}
		g.w("default: goto ")
		switch l := x.Default; {
		case l.NameID != 0:
			TODO("%s", x.Pos())
		default:
			g.w("_%v\n", l.Number)
		}
		g.w("}")
	case *ir.Variable:
		if x.Address {
			g.w("&")
		}

		sc := g.f.varDeclScopes[x.Index]
		if sc == 0 {
			sc = -1
		}
		g.w("(%v)", g.mangle(g.f.varDecls[x.Index].NameID, false, sc))
	default:
		TODO("%s: %T", x.Pos(), x)
	}
}

func (g *gen) emit(n *codeNode) {
	for _, op := range n.Ops {
		switch x := op.(type) {
		case *expr:
			g.expression(x.Expr)
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
		case *ir.Jmp:
			g.w("goto ")
			switch {
			case x.NameID != 0:
				g.w("_%v\n", x.NameID)
			default:
				g.w("_%v\n", x.Number)
			}
		case *ir.Label:
			n := int(x.NameID)
			if n == 0 {
				n = -x.Number
			}
			if _, ok := g.f.labelsUsed[n]; !ok {
				break
			}

			switch {
			case x.NameID != 0:
				g.w("_%v:\n", x.NameID)
			default:
				g.w("_%v:\n", x.Number)
			}
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

	//fmt.Printf("====\n%s\n", pretty(f.Body)) //TODO-
	g.f = newFn(g.tc, f)
	ft := g.f.t

	var buf buffer.Bytes

	defer buf.Close()

	g.w("func %v(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
	switch {
	case f.NameID == idMain && len(ft.Arguments) != 2:
		g.w("int32, uintptr) (r0 int32)")
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
			g.w("(r0 %s)", g.typ(ft.Results[0]))
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
		g.w("_ = %v\n", nm)
	}
	var root *codeNode
	root, g.f.labelsUsed = newCodeGraph(g, f.Body)
	m := map[*codeNode]struct{}{}
	var fn func(*codeNode)
	fn = func(n *codeNode) {
		if _, ok := m[n]; ok {
			return
		}

		more := map[*codeNode]struct{}{}
		for ; n != nil; n = n.Fallthrough {
			m[n] = struct{}{}
			g.emit(n)
			for _, v := range n.Out {
				more[v] = struct{}{}
			}
		}
		for v := range more {
			fn(v)
		}
	}
	fn(root)
	if len(ft.Results) != 0 {
		//TODO support multiple results.
		g.w("return r0\n")
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

func (g *gen) helpers(m map[ir.TypeID]struct{}) (r []typeNfo) {
	for k := range m {
		r = append(r, typeNfo{k, k.String()})
	}
	sort.Slice(r, func(i, j int) bool { return r[i].string < r[j].string })
	return r
}

func (g *gen) gen() error {
	g.w(`
func store(p, v interface{}) interface{} {
	switch x := v.(type) {
	case int32:
		*(p.(*int32)) = x
	default:
		panic("TODO539")
	}
	return v
}

`)
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
	if g.strings.Len() != 0 {
		g.w("var strTab = []byte(\"")
		for _, v := range g.strings.Bytes() {
			switch {
			case v == '\\':
				g.out.WriteString(`\\`)
			case v == '"':
				g.out.WriteString(`\"`)
			case v < ' ', v >= 0x7f:
				fmt.Fprintf(g.out, `\x%02x`, v)
			default:
				g.out.WriteByte(v)
			}
		}
		g.w("\")\n")
	}
	for _, v := range g.helpers(g.drops) {
		g.w("func drop_%d(%v) {}\n", v.TypeID, g.typ2(v.TypeID))
	}
	for _, v := range g.helpers(g.postIncs) {
		g.w("func postInc_%d(p *%[2]v, d %[2]v) %[2]v { v := *p; *p += d; return v }\n", v.TypeID, g.typ2(v.TypeID))
	}
	for _, v := range g.helpers(g.stores) {
		g.w("func store_%d(p *%[2]v, v %[2]v) %[2]v { *p = v; return v }\n", v.TypeID, g.typ2(v.TypeID))
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
