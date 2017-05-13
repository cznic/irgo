// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package irgo translates intermediate representations to Go. (Work In Progress)
package irgo

import (
	"fmt"
	"go/token"
	"io"
	"math"
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

type varNfo struct {
	def   *ir.VariableDeclaration
	scope int
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
	f      *ir.FunctionDefinition
	t      *ir.FunctionType
	varNfo []varNfo
}

func newFn(tc ir.TypeCache, f *ir.FunctionDefinition) *fn {
	t := tc.MustType(f.TypeID).(*ir.FunctionType)
	return &fn{
		f:      f,
		t:      t,
		varNfo: varInfo(f.Body),
	}
}

type gen struct {
	builtins  map[int]string // Object#: qualifier.
	copies    map[ir.TypeID]struct{}
	f         *fn
	mangled   map[cname]ir.NameID
	model     ir.MemoryModel
	obj       []ir.Object
	out       *buffer.Bytes
	postIncs  map[ir.TypeID]struct{}
	preIncs   map[ir.TypeID]struct{}
	qualifier func(*ir.FunctionDefinition) string
	stores    map[ir.TypeID]struct{}
	strTab    map[ir.StringID]int
	strings   buffer.Bytes
	tc        ir.TypeCache
}

func newGen(obj []ir.Object, qualifier func(*ir.FunctionDefinition) string) *gen {
	model, err := ir.NewMemoryModel()
	if err != nil {
		panic(err)
	}

	return &gen{
		builtins:  map[int]string{},
		copies:    map[ir.TypeID]struct{}{},
		mangled:   map[cname]ir.NameID{},
		model:     model,
		obj:       obj,
		out:       &buffer.Bytes{},
		postIncs:  map[ir.TypeID]struct{}{},
		preIncs:   map[ir.TypeID]struct{}{},
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
	case ir.Int16:
		buf.WriteString("int16 ")
	case ir.Uint16:
		buf.WriteString("uint16 ")
	case ir.Int32:
		buf.WriteString("int32 ")
	case ir.Uint32:
		buf.WriteString("uint32 ")
	case ir.Int64:
		buf.WriteString("int64 ")
	case ir.Uint64:
		buf.WriteString("uint64 ")
	case ir.Float32:
		buf.WriteString("float32 ")
	case ir.Float64:
		buf.WriteString("float64 ")
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
	case ir.Pointer:
		if t.ID() == idVoidPtr {
			buf.WriteString("uintptr ")
			return
		}

		e := t.(*ir.PointerType).Element
		if e.Kind() != ir.Function {
			buf.WriteByte('*')
		}
		g.typ0(buf, e)
	case ir.Function:
		ft := t.(*ir.FunctionType)
		buf.WriteString("func(")
		for _, v := range ft.Arguments {
			g.typ0(buf, v)
			buf.WriteByte(',')
		}
		buf.WriteByte(')')
		switch len(ft.Results) {
		case 0:
			// nop
		case 1:
			g.typ0(buf, ft.Results[0])
		default:
			TODO("")
		}
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

func (g *gen) relop3(n *exprNode, p bool) {
	switch {
	case p:
		g.w("uintptr(unsafe.Pointer(")
		g.expression(n)
		g.w("))")
	default:
		g.expression(n)
	}
}

func (g *gen) relop2(n *exprNode, op string, p bool) {
	g.relop3(n.Childs[0], p)
	g.w(op)
	g.relop3(n.Childs[1], p)
}

func (g *gen) relop(n *exprNode) {
	g.w("bool2int(")
	p := g.tc.MustType(n.Childs[0].TypeID).Kind() == ir.Pointer || g.tc.MustType(n.Childs[1].TypeID).Kind() == ir.Pointer
	switch x := n.Op.(type) {
	case *ir.Eq:
		g.relop2(n, "==", p)
	case *ir.Geq:
		g.relop2(n, ">=", p)
	case *ir.Gt:
		g.relop2(n, ">", p)
	case *ir.Leq:
		g.relop2(n, "<=", p)
	case *ir.Lt:
		g.relop2(n, "<", p)
	case *ir.Neq:
		g.relop2(n, "!=", p)
	default:
		TODO("%s: %T", n.Op.Pos(), x)
	}
	g.w(")")
}

func (g *gen) binop(n *exprNode) {
	g.expression(n.Childs[0])
	switch x := n.Op.(type) {
	case *ir.Add:
		g.w("+")
	case *ir.And:
		g.w("&")
	case *ir.Div:
		g.w("/")
	case *ir.Mul:
		g.w("*")
	case *ir.Or:
		g.w("|")
	case *ir.Rem:
		g.w("%%")
	case *ir.Sub:
		g.w("-")
	case *ir.Xor:
		g.w("^")
	default:
		TODO("%s: %T", n.Op.Pos(), x)
	}
	g.expression(n.Childs[1])
}

func (g *gen) bool(n *exprNode) {
	g.w("(")
	g.expression(n)
	g.w("!= 0)")
}

func (g *gen) logop(n *exprNode) {
	g.w("bool2int(")
	g.bool(n.Childs[0])
	switch n.Op {
	case land:
		g.w("&&")
	case lor:
		g.w("||")
	default:
		TODO("%v", n.Op)
	}
	g.bool(n.Childs[1])
	g.w(")")
}

func (g *gen) expression(n *exprNode) {
	switch n.Op.(type) {
	case
		*ir.Jnz,
		*ir.Jz,
		*ir.Drop,
		*ir.Switch:

		// nop
	default:
		g.w("(")
		defer g.w(")")
	}
	p := n.Parent
	for _, v := range n.Childs {
		v.Parent = n
	}
	switch x := n.Op.(type) {
	case *ir.Argument:
		if x.Address {
			g.w("&")
		}

		g.w("(%s)", g.mangle(g.f.f.Arguments[x.Index], false, -1))
	case *ir.Bool:
		g.w("bool2int(")
		g.expression(n.Childs[0])
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w("!= nil")
		default:
			g.w("!= 0")
		}
		g.w(")")
	case *ir.Call:
		f := g.obj[x.Index].(*ir.FunctionDefinition)
		if q, ok := g.isBuiltin(x.Index); ok {
			g.w("%s.", q)
		}
		g.w("%s(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
		ft := g.tc.MustType(f.TypeID).(*ir.FunctionType)
		for i, v := range n.Childs {
			var pt ir.Type
			if i < len(ft.Arguments) {
				pt = ft.Arguments[i]
			}
			at := g.tc.MustType(v.TypeID)
			switch {
			case ft.Variadic && i >= len(ft.Arguments) && at.Kind() == ir.Pointer:
				g.w("unsafe.Pointer(")
				g.expression(v)
				g.w(")")
			case pt != nil && pt.Kind() == ir.Pointer && pt.ID() != idVoidPtr && at.ID() == idVoidPtr:
				g.w("(%v)(unsafe.Pointer(", g.typ(pt))
				g.expression(v)
				g.w("))")
			default:
				g.expression(v)
			}
			g.w(", ")
		}
		g.w(")")
	case *ir.CallFP:
		fp := n.Childs[0]
		g.expression(fp)
		ft := g.tc.MustType(fp.TypeID).(*ir.PointerType).Element.(*ir.FunctionType)
		g.w("(")
		for i, v := range n.Childs[1:] {
			switch {
			case ft.Variadic && i >= len(ft.Arguments) && g.tc.MustType(v.TypeID).Kind() == ir.Pointer:
				g.w("unsafe.Pointer(")
				g.expression(v)
				g.w(")")
			default:
				g.expression(v)
			}
			g.w(", ")
		}
		g.w(")")
	case *ir.Const32:
		if p != nil {
			switch p.Op.(type) {
			case *ir.Element:
				switch ptrSize {
				case 4:
					g.w("%v", uint32(x.Value))
				case 8:
					g.w("%v", uint64(x.Value))
				}
				return
			}
		}

		switch x.TypeID {
		case idInt32:
			g.w("int32(%v) ", x.Value)
		default:
			TODO("%s: %v", x.Pos(), x.TypeID)
		}
	case *ir.Const64:
		switch x.TypeID {
		case idFloat64:
			g.w("float64(%v) ", math.Float64frombits(uint64(x.Value)))
		case idInt64:
			g.w("int64(%v) ", x.Value)
		case idUint64:
			g.w("uint64(%v) ", uint64(x.Value))
		default:
			TODO("%s: %v", x.Pos(), x.TypeID)
		}
	case *ir.Convert:
		if x, ok := n.Childs[0].Op.(*ir.Global); ok && x.NameID == idMain {
			g.expression(n.Childs[0])
			return
		}

		g.w("(%v)(", g.typ2(x.Result))
		switch {
		case g.tc.MustType(x.Result).Kind() == ir.Pointer:
			g.w("unsafe.Pointer(")
			switch {
			case g.tc.MustType(n.Childs[0].TypeID).Kind() != ir.Pointer:
				g.w("uintptr(")
				g.expression(n.Childs[0])
				g.w(")")
			default:
				g.expression(n.Childs[0])
			}
			g.w(")")
		default:
			g.expression(n.Childs[0])
		}
		g.w(")")
	case *ir.Copy:
		g.copies[x.TypeID] = struct{}{}
		g.w("copy_%d(", x.TypeID)
		g.expression(n.Childs[0])
		g.w(",")
		g.expression(n.Childs[1])
		g.w(")")
	case *ir.Drop:
		g.w("drop(")
		g.expression(n.Childs[0])
		g.w(")")
	case *ir.Element:
		t := g.tc.MustType(n.Childs[0].TypeID).(*ir.PointerType).Element
		et := t
		if t.Kind() == ir.Array {
			et = t.(*ir.ArrayType).Item
		}
		sz := g.model.Sizeof(et)
		if !x.Address {
			g.w("*")
		}
		g.w("(*%v)(unsafe.Pointer(uintptr(unsafe.Pointer(", g.typ(et))
		g.expression(n.Childs[0])
		s := "+"
		if x.Neg {
			s = "-"
		}
		g.w("))%s%v*uintptr", s, sz)
		g.expression(n.Childs[1])
		g.w("))")
	case *ir.Field:
		if x.Address {
			g.w("&")
		}

		g.w("(")
		g.expression(n.Childs[0])
		g.w(".X%v)", x.Index)
	case *ir.Global:
		t := g.tc.MustType(g.obj[x.Index].Base().TypeID)
		nm := g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1)
		if p != nil {
			switch p.Op.(type) {
			case
				*ir.Call,
				*ir.CallFP,
				*ir.Eq,
				*ir.Store:

				if t.Kind() == ir.Array {
					g.w("&(%v[0])", nm)
					return
				}
			}
		}
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
		g.w("!= 0 { goto ")
		switch {
		case x.NameID != 0:
			TODO("%s", x.Pos())
		default:
			g.w("_%v", x.Number)
		}
		g.w("}\n")
	case *ir.Jz:
		g.w("if")
		g.expression(n.Childs[0])
		g.w("== 0 { goto ")
		switch {
		case x.NameID != 0:
			TODO("%s", x.Pos())
		default:
			g.w("_%v", x.Number)
		}
		g.w("}\n")
	case *ir.Load:
		g.w("*")
		if _, ok := n.Childs[0].Op.(*ir.Dup); ok {
			g.w("p")
			return
		}

		g.expression(n.Childs[0])
	case
		*ir.Eq,
		*ir.Geq,
		*ir.Gt,
		*ir.Leq,
		*ir.Lt,
		*ir.Neq:

		g.relop(n)
	case
		*ir.Add,
		*ir.And,
		*ir.Div,
		*ir.Mul,
		*ir.Or,
		*ir.Rem,
		*ir.Sub,
		*ir.Xor:

		g.binop(n)
	case *ir.Nil:
		g.w("nil")
	case *ir.Not:
		g.w("bool2int(")
		g.expression(n.Childs[0])
		g.w("== 0)")
	case *ir.PostIncrement:
		g.postIncs[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("postInc_%d(", x.TypeID)
		g.expression(n.Childs[0])
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w(", %v)", x.Delta)
		default:
			g.w(", %v(%v))", g.typ2(x.TypeID), x.Delta)
		}
	case *ir.PreIncrement:
		g.preIncs[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("preInc_%d(", x.TypeID)
		g.expression(n.Childs[0])
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w(", %v)", x.Delta)
		default:
			g.w(", %v(%v))", g.typ2(x.TypeID), x.Delta)
		}
	case *ir.PtrDiff:
		sz := g.model.Sizeof(g.tc.MustType(x.PtrType).(*ir.PointerType).Element)
		g.w("%v(((", x.TypeID)
		g.w("uintptr(unsafe.Pointer(")
		g.expression(n.Childs[0])
		g.w("))-uintptr(unsafe.Pointer(")
		g.expression(n.Childs[1])
		g.w(")))/%v)", sz)
		g.w(")")
	case *ir.Result:
		if x.Address {
			g.w("&")
		}

		g.w("(r%v)", x.Index)
	case *ir.Store:
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.stores[x.TypeID] = struct{}{}
		g.w("store_%d(", x.TypeID)
		if _, ok := n.Childs[0].Op.(*ir.Dup); ok {
			t := g.typ2(x.TypeID)
			g.w("func()(*%[1]v, %[1]v){ p := ", t)
			g.expression(n.Childs[0].Childs[0])
			g.w("; return p,")
			g.expression(n.Childs[1])
			g.w("}()")
			g.w(")")
			return
		}

		g.expression(n.Childs[0])
		g.w(", ")
		g.expression(n.Childs[1])
		g.w(")")
	case *ir.StringConst:
		g.w("str(%v)", g.string(x.Value))
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
			g.value(idInt32, v.Value)
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
		nfo := g.f.varNfo[x.Index]
		sc := nfo.scope
		if sc == 0 {
			sc = -1
		}
		if p != nil {
			switch p.Op.(type) {
			case *ir.Call, *ir.CallFP:
				if g.tc.MustType(nfo.def.TypeID).Kind() == ir.Array {
					g.w("&(%v[0])", g.mangle(nfo.def.NameID, false, sc))
					return
				}
			}
		}
		if x.Address {
			g.w("&")
		}
		g.w("%v", g.mangle(nfo.def.NameID, false, sc))
	case xop:
		switch x {
		case lop:
			g.expression(n.Childs[1])
		case land, lor:
			g.logop(n)
		case ternary:
			g.w("func() %v { if ", n.TypeID)
			g.expression(n.Childs[0])
			g.w("!= 0 { return")
			g.expression(n.Childs[1])
			g.w("}; return")
			g.expression(n.Childs[2])
			g.w("}()")
		default:
			TODO("%T(%v)", x, x)
		}
	default:
		TODO("%s: %T\n%s", x.Pos(), x, n.tree())
	}
}

func (g *gen) emit(n *node) {
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

			nfo := g.f.varNfo[x.Index]
			sc := nfo.scope
			if sc == 0 {
				sc = -1
			}
			nm := g.mangle(x.NameID, false, sc)
			g.w("%s = ", nm)
			g.value(x.TypeID, x.Value)
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
			switch {
			case x.NameID != 0:
				g.w("_%v:\n", x.NameID)
			default:
				g.w("goto _%v\n", x.Number)
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

	// fmt.Printf("====\n%s\n", pretty(f.Body)) //TODO-
	// for i, v := range f.Body { //TODO-
	// 	fmt.Printf("%#05x %v\n", i, v) //TODO-
	// } //TODO-
	g.f = newFn(g.tc, f)
	ft := g.f.t

	var buf buffer.Bytes

	defer buf.Close()

	g.w("func %v(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
	switch {
	case f.NameID == idMain && len(ft.Arguments) != 2:
		g.w("int32, **int8) (r0 int32)")
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
	for _, v := range g.f.varNfo {
		sc := v.scope
		if sc == 0 {
			sc = -1
		}
		nm := g.mangle(v.def.NameID, false, sc)
		g.w("var %v %v\n", nm, g.typ2(v.def.TypeID))
		g.w("_ = %v\n", nm)
	}
	nodes := newGraph(g, f.Body)
	for _, v := range nodes {
		g.emit(v)
	}
	g.w("}\n\n")
}

func (g *gen) value(id ir.TypeID, v ir.Value) {
	t := g.tc.MustType(id)
	switch x := v.(type) {
	case *ir.AddressValue:
		if x.Label != 0 {
			TODO("")
			break
		}

		nm := g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1)
		if x.Offset == 0 {
			switch {
			case id == idVoidPtr:
				g.w("(uintptr(unsafe.Pointer(&%v)))", nm)
			default:
				if t.Kind() != ir.Pointer || t.(*ir.PointerType).Element.Kind() != ir.Function {
					g.w("&")
				}
				g.w("%v", nm)
			}
			break
		}

		g.w("(uintptr(unsafe.Pointer(&%v))+%v)", g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1), x.Offset)
	case *ir.CompositeValue:
		switch t := g.tc.MustType(id); t.Kind() {
		case ir.Array:
			et := t.(*ir.ArrayType).Item.ID()
			g.w("%v{", t)
			for _, v := range x.Values {
				g.value(et, v)
				g.w(", ")
			}
			g.w("}")
		default:
			TODO("TODO782 %v", t.Kind())
		}
	case *ir.Float64Value:
		g.w("%v", x.Value)
	case *ir.Int32Value:
		switch t.Kind() {
		case ir.Pointer:
			switch x.Value {
			case 0:
				g.w("nil")
			default:
				TODO("")
			}
		default:
			g.w("%v", x.Value)
		}
	case *ir.StringValue:
		if x.Offset != 0 {
			TODO("")
		}

		g.w("str(%v)", g.string(x.StringID))
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
	g.value(d.TypeID, d.Value)
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
	g.w("func bool2int(b bool) int32 { if b { return 1}; return 0 }\n")
	for _, v := range g.helpers(g.copies) {
		g.w("func copy_%d(d, s *%[2]v) *%[2]v { *d = *s; return d }\n", v.TypeID, g.typ2(v.TypeID))
	}
	g.w("func drop(interface{}) {}\n")
	for _, v := range g.helpers(g.postIncs) {
		switch {
		case g.tc.MustType(v.TypeID).Kind() == ir.Pointer:
			g.w("func postInc_%d(p *%[2]v, d int) %[2]v { q := (*uintptr)(unsafe.Pointer(p)); v := *q; *q += uintptr(d); return (%[2]v)(unsafe.Pointer(v)) }\n", v.TypeID, g.typ2(v.TypeID))
		default:
			g.w("func postInc_%d(p *%[2]v, d %[2]v) %[2]v { v := *p; *p += d; return v }\n", v.TypeID, g.typ2(v.TypeID))
		}
	}
	for _, v := range g.helpers(g.preIncs) {
		switch {
		case g.tc.MustType(v.TypeID).Kind() == ir.Pointer:
			g.w("func preInc_%d(p *%[2]v, d int) %[2]v { q := (*uintptr)(unsafe.Pointer(p)); v := *q + uintptr(d); *q = v; return (%[2]v)(unsafe.Pointer(v)) }\n", v.TypeID, g.typ2(v.TypeID))
		default:
			g.w("func preInc_%d(p *%[2]v, d %[2]v) %[2]v { v := *p + d; *p = v; return v }\n", v.TypeID, g.typ2(v.TypeID))
		}
	}
	for _, v := range g.helpers(g.stores) {
		g.w("func store_%d(p *%[2]v, v %[2]v) %[2]v { *p = v; return v }\n", v.TypeID, g.typ2(v.TypeID))
	}
	if g.strings.Len() != 0 {
		g.w("func str(n int) *int8 { return (*int8)(unsafe.Pointer(&strTab[n]))}\n")
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
