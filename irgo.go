// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//TODO vararg ap is incorrect

// Package irgo translates intermediate representations to Go. (Work In Progress)
package irgo

import (
	"bytes"
	"fmt"
	"go/token"
	"io"
	"math"
	"os"
	"path"
	"path/filepath"
	"runtime"
	"sort"
	"unsafe"

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
	index    int
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
	fns       map[ir.NameID]*ir.FunctionDefinition
	labels    map[int]bool
	mangled   map[cname]ir.NameID
	model     ir.MemoryModel
	obj       []ir.Object
	out       *buffer.Bytes
	postIncs  map[ir.TypeID]struct{}
	preIncs   map[ir.TypeID]struct{}
	qualifier func(*ir.FunctionDefinition) string
	storebits map[ir.TypeID]struct{}
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

	g := &gen{
		builtins:  map[int]string{},
		copies:    map[ir.TypeID]struct{}{},
		fns:       map[ir.NameID]*ir.FunctionDefinition{},
		mangled:   map[cname]ir.NameID{},
		model:     model,
		obj:       obj,
		out:       &buffer.Bytes{},
		postIncs:  map[ir.TypeID]struct{}{},
		preIncs:   map[ir.TypeID]struct{}{},
		qualifier: qualifier,
		storebits: map[ir.TypeID]struct{}{},
		stores:    map[ir.TypeID]struct{}{},
		strTab:    map[ir.StringID]int{},
		tc:        ir.TypeCache{},
	}
	for _, v := range obj {
		switch x := v.(type) {
		case *ir.FunctionDefinition:
			nm := g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1)
			g.fns[nm] = x
		}
	}
	return g
}

func (g *gen) mangle(nm ir.NameID, exported bool, index int) ir.NameID {
	k := cname{nm, exported, index}
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
	case ir.Uint8:
		buf.WriteString("uint8 ")
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
	case ir.Complex64:
		buf.WriteString("complex64 ")
	case ir.Complex128:
		buf.WriteString("complex128 ")
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
	case ir.Union:
		buf.WriteString("struct{X [0]struct{")
		for i, v := range t.(*ir.StructOrUnionType).Fields {
			fmt.Fprintf(buf, "X%v ", i)
			g.typ0(buf, v)
			buf.WriteByte(';')
		}
		fmt.Fprintf(buf, "}; U [%v]byte", g.model.Sizeof(t))
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

func (g *gen) pcmp(n *exprNode, op string) {
	t := g.tc.MustType(n.Childs[0].TypeID)
	u := g.tc.MustType(n.Childs[1].TypeID)
	if t.Kind() == ir.Pointer && t.(*ir.PointerType).Element.Kind() == ir.Function {
		// *(*unsafe.Pointer)(unsafe.Pointer(&struct{f t}{e}))
		g.w("*(*unsafe.Pointer)(unsafe.Pointer(&struct{f %v}{", g.typ(t))
		g.expression(n.Childs[0], false)
		g.w("}))")
		g.w("%s", op)
		g.w("*(*unsafe.Pointer)(unsafe.Pointer(&struct{f %v}{", g.typ(u))
		g.expression(n.Childs[1], false)
		g.w("}))")
		return
	}

	g.w("uintptr(unsafe.Pointer")
	g.expression(n.Childs[0], false)
	g.w(") %v uintptr(unsafe.Pointer", op)
	g.expression(n.Childs[1], false)
	g.w(")")
}

func (g *gen) relop(n *exprNode) {
	g.w("bool2int(")
	t := g.tc.MustType(n.Childs[0].TypeID)
	u := g.tc.MustType(n.Childs[1].TypeID)
	switch {
	case t.Kind() == ir.Pointer:
		switch n.Op.(type) {
		case *ir.Eq:
			if t.ID() == u.ID() {
				g.expression(n.Childs[0], false)
				g.w("==")
				g.expression(n.Childs[1], false)
				break
			}

			g.pcmp(n, "==")
		case *ir.Geq:
			g.pcmp(n, ">=")
		case *ir.Gt:
			g.pcmp(n, ">")
		case *ir.Leq:
			g.pcmp(n, "<=")
		case *ir.Lt:
			g.pcmp(n, "<")
		case *ir.Neq:
			if t.ID() == u.ID() {
				g.expression(n.Childs[0], false)
				g.w("!=")
				g.expression(n.Childs[1], false)
				break
			}

			g.pcmp(n, "!=")
		default:
			panic("internal error")
		}
	default:
		g.expression(n.Childs[0], false)
		switch n.Op.(type) {
		case *ir.Eq:
			g.w("==")
		case *ir.Geq:
			g.w(">=")
		case *ir.Gt:
			g.w(">")
		case *ir.Leq:
			g.w("<=")
		case *ir.Lt:
			g.w("<")
		case *ir.Neq:
			g.w("!=")
		default:
			panic("internal error")
		}
		g.expression(n.Childs[1], false)
	}
	g.w(")")
}

func (g *gen) binop(n *exprNode) {
	t := g.tc.MustType(n.Childs[0].TypeID)
	if t.Kind() == ir.Pointer {
		g.w("(%v)(unsafe.Pointer(", g.typ(t))
		g.w("uintptr(unsafe.Pointer")
		g.expression(n.Childs[0], false)
		g.w(")")
		switch x := n.Op.(type) {
		case *ir.Add:
			g.w("+")
		case *ir.Mul:
			g.w("*")
		case *ir.Sub:
			g.w("-")
		default:
			TODO("%s: %T", n.Op.Pos(), x)
		}
		g.w("uintptr(unsafe.Pointer")
		g.expression(n.Childs[1], false)
		g.w(")")
		g.w("))")
		return
	}

	g.expression(n.Childs[0], false)
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
	g.expression(n.Childs[1], false)
}

func (g *gen) shift(n *exprNode) {
	g.expression(n.Childs[0], false)
	switch x := n.Op.(type) {
	case *ir.Lsh:
		g.w("<<")
	case *ir.Rsh:
		g.w(">>")
	default:
		TODO("%s: %T", n.Op.Pos(), x)
	}
	g.w("uint")
	g.expression(n.Childs[1], false)
}

func (g *gen) bool(n *exprNode) {
	g.w("(")
	g.expression(n, false)
	g.w("!= 0)")
}

func (g *gen) call(ft *ir.FunctionType, args []*exprNode) {
	g.w("(")
	for i, v := range args {
		var pt ir.Type
		if i < len(ft.Arguments) {
			pt = ft.Arguments[i]
		}
		at := g.tc.MustType(v.TypeID)
		switch {
		case ft.Variadic && i >= len(ft.Arguments) && at.Kind() == ir.Pointer:
			et := at.(*ir.PointerType).Element
			switch et.Kind() {
			case ir.Function:
				// *(*unsafe.Pointer)(unsafe.Pointer(&struct{f t}{e}))
				g.w("*(*unsafe.Pointer)(unsafe.Pointer(&struct{f %v}{", g.typ(et))
				g.expression(v, false)
				g.w("}))")
			default:
				g.w("unsafe.Pointer")
				g.expression(v, false)
			}
		case pt != nil && pt.Kind() == ir.Pointer && pt.ID() != idVoidPtr && isTransitiveVoidPtr(at):
			g.w("(%v)(unsafe.Pointer(", g.typ(pt))
			g.expression(v, false)
			g.w("))")
		case pt != nil && isTransitiveVoidPtr(pt) && at.Kind() == ir.Pointer && !isTransitiveVoidPtr(at):
			g.w("uintptr(unsafe.Pointer")
			g.expression(v, false)
			g.w(")")
		default:
			g.expression(v, false)
		}
		g.w(", ")
	}
	g.w(")")
}

func (g *gen) expression(n *exprNode, void bool) {
	switch n.Op.(type) {
	case
		*ir.Jnz,
		*ir.Jz,
		*ir.Switch:

		// nop
	default:
		if !void {
			g.w("(")
			defer g.w(")")
		}
	}
	p := n.Parent
	for _, v := range n.Childs {
		v.Parent = n
	}

	var t ir.Type
	if id := n.TypeID; id != 0 {
		t = g.tc.MustType(id)
	}

	var a []*exprNode
	for c := n.Comma; c != nil; c = c.Comma {
		a = append(a, c)
	}
	if len(a) != 0 {
		if n.TypeID == 0 {
			TODO("%s:\n%s", n.Op.Pos(), pretty(n))
		}
		g.w("func() %v {", g.typ2(n.TypeID))
		for _, v := range a {
			v.Comma = nil
		}
		for i := len(a) - 1; i >= 0; i-- {
			g.expression(a[i], true)
			g.w(";")
		}
		g.w("return (")
		defer g.w(")}()")
	}
	switch x := n.Op.(type) {
	case *ir.Argument:
		if x.Address {
			g.w("&")
		}

		g.w("(%s)", g.mangle(g.f.f.Arguments[x.Index], false, -1))
	case *ir.Bool:
		g.w("bool2int(")
		t := g.tc.MustType(n.Childs[0].TypeID)
		g.expression(n.Childs[0], false)
		switch {
		case t.Kind() == ir.Pointer && t.ID() != idVoidPtr:
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
		g.w("%s", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1))
		ft := g.tc.MustType(f.TypeID).(*ir.FunctionType)
		g.call(ft, n.Childs)
	case *ir.CallFP:
		fp := n.Childs[0]
		g.expression(fp, false)
		ft := g.tc.MustType(fp.TypeID).(*ir.PointerType).Element.(*ir.FunctionType)
		g.call(ft, n.Childs[1:])
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

		switch t := g.tc.MustType(x.TypeID); t.Kind() {
		case ir.Pointer:
			g.w("uintptr(%v)", uintptr(x.Value))
		case ir.Int8:
			g.w("int8(%v) ", int8(x.Value))
		case ir.Uint8:
			g.w("byte(%v) ", byte(x.Value))
		case ir.Int16:
			g.w("int16(%v) ", int16(x.Value))
		case ir.Uint16:
			g.w("uint16(%v) ", uint16(x.Value))
		case ir.Int32:
			g.w("int32(%v) ", x.Value)
		case ir.Uint32:
			g.w("uint32(%v) ", uint32(x.Value))
		case ir.Float32:
			g.w("float32(%v) ", math.Float32frombits(uint32(x.Value)))
		default:
			TODO("%s: %v", x.Pos(), x.TypeID)
		}
	case *ir.Const64:
		switch x.TypeID {
		case idComplex64:
			g.w("complex(float32(%v), 0) ", math.Float64frombits(uint64(x.Value)))
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
			g.expression(n.Childs[0], false)
			return
		}

		e := n.Childs[0]
		t := g.tc.MustType(x.Result)
		if t.Kind() == ir.Pointer {
			et := t.(*ir.PointerType).Element
			if et.Kind() == ir.Function {
				switch y := e.Op.(type) {
				case *ir.Const32:
					if y.Value == 0 {
						g.w("nil")
						return
					}

					TODO("%s: %T", e.Op.Pos(), y)
				default:
					// *(*t)(unsafe.Pointer(&struct{f t0}{e}))
					g.w("*(*%v)(unsafe.Pointer(&struct{f %v}{", g.typ(t), g.typ2(x.TypeID))
					g.expression(e, false)
					g.w("}))")
					return
				}
			}
		}

		g.w("(%v)(", g.typ2(x.Result))
		switch {
		case t.Kind() == ir.Pointer:
			g.w("unsafe.Pointer(")
			switch {
			case g.tc.MustType(e.TypeID).Kind() != ir.Pointer:
				g.w("uintptr")
				g.expression(e, false)
			default:
				g.expression(e, false)
			}
			g.w(")")
		default:
			g.expression(e, false)
		}
		g.w(")")
	case *ir.Copy:
		if void {
			g.w("*")
			g.expression(n.Childs[0], false)
			g.w("= *")
			g.expression(n.Childs[1], false)
			return
		}

		g.copies[x.TypeID] = struct{}{}
		g.w("copy_%d(", x.TypeID)
		g.expression(n.Childs[0], false)
		g.w(",")
		g.expression(n.Childs[1], false)
		g.w(")")
	case *ir.Cpl:
		g.w("^")
		g.expression(n.Childs[0], false)
	case *ir.Drop:
		switch y := n.Childs[0]; y.Op.(type) {
		case
			*ir.Call,
			*ir.Copy,
			*ir.Label,
			*ir.PostIncrement,
			*ir.PreIncrement,
			*ir.Store:

			g.expression(y, true)
		default:
			g.w("drop(")
			g.expression(n.Childs[0], false)
			g.w(")")
		}
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
		g.w("(*%v)(unsafe.Pointer(uintptr(unsafe.Pointer", g.typ(et))
		g.expression(n.Childs[0], false)
		s := "+"
		if x.Neg {
			s = "-"
		}
		switch {
		case sz == 1:
			g.w(")%suintptr", s)
		default:
			g.w(")%s%v*uintptr", s, sz)
		}
		g.expression(n.Childs[1], false)
		g.w("))")
	case *ir.Field:
		switch t := g.tc.MustType(n.Childs[0].TypeID).(*ir.PointerType).Element; t.Kind() {
		case ir.Union:
			if !x.Address {
				g.w("*")
			}
			g.w("(*%v)(unsafe.Pointer", g.typ(t.(*ir.StructOrUnionType).Fields[x.Index]))
			g.expression(n.Childs[0], false)
			g.w(")")
		default:
			if x.Address {
				g.w("&")
			}
			g.w("(")
			g.expression(n.Childs[0], false)
			g.w(".X%v)", x.Index)
		}
	case *ir.Global:
		nm := g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1)
		t := g.tc.MustType(n.TypeID)
		if t.Kind() == ir.Pointer && t.(*ir.PointerType).Element.Kind() == ir.Array {
			g.w("&(%v[0])", nm)
			return
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
		g.expression(n.Childs[0], false)
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
		g.expression(n.Childs[0], false)
		g.w("== 0 { goto ")
		switch {
		case x.NameID != 0:
			TODO("%s", x.Pos())
		default:
			g.w("_%v", x.Number)
		}
		g.w("}\n")
	case *ir.Label:
		if x.Cond {
			g.w("func() %v { if ", g.typ2(n.TypeID))
			g.expression(n.Childs[0], false)
			g.w("!= 0 { return")
			g.expression(n.Childs[1], false)
			g.w("}; return")
			g.expression(n.Childs[2], false)
			g.w("}()")
			return
		}

		g.w("bool2int(")
		g.expression(n.Childs[0], false)
		g.w("!= 0")
		switch {
		case x.LAnd:
			g.w("&&")
		case x.LOr:
			g.w("||")
		default:
			panic("internal error")
		}
		g.expression(n.Childs[1], false)
		g.w("!= 0)")
	case *ir.Load:
		g.w("*")
		if _, ok := n.Childs[0].Op.(*ir.Dup); ok {
			g.w("p")
			return
		}

		g.expression(n.Childs[0], false)
	case
		*ir.Lsh,
		*ir.Rsh:

		g.shift(n)
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
	case *ir.Neg:
		g.w("-")
		g.expression(n.Childs[0], false)
	case *ir.Not:
		g.w("bool2int(")
		g.expression(n.Childs[0], false)
		g.w("== 0)")
	case *ir.PostIncrement:
		if void {
			switch {
			case t.Kind() == ir.Pointer:
				g.w("*(*uintptr)(unsafe.Pointer")
				g.expression(n.Childs[0], false)
				g.w(") += uintptr(%v)", uintptr(x.Delta))
			default:
				g.w("*")
				g.expression(n.Childs[0], false)
				g.w("+= %v", x.Delta)
			}
			return
		}

		g.postIncs[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("postInc_%d(", x.TypeID)
		g.expression(n.Childs[0], false)
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w(", %v)", x.Delta)
		default:
			g.w(", %v(%v))", g.typ2(x.TypeID), x.Delta)
		}
	case *ir.PreIncrement:
		if void {
			switch {
			case t.Kind() == ir.Pointer:
				g.w("*(*uintptr)(unsafe.Pointer")
				g.expression(n.Childs[0], false)
				g.w(") += uintptr(%v)", uintptr(x.Delta))
			default:
				g.w("*")
				g.expression(n.Childs[0], false)
				g.w("+= %v", x.Delta)
			}
			return
		}

		g.preIncs[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("preInc_%d(", x.TypeID)
		g.expression(n.Childs[0], false)
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w(", %v)", x.Delta)
		default:
			g.w(", %v(%v))", g.typ2(x.TypeID), x.Delta)
		}
	case *ir.PtrDiff:
		sz := g.model.Sizeof(g.tc.MustType(x.PtrType).(*ir.PointerType).Element)
		g.w("%v(((", x.TypeID)
		g.w("uintptr(unsafe.Pointer")
		g.expression(n.Childs[0], false)
		g.w(")-uintptr(unsafe.Pointer")
		g.expression(n.Childs[1], false)
		g.w("))/%v)", sz)
		g.w(")")
	case *ir.Result:
		if x.Address {
			g.w("&")
		}

		g.w("(r%v)", x.Index)
	case *ir.Store:
		_, asop := n.Childs[0].Op.(*ir.Dup)
		t := g.tc.MustType(n.Childs[0].TypeID)
		u := g.tc.MustType(n.Childs[1].TypeID)
		if x.Bits != 0 {
			m := (uint64(1)<<uint(x.Bits) - 1) << uint(x.BitOffset)
			if void {
				if asop {
					TODO("%s", x.Pos())
					return
				}

				TODO("%s", x.Pos())
				return
			}

			g.storebits[x.TypeID] = struct{}{}
			g.w("storebits_%d(", x.TypeID)
			if asop {
				g.expression(n.Childs[0].Childs[0], false)
				g.w(", (")
				g.expression(n.Childs[1], false)
				g.w("<<%v), %v, %v)", x.BitOffset, m, x.BitOffset)
				return
			}

			g.expression(n.Childs[0], false)
			g.w(", (")
			g.expression(n.Childs[1], false)
			g.w("<<%v), %v, %v)", x.BitOffset, m, x.BitOffset)
			return
		}

		if void {
			if asop {
				g.w("{ p := ")
				g.expression(n.Childs[0].Childs[0], false)
				g.w("; *p =")
				g.expression(n.Childs[1], false)
				g.w("}")
				return
			}

			g.w("*")
			switch {
			case isTransitiveVoidPtr(t):
				switch {
				case isTransitiveVoidPtr(u):
					g.expression(n.Childs[0], false)
					g.w("=")
					g.expression(n.Childs[1], false)
				default:
					g.expression(n.Childs[0], false)
					g.w("=")
					g.w("uintptr(unsafe.Pointer")
					g.expression(n.Childs[1], false)
					g.w(")")
				}
			default:
				switch {
				case isTransitiveVoidPtr(u):
					g.expression(n.Childs[0], false)
					g.w("=")
					g.w("(%v)(unsafe.Pointer", g.typ(t.(*ir.PointerType).Element))
					g.expression(n.Childs[1], false)
					g.w(")")
				default:
					g.expression(n.Childs[0], false)
					g.w("=")
					g.expression(n.Childs[1], false)
				}
			}
			return
		}

		g.stores[x.TypeID] = struct{}{}
		g.w("store_%d(", x.TypeID)
		if asop {
			g.w("func()(*%[1]v, %[1]v){ p := ", g.typ2(x.TypeID))
			g.expression(n.Childs[0].Childs[0], false)
			g.w("; return p,")
			g.expression(n.Childs[1], false)
			g.w("}()")
			g.w(")")
			return
		}

		g.expression(n.Childs[0], false)
		g.w(", ")
		switch {
		case !isTransitiveVoidPtr(t) && isTransitiveVoidPtr(u):
			g.w("(%v)(unsafe.Pointer", g.typ(t.(*ir.PointerType).Element))
			g.expression(n.Childs[1], false)
			g.w(")")
		default:
			g.expression(n.Childs[1], false)
		}
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
		g.expression(n.Childs[0], false)
		g.w("{\n")
		for _, v := range a {
			g.w("case ")
			g.value(x.Pos(), idInt32, v.Value)
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
		g.w("}\n")
	case *ir.Variable:
		nfo := g.f.varNfo[x.Index]
		sc := nfo.scope
		if sc == 0 {
			sc = -1
		}
		if p != nil {
			switch p.Op.(type) {
			case *ir.Call, *ir.CallFP, *ir.Store:
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
	default:
		//TODO("%s: %T\n%s", x.Pos(), x, n.tree())
		TODO("%s: %T", x.Pos(), x)
	}
}

func (g *gen) emit(n *node) {
	for _, op := range n.Ops {
		switch x := op.(type) {
		case *expr:
			g.expression(x.Expr, true)
			g.w("\n")
		case *ir.Return:
			g.w("return\n\n")
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
			g.value(x.Pos(), x.TypeID, x.Value)
			g.w("\n")
		case *ir.Jmp:
			g.w("goto ")
			switch {
			case x.NameID != 0:
				g.w("_%v\n", x.NameID)
			default:
				g.w("_%v\n", x.Number)
			}
			g.w("\n")
		case *ir.Label:
			if !g.labels[label(x)] {
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

func (g *gen) collectLabels(nodes []*node) {
	g.labels = map[int]bool{}
	for _, v := range nodes {
		for _, op := range v.Ops {
			switch x := op.(type) {
			case *expr:
				switch y := x.Expr.Op.(type) {
				case *ir.Jnz:
					n := int(y.NameID)
					if n == 0 {
						n = -y.Number
					}
					g.labels[n] = true
				case *ir.Jz:
					n := int(y.NameID)
					if n == 0 {
						n = -y.Number
					}
					g.labels[n] = true
				case *ir.Switch:
					for _, v := range y.Labels {
						n := int(v.NameID)
						if n == 0 {
							n = -v.Number
						}
						g.labels[n] = true
					}
					n := int(y.Default.NameID)
					if n == 0 {
						n = -y.Default.Number
					}
					g.labels[n] = true
				}
			case *ir.Jmp:
				if x.Cond {
					break
				}

				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				g.labels[n] = true
			}
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
		if ft.Variadic {
			g.w("args ...interface{}")
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
		g.w("var %v %v // %s\n", nm, g.typ2(v.def.TypeID), v.def.Pos())
		g.w("_ = %v\n", nm)
	}
	nodes := newGraph(g, f.Body)
	g.collectLabels(nodes)
	for _, v := range nodes {
		g.emit(v)
	}
	g.w("}\n\n")
}

func (g *gen) unionValue(pos token.Position, ft ir.Type, val []ir.Value) []byte {
	switch {
	case len(val) == 0:
		return nil
	case len(val) != 1:
		TODO("%s: %v, %v", pos, ft, val)
	}

	b := make([]byte, g.model.Sizeof(ft))
	switch ft.Kind() {
	case ir.Int32:
		*(*int32)(unsafe.Pointer(&b[0])) = val[0].(*ir.Int32Value).Value
	default:
		TODO("%s: %v, %T(%v)", pos, ft, val[0], val[0])
	}
	return b
}

func (g *gen) value(pos token.Position, id ir.TypeID, v ir.Value) {
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
			case t.Kind() == ir.Pointer && t.(*ir.PointerType).Element.Kind() == ir.Function:
				t = t.(*ir.PointerType).Element
				ft := g.tc.MustType(g.fns[nm].TypeID)
				switch {
				case t.ID() != ft.ID():
					g.w("*(*%v)(unsafe.Pointer(&struct{f %v}{%v}))", g.typ(t), g.typ(ft), nm)
				default:
					g.w("%v", nm)
				}
			default:
				g.w("&%v", nm)
			}
			break
		}

		g.w("(uintptr(unsafe.Pointer(&%v))+%v)", g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1), x.Offset)
	case *ir.CompositeValue:
		switch t := g.tc.MustType(id); t.Kind() {
		case ir.Array:
			et := t.(*ir.ArrayType).Item.ID()
			g.w("%v{", g.typ(t))
			if !isZeroValue(x) {
				for _, v := range x.Values {
					g.value(pos, et, v)
					g.w(", ")
				}
			}
			g.w("}")
		case ir.Struct:
			f := t.(*ir.StructOrUnionType).Fields
			g.w("%v{", g.typ(t))
			if !isZeroValue(x) {
				for i, v := range x.Values {
					if v == nil {
						continue
					}

					g.w("X%v: ", i)
					g.value(pos, f[i].ID(), v)
					g.w(", ")
				}
			}
			g.w("}")
		case ir.Union:
			ft := t.(*ir.StructOrUnionType).Fields[0]
			g.w("%v{", g.typ(t))
			if !isZeroValue(x) {
				g.w("U: [%v]byte{", g.model.Sizeof(t))
				for _, v := range g.unionValue(pos, ft, x.Values) {
					switch {
					case v < 10:
						g.w("%v,", v)
					default:
						g.w("%#02x, ", v)
					}
				}
				g.w("}")
			}
			g.w("}")
		case ir.Pointer:
			et := t.(*ir.PointerType).Element
			switch et.Kind() {
			case ir.Pointer:
				eet := et.(*ir.PointerType).Element
				switch eet.Kind() {
				case ir.Function:
					g.w("%v{", g.typ(et))
					for _, v := range x.Values {
						g.value(pos, et.ID(), v)
						g.w(", ")
					}
					g.w("}")
				default:
					TODO("%s: TODO1250 %v:%v, %v", pos, eet, eet.Kind(), x.Values)
				}
			default:
				TODO("%s: TODO1247 %v:%v", pos, et, et.Kind())
			}
		default:
			TODO("%s: TODO782 %v:%v", pos, t, t.Kind())
		}
	case *ir.Complex64Value:
		g.w("complex(float32(%v), float32(%v))", real(x.Value), imag(x.Value))
	case *ir.Float32Value:
		g.w("float32(%v)", x.Value)
	case *ir.Float64Value:
		g.w("%v", x.Value)
	case *ir.Int32Value:
		switch t.Kind() {
		case ir.Pointer:
			switch x.Value {
			case 0:
				switch {
				case t.ID() == idVoidPtr:
					g.w("0")
				default:
					g.w("nil")
				}
			default:
				g.w("(%v)(unsafe.Pointer(uintptr(%v)))", g.typ(t), uintptr(x.Value))
			}
		default:
			g.w("%v", x.Value)
		}
	case *ir.Int64Value:
		switch t.Kind() {
		case ir.Pointer:
			switch x.Value {
			case 0:
				g.w("nil")
			default:
				g.w("(%v)(unsafe.Pointer(uintptr(%v)))", g.typ(t), uintptr(x.Value))
			}
		case ir.Int32:
			g.w("int32(%v)", int32(x.Value))
		case ir.Uint32:
			g.w("uint32(%v)", uint32(x.Value))
		case ir.Int64:
			g.w("int64(%v)", x.Value)
		case ir.Uint64:
			g.w("uint64(%v)", uint64(x.Value))
		default:
			TODO("%s: %v", pos, t.Kind())
		}
	case *ir.StringValue:
		if x.Offset != 0 {
			TODO("%s", pos)
		}

		g.w("str(%v)", g.string(x.StringID))
	default:
		TODO("%s: %T", pos, x)
	}
}

func (g *gen) dataDefinition(d *ir.DataDefinition) {
	nm := g.mangle(d.NameID, d.Linkage == ir.ExternalLinkage, -1)
	g.w("var %s ", nm)
	t := g.tc.MustType(d.TypeID)
	switch t.Kind() {
	case ir.Pointer:
		switch x := d.Value.(type) {
		case *ir.CompositeValue:
			et := t.(*ir.PointerType).Element
			id := ir.TypeID(dict.SID(fmt.Sprintf("[%v]%v", len(x.Values), et)))
			t = g.tc.MustType(id)
			g.w("%v", g.typ(t))
		default:
			g.w("%s", g.typ(t))
		}
	default:
		g.w("%s", g.typ(t))
	}
	g.w(" // %s\n\n", g.pos(d.Position))
	if isZeroValue(d.Value) {
		return
	}

	g.w("func init() {\n")
	switch {
	case t.Kind() == ir.Array && t.(*ir.ArrayType).Item.Kind() == ir.Int8:
		g.w("crt.Xstrncpy(&%v[0],", nm) //TODO no way to get the qualifier - hardcoded.
		switch x := d.Value.(type) {
		case *ir.CompositeValue:
			var b buffer.Bytes
			for _, v := range x.Values {
				b.WriteByte(byte(v.(*ir.Int32Value).Value))
			}
			g.w("str(%v)", g.string(ir.StringID(dict.ID(b.Bytes()))))
			b.Close()
		default:
			g.value(d.Position, d.TypeID, d.Value)
		}
		g.w(", %v)", t.(*ir.ArrayType).Items)
	default:
		g.w("%s = ", nm)
		g.value(d.Position, t.ID(), d.Value)
	}
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
	g.w("package foo\n")
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
	for _, v := range g.helpers(g.storebits) {
		g.w("func storebits_%d(p *%[2]v, v, m %[2]v, o uint) %[2]v { *p = *p&m|(v<<o); return v }\n", v.TypeID, g.typ2(v.TypeID))
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
	return newOpt(g).opt()
}

// New writes Go code generated from obj to out.  No package or import clause
// is generated.  The qualifier function is called for implementation defined
// functions.  It must return the package qualifier, if any, that should be
// used to call the implementation defined function.
func New(obj []ir.Object, out io.Writer, qualifier func(*ir.FunctionDefinition) string) (err error) {
	var g *gen

	defer func() {
		switch x := recover().(type) {
		case nil:
			b := g.out.Bytes()
			i := bytes.IndexByte(b, '\n')
			_, err = out.Write(b[i+1:]) // Remove package clause.
			if e := g.out.Close(); e != nil && err == nil {
				err = e
			}
			return
		case error:
			err = x
		default:
			err = fmt.Errorf("irgo.New: PANIC: %v", x)
		}
		if err != nil && Testing {
			panic(err)
		}
	}()

	g = newGen(obj, qualifier)
	return g.gen()
}
