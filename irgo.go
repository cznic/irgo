// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

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
	"regexp"
	"runtime"
	"sort"
	"strings"
	"unsafe"

	"github.com/cznic/internal/buffer"
	"github.com/cznic/ir"
	"github.com/cznic/mathutil"
	"github.com/cznic/xc"
)

const (
	crt          = "crt"
	mallocAllign = 2 * ptrSize
	ptrSize      = mathutil.UintPtrBits / 8
)

var (
	// Testing amends things for tests.
	Testing bool
	// Testing hook.
	FTrace bool

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
	i     int
	r     int
	scope int
	w     int
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
	builtins  map[int]struct{} // Object#
	copies    map[ir.TypeID]struct{}
	elems     map[ir.TypeID]struct{}
	f         *fn
	fns       map[ir.NameID]*ir.FunctionDefinition
	labels    map[int]int
	lblUsed   map[int]int
	mangled   map[cname]ir.NameID
	model     ir.MemoryModel
	obj       []ir.Object
	out       *buffer.Bytes
	postIncs  map[ir.TypeID]struct{}
	preIncs   map[ir.TypeID]struct{}
	stable    map[ir.TypeID]int
	storebits map[ir.TypeID]struct{}
	stores    map[ir.TypeID]struct{}
	strTab    map[ir.StringID]int
	strings   buffer.Bytes
	tc        ir.TypeCache
	tm        map[ir.TypeID]string
	types     map[ir.TypeID]struct{}
}

func newGen(obj []ir.Object, tm map[ir.TypeID]string) *gen {
	model, err := ir.NewMemoryModel()
	if err != nil {
		panic(err)
	}

	g := &gen{
		builtins:  map[int]struct{}{},
		copies:    map[ir.TypeID]struct{}{},
		elems:     map[ir.TypeID]struct{}{},
		fns:       map[ir.NameID]*ir.FunctionDefinition{},
		mangled:   map[cname]ir.NameID{},
		model:     model,
		obj:       obj,
		out:       &buffer.Bytes{},
		postIncs:  map[ir.TypeID]struct{}{},
		preIncs:   map[ir.TypeID]struct{}{},
		stable:    map[ir.TypeID]int{},
		storebits: map[ir.TypeID]struct{}{},
		stores:    map[ir.TypeID]struct{}{},
		strTab:    map[ir.StringID]int{},
		tc:        ir.TypeCache{},
		tm:        tm,
		types:     map[ir.TypeID]struct{}{},
	}
	for _, v := range obj {
		switch x := v.(type) {
		case *ir.FunctionDefinition:
			nm := g.mangle2(x.Package, x.NameID, x.Linkage == ir.ExternalLinkage, -1)
			g.fns[nm] = x
		}
	}
	return g
}

func (g *gen) reg(t ir.TypeID) int {
	if n, ok := g.stable[t]; ok {
		return n
	}

	n := len(g.stable)
	g.stable[t] = n
	return n
}

func (g *gen) mangle(nm ir.NameID, exported bool, index int) ir.NameID {
	return g.mangle2(0, nm, exported, index)
}

func (g *gen) mangle2(pkg, nm ir.NameID, exported bool, index int) ir.NameID {
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

		if pkg != 0 {
			buf.Write(dict.S(int(pkg)))
			buf.WriteByte('.')
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

func (g *gen) typ0(buf *buffer.Bytes, t ir.Type, full bool) {
	if !full {
		if v, ok := g.tm[t.ID()]; ok {
			buf.WriteString(v)
			buf.WriteByte(' ')
			return
		}
	}

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
		n := at.Items
		fmt.Fprintf(buf, "[%v]", n)
		g.typ0(buf, at.Item, false)
	case ir.Struct:
		if full {
			buf.WriteString("struct{")
			for i, v := range t.(*ir.StructOrUnionType).Fields {
				fmt.Fprintf(buf, "X%v ", i)
				g.typ0(buf, v, false)
				buf.WriteByte(';')
			}
			buf.WriteString("}")
			return
		}

		g.types[t.ID()] = struct{}{}
		fmt.Fprintf(buf, "t%d ", g.reg(t.ID()))
	case ir.Union:
		if full {
			buf.WriteString("struct{X [0]struct{")
			for i, v := range t.(*ir.StructOrUnionType).Fields {
				fmt.Fprintf(buf, "X%v ", i)
				g.typ0(buf, v, false)
				buf.WriteByte(';')
			}
			fmt.Fprintf(buf, "}; U [%v]byte", g.model.Sizeof(t))
			buf.WriteString("}")
			return
		}

		g.types[t.ID()] = struct{}{}
		fmt.Fprintf(buf, "t%d ", g.reg(t.ID()))
	case ir.Pointer:
		if t.ID() == idVaList {
			buf.WriteString("[]interface{} ")
			return
		}

		if t.ID() == idVoidPtr {
			buf.WriteString("unsafe.Pointer ")
			return
		}

		e := t.(*ir.PointerType).Element
		if e.Kind() != ir.Function {
			buf.WriteByte('*')
		}
		g.typ0(buf, e, false)
	case ir.Function:
		ft := t.(*ir.FunctionType)
		fmt.Fprintf(buf, "func(*%s.TLS", crt)
		for _, v := range ft.Arguments {
			buf.WriteString(", ")
			g.typ0(buf, v, false)
		}
		if ft.Variadic {
			buf.WriteString(", ...interface{}")
		}
		buf.WriteByte(')')
		switch len(ft.Results) {
		case 0:
			// nop
		case 1:
			g.typ0(buf, ft.Results[0], false)
		default:
			TODO("")
		}
	default:
		TODO("%v", t.Kind())
	}
}

func (g *gen) fullType(t ir.TypeID) ir.NameID {
	var buf buffer.Bytes

	defer buf.Close()

	g.typ0(&buf, g.tc.MustType(t), true)
	return ir.NameID(dict.ID(buf.Bytes()))
}

func (g *gen) typ(t ir.Type) ir.NameID {
	var buf buffer.Bytes

	defer buf.Close()

	g.typ0(&buf, t, false)
	return ir.NameID(dict.ID(buf.Bytes()))
}

func (g *gen) typ2(t ir.TypeID) ir.NameID { return g.typ(g.tc.MustType(t)) }

func (g *gen) isBuiltin(i int) bool {
	if _, ok := g.builtins[i]; ok {
		return true
	}

	f := g.obj[i]
	if x, ok := f.(*ir.FunctionDefinition); ok && len(x.Body) == 1 {
		if _, ok := x.Body[0].(*ir.Panic); ok {
			g.builtins[i] = struct{}{}
			return true
		}
	}

	return false
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

	x := g.strings.Len()
	for g.strings.Len() < x {
		g.strings.WriteByte(0)
	}
	g.strTab[n] = x
	g.strings.Write(dict.S(int(n)))
	g.strings.WriteByte(0)
	return x
}

func (g *gen) wstring(n ir.StringID) int {
	if x, ok := g.strTab[n]; ok {
		return x
	}

	ws := []rune(string(dict.S(int(n))))
	sz := roundup(4*(len(ws)+1), mallocAllign)
	b := make([]byte, sz)
	for i, v := range ws {
		*(*rune)(unsafe.Pointer(&b[4*i])) = v //TODO Windows UTF-16
	}
	return g.string(ir.StringID(dict.ID(b)))
}

func (g *gen) collectLabels(nodes []*node) {
	g.lblUsed = map[int]int{}
	for _, v := range nodes {
		for _, op := range v.Ops {
			switch x := op.(type) {
			case *expr:
				switch y := x.Expr.Op.(type) {
				case *ir.Jnz:
					g.lblUsed[g.labels[label2(y.NameID, y.Number)]]++
				case *ir.Jz:
					g.lblUsed[g.labels[label2(y.NameID, y.Number)]]++
				case *ir.Switch:
					for _, v := range y.Labels {
						g.lblUsed[g.labels[label2(v.NameID, v.Number)]]++
					}
					g.lblUsed[g.labels[label2(y.Default.NameID, y.Default.Number)]]++
				}
			case *ir.Jmp:
				if x.Cond {
					break
				}

				g.lblUsed[g.labels[label2(x.NameID, x.Number)]]++
			}
		}
	}
}

func (g *gen) call(ft *ir.FunctionType, args []*exprNode) {
	g.w("(tls")
	for i, v := range args {
		if x, ok := v.Op.(*ir.Variable); ok {
			nfo := &g.f.varNfo[x.Index]
			sc := nfo.scope
			if sc == 0 {
				sc = -1
			}
			nfo.r++
		}
		g.w(", ")
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
				g.expression(v, false)
			default:
				g.convert(v, idVoidPtr)
			}
		case pt != nil:
			g.convert(v, pt.ID())
		default:
			g.expression(v, false)
		}
	}
	g.w(")")
}

func (g *gen) pcmp(n *exprNode, op string) {
	t := g.tc.MustType(n.Childs[0].TypeID)
	u := g.tc.MustType(n.Childs[1].TypeID)
	if t.Kind() == ir.Pointer && t.(*ir.PointerType).Element.Kind() == ir.Function {
		if isZeroExpr(n.Childs[0]) {
			g.expression(n.Childs[1], false)
			g.w("%s nil", op)
			return
		}

		if isZeroExpr(n.Childs[1]) {
			g.expression(n.Childs[0], false)
			g.w("%s nil", op)
			return
		}

		// *(*unsafe.Pointer)(unsafe.Pointer(&struct{f t}{e}))
		g.w("*(*uintptr)(unsafe.Pointer(&struct{f %v}{", g.typ(t))
		g.expression(n.Childs[0], false)
		g.w("}))")
		g.w("%s", op)
		g.w("*(*uintptr)(unsafe.Pointer(&struct{f %v}{", g.typ(u))
		g.expression(n.Childs[1], false)
		g.w("}))")
		return
	}

	switch op {
	case "==", "!=":
		switch {
		case t == u:
			g.expression(n.Childs[0], false)
			g.w("%s", op)
			g.expression(n.Childs[1], false)
		default:
			g.convert(n.Childs[0], idVoidPtr)
			g.w(" %v ", op)
			g.convert(n.Childs[1], idVoidPtr)
		}
		return
	}

	// >=, >, <=, <
	g.w("%s.P2U(", crt)
	g.convert(n.Childs[0], idVoidPtr)
	g.w(")%s %s.P2U(", op, crt)
	g.convert(n.Childs[1], idVoidPtr)
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
			if t.ID() == u.ID() && t.(*ir.PointerType).Element.Kind() != ir.Function {
				switch {
				case t.ID() == idVoidPtr:
					g.convert(n.Childs[0], idVoidPtr)
				default:
					g.expression(n.Childs[0], false)
				}
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
			if t.ID() == u.ID() && t.(*ir.PointerType).Element.Kind() != ir.Function {
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
		switch x, ok := n.Childs[0].Op.(*ir.Convert); {
		case ok && isIntegralType(x.TypeID):
			g.w("uintptr")
			g.expression(n.Childs[0].Childs[0], false)
		default:
			g.w("uintptr(")
			g.convert(n.Childs[0], idVoidPtr)
			g.w(")")
		}
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
		switch x, ok := n.Childs[1].Op.(*ir.Convert); {
		case ok && isIntegralType(x.TypeID):
			g.w("uintptr")
			g.expression(n.Childs[1].Childs[0], false)
		default:
			g.w("uintptr(")
			g.convert(n.Childs[1], idVoidPtr)
			g.w(")")
		}
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

func (g *gen) label(nm ir.NameID, n int) {
	switch m := g.labels[label2(nm, n)]; {
	case m > 0:
		g.w("_%v", ir.NameID(m))
	default:
		g.w("_%v", -m)
	}
}

func (g *gen) expression(n *exprNode, void bool) bool { return g.expression2(n, void, 0) }

func (g *gen) expression2(n *exprNode, void bool, nextLabel int) bool {
	switch n.Op.(type) {
	case
		*ir.Drop,
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
		for _, v := range a {
			v.Comma = nil
		}
		switch {
		case void:
			for i := len(a) - 1; i >= 0; i-- {
				g.expression(a[i], true)
				g.w(";")
			}
			switch n.Op.(type) {
			case *ir.Const32:
				return false
			}

			g.w("_ = ")
			void = false
			defer g.w("\n")
		default:
			g.w("func() %v {", g.typ2(n.TypeID))
			for i := len(a) - 1; i >= 0; i-- {
				g.expression(a[i], true)
				g.w(";")
			}
			g.w("return (")
			void = false
			defer g.w(")}()")
		}
	}
	switch x := n.Op.(type) {
	case *ir.Argument:
		if void {
			return false
		}

		if x.Address {
			g.w("&")
		}

		g.w("(%s)", g.mangle(g.f.f.Arguments[x.Index], false, -1))
	case *ir.Bool:
		g.w("bool2int(")
		e := n.Childs[0]
	more:
		t := g.tc.MustType(e.TypeID)
		switch {
		case t.Kind() == ir.Pointer:
			if x, ok := e.Op.(*ir.Convert); ok && g.tc.MustType(x.TypeID).Kind() == ir.Pointer && e.Comma == nil {
				e = e.Childs[0]
				goto more
			}

			g.expression(e, false)
			g.w("!= nil")
		default:
			g.expression(e, false)
			g.w("!= 0")
		}
		g.w(")")
	case *ir.Call:
		f := g.obj[x.Index].(*ir.FunctionDefinition)
		if g.isBuiltin(x.Index) {
			g.w("%s.", crt)
		}
		g.w("%s", g.mangle2(f.Package, f.NameID, f.Linkage == ir.ExternalLinkage, -1))
		ft := g.tc.MustType(f.TypeID).(*ir.FunctionType)
		g.call(ft, n.Childs)
	case *ir.CallFP:
		fp := n.Childs[0]
		g.expression(fp, false)
		ft := g.tc.MustType(fp.TypeID).(*ir.PointerType).Element.(*ir.FunctionType)
		g.call(ft, n.Childs[1:])
	case *ir.Const32:
		if void {
			break
		}

		switch t := g.tc.MustType(x.TypeID); t.Kind() {
		case ir.Pointer:
			switch {
			case x.Value == 0:
				TODO("%s: %v", x.Pos(), x.TypeID)
			default:
				g.w("(%v)(unsafe.Pointer(uintptr(%v)))", g.typ(t), uintptr(x.Value))
			}
		case ir.Int8:
			g.w("i8(%v) ", int8(x.Value))
		case ir.Uint8:
			g.w("u8(%v) ", byte(x.Value))
		case ir.Int16:
			g.w("i16(%v) ", int16(x.Value))
		case ir.Uint16:
			g.w("u16(%v) ", uint16(x.Value))
		case ir.Int32:
			g.w("i32(%v) ", x.Value)
		case ir.Uint32:
			g.w("u32(%v) ", uint32(x.Value))
		case ir.Int64:
			g.w("i64(%v) ", int64(x.Value))
		case ir.Uint64:
			g.w("u64(%v) ", uint64(x.Value))
		case ir.Float32:
			g.w("float32(%v) ", math.Float32frombits(uint32(x.Value)))
		default:
			TODO("%s: %v", x.Pos(), x.TypeID)
		}
	case *ir.Const64:
		if void {
			break
		}

		switch x.TypeID {
		case idComplex64:
			g.w("complex(float32(%v), 0) ", math.Float64frombits(uint64(x.Value)))
		case idFloat64:
			v := math.Float64frombits(uint64(x.Value))
			switch {
			case math.IsInf(v, 0):
				g.w("inf")
			case math.IsInf(v, -1):
				g.w("-inf")
			default:
				g.w("float64(%v) ", v)
			}
		case idInt8:
			g.w("i8(%v) ", int8(x.Value))
		case idUint8:
			g.w("u8(%v) ", byte(x.Value))
		case idInt16:
			g.w("i16(%v) ", int16(x.Value))
		case idUint16:
			g.w("u16(%v) ", uint16(x.Value))
		case idInt32:
			g.w("i32(%v) ", int32(x.Value))
		case idUint32:
			g.w("u32(%v) ", uint32(x.Value))
		case idInt64:
			g.w("i64(%v) ", x.Value)
		case idUint64:
			g.w("u64(%v) ", uint64(x.Value))
		default:
			TODO("%s: %v", x.Pos(), x.TypeID)
		}
	case *ir.Convert:
		e := n.Childs[0]
		if void && e.TypeID != idVaList {
			g.expression(e, true)
			return false
		}

		g.convert2(e, x.TypeID, x.Result)
	case *ir.Copy:
		if void {
			g.w("*")
			g.expression(n.Childs[0], false)
			g.w("= *")
			g.expression(n.Childs[1], false)
			return false
		}

		g.copies[x.TypeID] = struct{}{}
		g.w("copy%d(", g.reg(x.TypeID))
		g.expression(n.Childs[0], false)
		g.w(",")
		g.expression(n.Childs[1], false)
		g.w(")")
	case *ir.Cpl:
		g.w("^")
		g.expression(n.Childs[0], false)
	case *ir.Drop:
		g.expression(n.Childs[0], true)
	case *ir.Element:
		if x, ok := n.Childs[0].Op.(*ir.Variable); ok {
			nfo := &g.f.varNfo[x.Index]
			sc := nfo.scope
			if sc == 0 {
				sc = -1
			}
			nfo.r++
		}
		s := ""
		if x.Neg {
			s = "-"
		}
		g.elems[x.TypeID] = struct{}{}
		if !x.Address {
			g.w("*")
		}
		g.w("elem%v(", g.reg(x.TypeID))
		g.expression(n.Childs[0], false)
		g.w(", %suintptr", s)
		g.expression(n.Childs[1], false)
		g.w(")")
	case *ir.Field:
		e := n.Childs[0]
		if x, ok := e.Op.(*ir.Variable); ok {
			nfo := &g.f.varNfo[x.Index]
			sc := nfo.scope
			if sc == 0 {
				sc = -1
			}
			nfo.r++
		}
		t := g.tc.MustType(x.TypeID).(*ir.PointerType).Element.(*ir.StructOrUnionType)
		ft := t.Fields[x.Index]
		switch t.Kind() {
		case ir.Union:
			if !x.Address {
				g.w("*")
			}
			g.w("(*%v)(unsafe.Pointer", g.typ(ft))
			g.convert(e, x.TypeID)
			g.w(")")
		default:
			if x.Address {
				g.w("&")
			}

			g.w("(")
			g.expression(e, false)
			g.w(".X%v)", x.Index)
		}
	case *ir.Global:
		nm := g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1)
		s := ""
		if g.isBuiltin(x.Index) {
			s = fmt.Sprintf("%s.", crt)
		}
		if x.Address {
			switch t := g.tc.MustType(x.TypeID); t.Kind() {
			case ir.Pointer:
				if t.(*ir.PointerType).Element.Kind() == ir.Function {
					g.w("%s%s", s, nm)
					return false
				}

				g.w("&%s", nm)
				return false
			default:
				TODO("%s: %T\n%s", x.Pos(), x, x.TypeID)
			}
		}

		g.w("%s%s", s, nm)
	case *ir.Jnz:
		l := int(x.NameID)
		if l == 0 {
			l = -x.Number
		}
		if nextLabel == l {
			g.w("if")
			g.expression(n.Childs[0], false)
			g.w("== 0 {")
			g.lblUsed[g.labels[l]]--
			return true
		}

		g.w("if")
		g.expression(n.Childs[0], false)
		g.w("!= 0 { goto ")
		g.label(x.NameID, x.Number)
		g.w("}")
	case *ir.Jz:
		l := int(x.NameID)
		if l == 0 {
			l = -x.Number
		}
		if nextLabel == l {
			g.w("if")
			g.expression(n.Childs[0], false)
			g.w("!= 0 {")
			g.lblUsed[g.labels[l]]--
			return true
		}

		g.w("if")
		g.expression(n.Childs[0], false)
		g.w("== 0 { goto ")
		g.label(x.NameID, x.Number)
		g.w("}")
	case *ir.Label:
		if x.Cond {
			if void {
				switch n.Childs[1].Op.(type) {
				case *ir.Const32:
					if n.Childs[1].Comma != nil {
						break
					}

					//TODO The func() wrapper bypasses an internal compiler error (fixed in Go1.9.)
					g.w("func() { if ")
					g.expression(n.Childs[0], false)
					g.w("== 0 {")
					g.expression(n.Childs[2], true)
					g.w("}}()")
					return false
				}
			}

			g.w("func() %v { if ", g.typ2(n.TypeID))
			g.expression(n.Childs[0], false)
			g.w("!= 0 { return ")
			switch {
			case n.TypeID == idVoidPtr:
				g.convert(n.Childs[1], idVoidPtr)
			default:
				g.expression(n.Childs[1], false)
			}
			g.w("}; return")
			g.expression(n.Childs[2], false)
			g.w("}()")
			return false
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
			return false
		}

		g.expression(n.Childs[0], false)
	case *ir.Neg:
		g.w("-")
		g.expression(n.Childs[0], false)
	case *ir.Nil:
		g.w("nil")
	case *ir.Not:
		g.w("bool2int(")
		g.expression(n.Childs[0], false)
		g.w("== 0)")
	case *ir.PostIncrement:
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		if void {
			switch {
			case t.Kind() == ir.Pointer:
				g.w("*(*uintptr)(")
				g.convert(n.Childs[0], idVoidPtr)
				g.w(") += uintptr(%v)", uintptr(x.Delta))
			default:
				g.w("*")
				g.expression(n.Childs[0], false)
				switch {
				case x.Delta < 0:
					g.w("-= %v", -x.Delta)
				default:
					g.w("+= %v", x.Delta)
				}
			}
			return false
		}

		g.postIncs[x.TypeID] = struct{}{}
		g.w("postInc%d(", g.reg(x.TypeID))
		g.expression(n.Childs[0], false)
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w(", %v)", x.Delta)
		default:
			switch x.TypeID {
			case idInt8:
				g.w(", %v)", int8(x.Delta))
			case idUint8:
				g.w(", byte(%v))", uint8(x.Delta))
			case idInt16:
				g.w(", %v)", int16(x.Delta))
			case idUint16:
				g.w(", uint16(%v))", uint16(x.Delta))
			case idInt32:
				g.w(", %v)", int32(x.Delta))
			case idUint32:
				g.w(", uint32(%v))", uint32(x.Delta))
			case idInt64:
				g.w(", %v)", int64(x.Delta))
			case idUint64:
				g.w(", uint64(%v))", uint64(x.Delta))
			case idFloat32:
				g.w(", %v)", float32(x.Delta))
			case idFloat64:
				g.w(", %v)", float64(x.Delta))
			default:
				TODO("%s: %v", x.Pos(), x.TypeID)
			}
		}
	case *ir.PreIncrement:
		if void {
			switch {
			case t.Kind() == ir.Pointer:
				g.w("*(*uintptr)(")
				g.convert(n.Childs[0], idVoidPtr)
				g.w(") += uintptr(%v)", uintptr(x.Delta))
			default:
				g.w("*")
				g.expression(n.Childs[0], false)
				switch {
				case x.Delta < 0:
					g.w("-= %v", -x.Delta)
				default:
					g.w("+= %v", x.Delta)
				}
			}
			return false
		}

		g.preIncs[x.TypeID] = struct{}{}
		if x.Bits != 0 {
			TODO("%s", x.Pos())
		}

		g.w("preInc%d(", g.reg(x.TypeID))
		g.expression(n.Childs[0], false)
		switch {
		case g.tc.MustType(x.TypeID).Kind() == ir.Pointer:
			g.w(", %v)", x.Delta)
		default:
			switch x.TypeID {
			case idInt8:
				g.w(", %v)", int8(x.Delta))
			case idUint8:
				g.w(", byte(%v))", uint8(x.Delta))
			case idInt16:
				g.w(", %v)", int16(x.Delta))
			case idUint16:
				g.w(", uint16(%v))", uint16(x.Delta))
			case idInt32:
				g.w(", %v)", int32(x.Delta))
			case idUint32:
				g.w(", uint32(%v))", uint32(x.Delta))
			case idInt64:
				g.w(", %v)", int64(x.Delta))
			case idUint64:
				g.w(", uint64(%v))", uint64(x.Delta))
			case idFloat32:
				g.w(", %v)", float32(x.Delta))
			case idFloat64:
				g.w(", %v)", float64(x.Delta))
			default:
				TODO("%s: %v", x.Pos(), x.TypeID)
			}
		}
	case *ir.PtrDiff:
		sz := g.model.Sizeof(g.tc.MustType(x.PtrType).(*ir.PointerType).Element)
		g.w("%v((", x.TypeID)
		if sz != 1 {
			g.w("(")
		}
		g.w("uintptr(")
		g.convert(n.Childs[0], idVoidPtr)
		g.w(")-uintptr(")
		g.convert(n.Childs[1], idVoidPtr)
		g.w("))")
		if sz != 1 {
			g.w("/%v)", sz)
		}
		g.w(")")
	case *ir.Result:
		if x.Address {
			g.w("&")
		}

		g.w("(r%v)", x.Index)
	case *ir.Store:
		_, asop := n.Childs[0].Op.(*ir.Dup)
		switch {
		case x.Bits == 0 && !void && !asop:
			g.stores[x.TypeID] = struct{}{}
			g.w("store%d(", g.reg(x.TypeID))
			g.expression(n.Childs[0], false)
			g.w(", ")
			g.expression(n.Childs[1], false)
			g.w(")")
		case x.Bits == 0 && !void && asop:
			g.stores[x.TypeID] = struct{}{}
			g.w("store%d(", g.reg(x.TypeID))
			g.w("func()(*%[1]v, %[1]v){ p := ", g.typ2(x.TypeID))
			g.expression(n.Childs[0].Childs[0], false)
			g.w("; return p,")
			g.expression(n.Childs[1], false)
			g.w("}()")
			g.w(")")
			return false
		case x.Bits == 0 && void && !asop:
			g.w("*")
			g.expression(n.Childs[0], false)
			g.w("=")
			switch {
			case n.Childs[0].TypeID == idPVoidPtr && n.Childs[1].TypeID == idVoidPtr:
				switch x := n.Childs[1].Op.(type) {
				case *ir.Convert:
					if x.Result == idVoidPtr {
						g.convert(n.Childs[1], g.tc.MustType(n.Childs[0].TypeID).(*ir.PointerType).Element.ID())
						break
					}

					g.convert(n.Childs[1], idVoidPtr)
				default:
					g.w("unsafe.Pointer") //TODO unsafe.Pointer kept here b/c of sqlite/mptest failing.
					g.expression(n.Childs[1], false)
				}
			default:
				g.convert(n.Childs[1], g.tc.MustType(n.Childs[0].TypeID).(*ir.PointerType).Element.ID())
			}
			switch n.Childs[0].Op.(type) {
			case *ir.Global:
				g.w("\nbug20530(*")
				g.expression(n.Childs[0], false)
				g.w(")")
			}
		case x.Bits == 0 && void && asop:
			e := n.Childs[1]
			switch x := e.Op.(type) {
			case *ir.Convert:
				g.w("{ p := ")
				g.expression(n.Childs[0].Childs[0], false)
				g.w("; *p =")
				g.expression(n.Childs[1], false)
				g.w(" }")
			case *ir.Element:
				if !x.Address {
					TODO("%s", x.Position)
				}

				t := g.tc.MustType(x.TypeID)
				sz := g.model.Sizeof(t.(*ir.PointerType).Element)
				s := "+"
				if x.Neg {
					s = "-"
				}
				g.w("*(*uintptr)(")
				g.convert(n.Childs[0].Childs[0], idVoidPtr)
				s2 := ""
				if sz != 1 {
					s2 = fmt.Sprintf("%v*", sz)
				}
				g.w(") %s= %suintptr(", s, s2)
				g.expression(e.Childs[1], false)
				g.w(")")
			case *ir.Lsh:
				g.w("*")
				g.expression(n.Childs[0].Childs[0], false)
				g.w("<<=uint(")
				g.expression(e.Childs[1], false)
				g.w(")")
			case *ir.Rsh:
				g.w("*")
				g.expression(n.Childs[0].Childs[0], false)
				g.w(">>=uint(")
				g.expression(e.Childs[1], false)
				g.w(")")
			default:
				g.w("*")
				g.expression(n.Childs[0].Childs[0], false)
				switch e.Op.(type) {
				case *ir.Add:
					g.w("+=")
				case *ir.And:
					g.w("&=")
				case *ir.Div:
					g.w("/=")
				case *ir.Mul:
					g.w("*=")
				case *ir.Or:
					g.w("|=")
				case *ir.Rem:
					g.w("%%=")
				case *ir.Sub:
					g.w("-=")
				case *ir.Xor:
					g.w("^=")
				}
				g.expression(e.Childs[1], false)
			}
		case x.Bits != 0 && !void && !asop:
			m := (uint64(1)<<uint(x.Bits) - 1) << uint(x.BitOffset)
			g.storebits[x.TypeID] = struct{}{}
			g.w("storebits%d(", g.reg(x.TypeID))
			g.expression(n.Childs[0], false)
			g.w(", ")
			g.expression(n.Childs[1], false)
			g.w(", %v, %v)", m, x.BitOffset)
		case x.Bits != 0 && void && !asop:
			m := (uint64(1)<<uint(x.Bits) - 1) << uint(x.BitOffset)
			g.storebits[x.TypeID] = struct{}{}
			g.w("storebits%d(", g.reg(x.TypeID))
			g.expression(n.Childs[0], false)
			g.w(", ")
			g.expression(n.Childs[1], false)
			g.w(", %v, %v)", m, x.BitOffset)
		case x.Bits != 0 && void && asop:
			m := (uint64(1)<<uint(x.Bits) - 1) << uint(x.BitOffset)
			g.w("{ p := ")
			g.expression(n.Childs[0].Childs[0], false)
			g.w("; v :=")
			g.expression(n.Childs[1], false)
			s := ""
			switch n.Childs[1].TypeID {
			case idInt8:
				s = fmt.Sprint(int8(m))
			case idInt16:
				s = fmt.Sprint(int16(m))
			case idInt32:
				s = fmt.Sprint(int32(m))
			case idInt64:
				s = fmt.Sprint(int64(m))
			default:
				_ = m
				TODO("%s: %v", x.Pos(), n.Childs[1].TypeID)
			}
			g.w("; *p = *p&^%s|(v<<%v)&%s", s, x.BitOffset, s)
			g.w("}")
		default:
			TODO("%s: %v %v %v", x.Pos(), x.Bits, void, asop)
		}
	case *ir.StringConst:
		switch x.TypeID {
		case idInt8Ptr:
			g.w("str(%v)", g.string(x.Value))
		case idInt32Ptr:
			g.w("wstr(%v)", g.wstring(x.Value))
		default:
			panic(fmt.Errorf("%s: TODO %v", x.Position, x.TypeID))
		}
	case *ir.Variable:
		if void {
			return false
		}

		nfo := &g.f.varNfo[x.Index]
		sc := nfo.scope
		if sc == 0 {
			sc = -1
		}
		switch {
		case x.Address:
			g.w("&")
			nfo.w++
		default:
			nfo.r++
		}
		switch {
		case nfo.def.NameID == 0:
			g.w("_%v", x.Index)
		default:
			g.w("%v", g.mangle(nfo.def.NameID, false, sc))
		}
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
			g.value(x.Pos(), x.TypeID, v.Value)
			g.w(": goto ")
			g.label(v.Label.NameID, v.Label.Number)
			g.w("\n")
		}
		g.w("default: goto ")
		g.label(x.Default.NameID, x.Default.Number)
		g.w("\n}\n")
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
	case
		*ir.Lsh,
		*ir.Rsh:

		if void {
			g.expression(n.Childs[0], true)
			return false
		}

		g.shift(n)
	case
		*ir.Eq,
		*ir.Geq,
		*ir.Gt,
		*ir.Leq,
		*ir.Lt,
		*ir.Neq:

		g.relop(n)
	default:
		TODO("%s: %T", x.Pos(), x)
	}
	return false
}

func (g *gen) convert(e *exprNode, to ir.TypeID) { g.convert2(e, e.TypeID, to) }

func (g *gen) convert2(e *exprNode, from, to ir.TypeID) {
	if x, ok := e.Op.(*ir.Global); ok && x.NameID == idMain {
		g.expression(e, false)
		return
	}

	if from == to {
		g.expression(e, false)
		return
	}

	if to == idVaList {
		switch x := e.Op.(type) {
		case *ir.Const32:
			switch x.Value {
			case 0: // va_end
				g.w("nil")
				return
			case 1: // va_start
				g.w("args")
				return
			default:
				TODO("%s: %v", e.Op.Pos(), x.Value)
			}
		default:
			TODO("%s: %T %v", e.Op.Pos(), x, e.TypeID)
		}
	}

	if from == idVaList {
		switch t := g.tc.MustType(to); {
		case t.Kind() == ir.Pointer:
			if u := t.(*ir.PointerType); u.Element.Kind() == ir.Function {
				g.w("%s.VAOther(&", crt)
				g.expression(e, false)
				g.w(").(%v)", g.typ(u.Element))
				break
			}

			if to != idVoidPtr {
				g.w("(%v)(%s.VAPointer(&", g.typ(t), crt)
				g.expression(e, false)
				g.w("))")
				break
			}

			fallthrough
		case isIntegralType(to):
			s := g.tc.MustType(to).Kind().String()
			s = strings.ToUpper(s[:1]) + s[1:]
			g.w("%s.VA%s(&", crt, s)
			g.expression(e, false)
			g.w(")")
		default:
			g.w("%s.VAOther(&", crt)
			g.expression(e, false)
			g.w(").(%v)", g.typ(t))
		}
		return
	}

	t := g.tc.MustType(to)
	if t.Kind() == ir.Pointer && isZeroExpr(e) {
		//TODO crt.Xutimes(tls, _zLockFile, (*[2]crt.Xstruct_timeval)(nil)) -> crt.Xutimes(tls, _zLockFile, nil)
		g.w("nil")
		return
	}

	et := g.tc.MustType(from)
	if et.Kind() == ir.Pointer && to == idVoidPtr {
		if _, ok := e.Op.(*ir.Convert); ok {
			g.convert(e.Childs[0], to)
			return
		}
	}

	if t.Kind() == ir.Pointer {
		et := t.(*ir.PointerType).Element
		if et.Kind() == ir.Function {
			switch y := e.Op.(type) {
			case *ir.Const32:
				// *(*t)(unsafe.Pointer(&struct{f uintptr}{e}))
				g.w("*(*%v)(unsafe.Pointer(&struct{f uintptr}{%v}))", g.typ(t), uintptr(y.Value))
			case *ir.Convert:
				g.convert2(e.Childs[0], from, to)
			default:
				// func() t { v := e; return *(*t)(unsafe.Pointer(&v)) }()
				g.w("func() %v { v := ", g.typ(t))
				g.expression(e, false)
				g.w("; return *(*%v)(unsafe.Pointer(&v)) }()", g.typ(t))
			}
			return
		}
	}

	if et.Kind() == ir.Pointer && isIntegralType(to) {
		g.w("(%v)(%s.P2U(", g.typ(t), crt)
		g.convert(e, idVoidPtr)
		g.w("))")
		return
	}

	if t.Kind() == ir.Complex64 {
		g.w("complex(")
		g.convert(e, idFloat32)
		g.w(", 0)")
		return
	}

	if t.Kind() == ir.Complex128 {
		g.w("complex(")
		g.convert(e, idFloat64)
		g.w(", 0)")
		return
	}

	g.w("(%v)(", g.typ2(to))
	switch {
	case t.Kind() == ir.Pointer:
		switch {
		case isIntegralType(from):
			g.w("%s.U2P(uintptr", crt)
			g.expression(e, false)
			g.w(")")
		default:
			if e.TypeID != idVoidPtr {
				g.w("unsafe.Pointer")
			}
			g.expression(e, false)
		}
	default:
		g.expression(e, false)
	}
	g.w(")")
}

func (g *gen) emit(n *node, lastVoid bool, nextLabel int) {
	var r bool
	for i, op := range n.Ops {
		switch x := op.(type) {
		case *expr:
			if g.expression2(x.Expr, true, nextLabel) {
				r = true
			}
			g.w("\n")
		case *ir.Jmp:
			g.w("goto ")
			g.label(x.NameID, x.Number)
			g.w("\n")
		case *ir.Label:
			if g.lblUsed[label(x)] == 0 {
				break
			}

			g.label(x.NameID, x.Number)
			g.w(":\n")
		case *ir.Return:
			if i != len(n.Ops)-1 || !lastVoid {
				g.w("return\n")
			}
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
			t := g.tc.MustType(x.TypeID)
			var it ir.Type
			if t.Kind() == ir.Array {
				it = t.(*ir.ArrayType).Item
			}
			switch {
			case it != nil && it.Kind() == ir.Int8:
				n := t.(*ir.ArrayType).Items
				switch y := x.Value.(type) {
				case *ir.CompositeValue:
					g.w("%s = [%v]int8{", nm, n)
					for _, v := range y.Values {
						g.w("%v, ", int8(v.(*ir.Int32Value).Value))
					}
					g.w("}")
				case *ir.StringValue:
					g.w("%s.Xstrncpy(nil, &%v[0],", crt, nm)
					g.value(x.Position, x.TypeID, x.Value)
					g.w(", %v)", n)
				default:
					TODO("%s: %T", x.Pos(), y)
				}
			default:
				g.w("%s = ", nm)
				g.value(x.Pos(), x.TypeID, x.Value)
			}
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
	if r {
		g.w("}\n")
	}
}

func (g *gen) functionDefinition(oi int, f *ir.FunctionDefinition) {
	if g.isBuiltin(oi) || f.Package != 0 {
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

	g.w("%s", f.Comment)
	nm := g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage, -1)
	g.w("func %v(tls *%v.TLS", nm, crt)
	switch {
	case f.NameID == idMain && len(ft.Arguments) != 2:
		g.w(", _ int32, _ **int8) (r0 int32)")
	default:
		for i, v := range ft.Arguments {
			if i < len(f.Arguments) {
				g.w(", %v ", g.mangle(f.Arguments[i], false, -1))
			}
			g.w("%s", g.typ(v))
		}
		if ft.Variadic {
			g.w(", args ...interface{}")
		}
		g.w(")")
		if len(ft.Results) != 0 {
			//TODO support multiple results.
			g.w("(r0 %s)", g.typ(ft.Results[0]))
		}
	}
	g.w("{\n")
	if FTrace {
		g.w("ftrace(%q)\n", nm)
	}
	m := map[ir.TypeID][]varNfo{}
	for i, v := range g.f.varNfo {
		v.i = i
		t := v.def.TypeID
		m[t] = append(m[t], v)
	}
	var a []int
	for k := range m {
		a = append(a, int(k))
	}
	sort.Ints(a)
	for _, t := range a {
		g.w("var ")
		t := ir.TypeID(t)
		a := m[t]
		for i, v := range a {
			sc := v.scope
			if sc == 0 {
				sc = -1
			}
			if i != 0 {
				g.w(",")
			}
			switch {
			case v.def.NameID == 0:
				g.w("_%v", v.i)
			default:
				nm := g.mangle(v.def.NameID, false, sc)
				g.w("%v", nm)
			}
		}
		g.w(" %v\n", g.typ2(t))
	}
	nodes := newGraph(g, f.Body)
	g.collectLabels(nodes)
	for i, v := range nodes {
		nextLabel := mathutil.MinInt
		if i < len(nodes)-1 {
			if x, ok := nodes[i+1].Ops[0].(*ir.Label); ok {
				nextLabel = int(x.NameID)
				if nextLabel == 0 {
					nextLabel = -x.Number
				}
			}
		}
		g.emit(v, i == len(nodes)-1 && len(ft.Results) == 0, nextLabel)
	}
	ok := true
	for _, v := range g.f.varNfo {
		if v.r == 0 && v.def.NameID != 0 {
			sc := v.scope
			if sc == 0 {
				sc = -1
			}
			nm := g.mangle(v.def.NameID, false, sc)
			g.w("_ = %v\n", nm)
			ok = false
		}
	}
	if !ok && len(ft.Results) != 0 {
		g.w("panic(0)\n")
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
				g.w("unsafe.Pointer(&%v)", nm)
			case t.Kind() == ir.Pointer && t.(*ir.PointerType).Element.Kind() == ir.Function:
				s := ""
				if g.isBuiltin(x.Index) {
					s = fmt.Sprintf("%s.", crt)
				}
				t = t.(*ir.PointerType).Element
				ft := g.tc.MustType(g.fns[nm].TypeID)
				switch {
				case t.ID() != ft.ID():
					g.w("*(*%v)(unsafe.Pointer(&struct{f %v}{%s%v}))", g.typ(t), g.typ(ft), s, nm)
				default:
					g.w("%s%v", s, nm)
				}
			default:
				g.w("&%v", nm)
			}
			break
		}

		g.w("(%v)(uintptr(unsafe.Pointer(&%v))+%v)", g.typ2(id), g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage, -1), x.Offset)
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
					if isZeroValue(v) {
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
	case *ir.Float32Value:
		if id != idFloat32 {
			g.w("(%v)(", g.typ2(id))
		}
		switch {
		case x.Value == 0 && math.Signbit(float64(x.Value)):
			g.w("nzf32")
		default:
			g.w("%v", x.Value)
		}
		if id != idFloat32 {
			g.w(")")
		}
	case *ir.Float64Value:
		if id != idFloat64 {
			g.w("(%v)(", g.typ2(id))
		}
		switch {
		case x.Value == 0 && math.Signbit(x.Value):
			g.w("nzf64")
		default:
			g.w("%v", x.Value)
		}
		if id != idFloat64 {
			g.w(")")
		}
	case *ir.Int32Value:
		switch t.Kind() {
		case ir.Pointer:
			switch x.Value {
			case 0:
				g.w("nil")
			default:
				g.w("(%v)(%s.U2P(%v))", g.typ(t), crt, uintptr(x.Value))
			}
		case ir.Int8:
			g.w("i8(%v)", int8(x.Value))
		case ir.Uint8:
			g.w("u8(%v)", byte(x.Value))
		case ir.Int16:
			g.w("i16(%v)", int16(x.Value))
		case ir.Uint16:
			g.w("u16(%v)", uint16(x.Value))
		case ir.Int32:
			g.w("i32(%v)", x.Value)
		case ir.Uint32:
			g.w("u32(%v)", uint32(x.Value))
		case ir.Int64:
			g.w("i64(%v)", x.Value)
		case ir.Uint64:
			g.w("u64(%v)", uint64(x.Value))
		case ir.Float32:
			g.w("float32(%v)", x.Value)
		case ir.Float64:
			g.w("float64(%v)", x.Value)
		default:
			TODO("%s: %v", pos, t.Kind())
		}
	case *ir.Int64Value:
		switch t.Kind() {
		case ir.Pointer:
			switch x.Value {
			case 0:
				g.w("nil")
			default:
				g.w("(%v)(%s.U2P(%v))", g.typ(t), crt, uintptr(x.Value))
			}
		case ir.Int8:
			g.w("i8(%v)", int8(x.Value))
		case ir.Uint8:
			g.w("u8(%v)", byte(x.Value))
		case ir.Int16:
			g.w("i16(%v)", int16(x.Value))
		case ir.Uint16:
			g.w("u16(%v)", uint16(x.Value))
		case ir.Int32:
			g.w("i32(%v)", int32(x.Value))
		case ir.Uint32:
			g.w("u32(%v)", uint32(x.Value))
		case ir.Int64:
			g.w("i64(%v)", x.Value)
		case ir.Uint64:
			g.w("u64(%v)", uint64(x.Value))
		case ir.Float32:
			g.w("float32(%v)", x.Value)
		case ir.Float64:
			g.w("float64(%v)", x.Value)
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
	if d.Package != 0 {
		return
	}

	nm := g.mangle(d.NameID, d.Linkage == ir.ExternalLinkage, -1)
	g.w("var %s ", nm)
	t := g.tc.MustType(d.TypeID)
	// fmt.Printf("%s: %v %v // DD \n", d.Position, d.NameID, t)
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
	g.w("\n\n")
	if isZeroValue(d.Value) {
		return
	}

	g.w("func init() {\n")
	var it ir.Type
	if t.Kind() == ir.Array {
		it = t.(*ir.ArrayType).Item
	}
outer:
	switch {
	case it != nil && it.Kind() == ir.Int8:
		n := t.(*ir.ArrayType).Items
		switch y := d.Value.(type) {
		case *ir.CompositeValue:
			g.w("%s = [%v]int8{", nm, n)
			for _, v := range y.Values {
				g.w("%v, ", int8(v.(*ir.Int32Value).Value))
			}
			g.w("}")
		case *ir.StringValue:
			g.w("%s.Xstrncpy(nil, &%v[0],", crt, nm)
			g.value(d.Position, d.TypeID, d.Value)
			g.w(", %v)", n)
		default:
			TODO("%s: %T", d.Position, y)
		}
	case it != nil && it.Kind() == ir.Uint8:
		n := t.(*ir.ArrayType).Items
		switch y := d.Value.(type) {
		case *ir.CompositeValue:
			g.w("%s = [%v]uint8{", nm, n)
			for _, v := range y.Values {
				g.w("%v, ", uint8(v.(*ir.Int32Value).Value))
			}
			g.w("}")
		case *ir.StringValue:
			g.w("%s.Xstrncpy(nil, (*int8)(unsafe.Pointer(&%v[0])),", crt, nm)
			g.value(d.Position, d.TypeID, d.Value)
			g.w(", %v)", n)
		default:
			TODO("%s: %T", d.Position, y)
		}
	case it != nil && it.ID() == idUint8Ptr:
		switch x := d.Value.(type) {
		case *ir.CompositeValue:
			switch len(x.Values) {
			case 1:
				switch y := x.Values[0].(type) {
				case *ir.StringValue:
					g.w("%s = %v{(*byte)(unsafe.Pointer(str(%v)))}", nm, g.typ(t), g.string(y.StringID))
					break outer
				default:
					TODO("%s: %T", d.Position, y)
				}
			default:
				TODO("%s: t %v it %v", d.Position, t, it)
			}
		default:
			TODO("%s: %T", d.Position, x)
		}
		fallthrough
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
	g.w("func bug20530(interface{}) {} //TODO remove when https://github.com/golang/go/issues/20530 is fixed.\n")
	g.w("func i16(n int16) int16 { return n }\n")
	g.w("func i32(n int32) int32 { return n }\n")
	g.w("func i64(n int64) int64 { return n }\n")
	g.w("func i8(n int8) int8 { return n }\n")
	g.w("func init() { nzf32 *= -1; nzf64 *= -1 }\n")
	g.w("func u16(n uint16) uint16 { return n }\n")
	g.w("func u32(n uint32) uint32 { return n }\n")
	g.w("func u64(n uint64) uint64 { return n }\n")
	g.w("func u8(n byte) byte { return n }\n")
	g.w("var inf = math.Inf(1)\n")
	g.w("var nzf32 float32 // -0.0\n")
	g.w("var nzf64 float64 // -0.0\n")
	for _, v := range g.helpers(g.copies) {
		g.w("func copy%d(d, s *%[2]v) *%[2]v { *d = *s; return d }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
	}
	for _, v := range g.helpers(g.elems) {
		t := g.tc.MustType(v.TypeID)
		sz := g.model.Sizeof(t.(*ir.PointerType).Element)
		g.w("func elem%d(a %[2]v, index uintptr) %[2]v { return (%[2]v)(unsafe.Pointer(uintptr(unsafe.Pointer(a))+%[3]v*index)) }\n", g.reg(v.TypeID), g.typ2(v.TypeID), sz)
	}
	for _, v := range g.helpers(g.postIncs) {
		switch {
		case g.tc.MustType(v.TypeID).Kind() == ir.Pointer:
			g.w("func postInc%d(p *%[2]v, d int) %[2]v { q := (*uintptr)(unsafe.Pointer(p)); v := *q; *q += uintptr(d); return (%[2]v)(unsafe.Pointer(v)) }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
		default:
			g.w("func postInc%d(p *%[2]v, d %[2]v) %[2]v { v := *p; *p += d; return v }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
		}
	}
	for _, v := range g.helpers(g.preIncs) {
		switch {
		case g.tc.MustType(v.TypeID).Kind() == ir.Pointer:
			g.w("func preInc%d(p *%[2]v, d int) %[2]v { q := (*uintptr)(unsafe.Pointer(p)); v := *q + uintptr(d); *q = v; return (%[2]v)(unsafe.Pointer(v)) }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
		default:
			g.w("func preInc%d(p *%[2]v, d %[2]v) %[2]v { v := *p + d; *p = v; return v }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
		}
	}
	for _, v := range g.helpers(g.storebits) {
		g.w("func storebits%d(p *%[2]v, v %[2]v, m uint64, o uint) %[2]v { *p = *p&^%[2]v(m)|(v<<o&%[2]v(m)); return v }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
	}
	for _, v := range g.helpers(g.stores) {
		g.w("func store%d(p *%[2]v, v %[2]v) %[2]v { *p = v; return v }\n", g.reg(v.TypeID), g.typ2(v.TypeID))
	}
	defined := map[ir.TypeID]struct{}{}
	var a []int
	for k, v := range g.tm {
		defined[k] = struct{}{}
		if !strings.Contains(v, ".") {
			a = append(a, int(k))
		}
	}
	sort.Ints(a)
	for _, v := range a {
		id := ir.TypeID(v)
		g.w("\ntype %s %v // t%d %v\n", g.tm[id], g.fullType(id), g.reg(id), id)
	}
more:
	a = a[:0]
	for k := range g.types {
		if _, ok := defined[k]; !ok {
			a = append(a, int(k))
		}
	}
	sort.Ints(a)
	for _, v := range a {
		id := ir.TypeID(v)
		g.w("\ntype t%d %v // %v\n", g.reg(id), g.fullType(id), id)
		defined[id] = struct{}{}
	}
	if len(a) != 0 {
		goto more
	}
	if g.strings.Len() != 0 {
		g.w("func str(n int) *int8 { return (*int8)(unsafe.Pointer(&strTab[n]))}\n")
		g.w("func wstr(n int) *int32 { return (*int32)(unsafe.Pointer(&strTab[n]))}\n") //TODO Windows UTF-16
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

var (
	re  = regexp.MustCompile(`\n\n\treturn`)
	re2 = regexp.MustCompile(`\n\n}`)
	re3 = regexp.MustCompile(`\n\t;`)
	re4 = regexp.MustCompile(`\n\n\t\treturn`)
	re5 = regexp.MustCompile(`\n\n\t}`)
	re6 = regexp.MustCompile(`{\n\n`)
)

// New writes Go code generated from obj to out.  No package or import clause
// is generated. The types argument is consulted for named types.
func New(out io.Writer, obj []ir.Object, types map[ir.TypeID]string) (err error) {
	var g *gen

	defer func() {
		switch x := recover().(type) {
		case nil:
			b := g.out.Bytes()
			i := bytes.IndexByte(b, '\n')
			b = b[i+1:] // Remove package clause.
			b = re.ReplaceAll(b, []byte("\n\treturn"))
			b = re2.ReplaceAll(b, []byte("\n}"))
			b = re3.ReplaceAll(b, nil)
			b = re4.ReplaceAll(b, []byte("\n\t\treturn"))
			b = re5.ReplaceAll(b, []byte("\n\t}"))
			b = re6.ReplaceAll(b, []byte("{\n"))
			_, err = out.Write(b)
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

	g = newGen(obj, types)
	return g.gen()
}
