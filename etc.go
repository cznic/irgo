// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package irgo

import (
	"fmt"
	"go/token"
	"reflect"
	"sort"

	"github.com/cznic/ir"
	"github.com/cznic/sortutil"
	"github.com/cznic/strutil"
)

var (
	idComplex128 = ir.TypeID(dict.SID("complex128"))
	idComplex64  = ir.TypeID(dict.SID("complex64"))
	idFloat32    = ir.TypeID(dict.SID("float32"))
	idFloat64    = ir.TypeID(dict.SID("float64"))
	idInt16      = ir.TypeID(dict.SID("int16"))
	idInt32      = ir.TypeID(dict.SID("int32"))
	idInt64      = ir.TypeID(dict.SID("int64"))
	idInt8       = ir.TypeID(dict.SID("int8"))
	idMain       = ir.NameID(dict.SID("main"))
	idUint16     = ir.TypeID(dict.SID("uint16"))
	idUint32     = ir.TypeID(dict.SID("uint32"))
	idUint64     = ir.TypeID(dict.SID("uint64"))
	idUint8      = ir.TypeID(dict.SID("uint8"))
	idVoid       = ir.TypeID(dict.SID("struct{}"))
	idVoidPtr    = ir.TypeID(dict.SID("*struct{}"))

	hooks = strutil.PrettyPrintHooks{
		reflect.TypeOf(ir.NameID(0)): func(f strutil.Formatter, v interface{}, prefix string, suffix string) {
			f.Format(prefix)
			f.Format("%v", v.(ir.NameID))
			f.Format(suffix)
		},
		reflect.TypeOf(ir.TypeID(0)): func(f strutil.Formatter, v interface{}, prefix string, suffix string) {
			f.Format(prefix)
			f.Format("%v", v.(ir.TypeID))
			f.Format(suffix)
		},
		reflect.TypeOf(token.Position{}): func(f strutil.Formatter, v interface{}, prefix string, suffix string) {
			f.Format(prefix)
			f.Format("%v", v.(token.Position).String())
			f.Format(suffix)
		},
	}
)

func pretty(v interface{}) string { return strutil.PrettyString(v, "", "", hooks) }

type stackItem struct {
	ir.TypeID
	Value ir.Value
}

func (s stackItem) String() string {
	if s.Value == nil {
		return s.TypeID.String()
	}

	return fmt.Sprintf("%v:%v", s.TypeID, s.Value)
}

type stack []stackItem

func (s stack) pop() stack              { return s[:len(s)-1 : len(s)-1] }
func (s stack) push(v stackItem) stack  { return append(s[:len(s):len(s)], v) }
func (s stack) pushT(t ir.TypeID) stack { return append(s[:len(s):len(s)], stackItem{TypeID: t}) }
func (s stack) tos() stackItem          { return s[len(s)-1] }

type operation interface {
	Pos() token.Position
}

type expr struct {
	Expr *exprNode
	token.Position
}

func newExpr(n *exprNode, pos token.Position) *expr { return &expr{n, pos} }

// Pos implements operation.
func (e *expr) Pos() token.Position { return e.Position }

type exprNode struct {
	Childs exprList
	Comma  *exprNode
	Op     operation
	Parent *exprNode
	ir.TypeID
}

func (e *exprNode) tree() string {
	for e.Parent != nil {
		e = e.Parent
	}
	return pretty(e)
}

type exprList []*exprNode

func (p *exprList) operand(op operation, t ir.TypeID) { p.push(&exprNode{Op: op, TypeID: t}) }
func (p *exprList) unop(op operation, t ir.TypeID)    { p.op(op, t, exprList{p.pop()}) }
func (p exprList) String() string                     { return pretty(p) }

func (p *exprList) op(op operation, t ir.TypeID, childs exprList) {
	p.push(&exprNode{Op: op, TypeID: t, Childs: childs})
}

func (p *exprList) push(e *exprNode) {
	a := *p
	var c *exprNode
	if n := len(a); n > 0 {
		switch x := a[n-1].Op.(type) {
		case *ir.Drop:
			if x.Comma {
				c = p.pop()
			}
		case *ir.Call:
			if x.Comma {
				c = p.pop()
			}
		case *ir.CallFP:
			if x.Comma {
				c = p.pop()
			}
		}
	}
	e.Comma = c
	*p = append(*p, e)
}

func (p *exprList) binop(op operation, t ir.TypeID) {
	b := p.pop()
	a := p.pop()
	p.op(op, t, exprList{a, b})
}

func (p *exprList) pop() *exprNode {
	s := *p
	r := s[len(s)-1]
	*p = s[:len(s)-1]
	return r
}

type node struct {
	Fallthrough *node
	Ops         []operation
	Out         []*node
	Stacks      []stack
	live        bool
	outm        map[*node]struct{}
	valid       bool
}

func (n *node) addEdge(dest *node) {
	if n.outm == nil {
		n.outm = map[*node]struct{}{}
	}
	if _, ok := n.outm[dest]; !ok {
		n.Out = append(n.Out, dest)
		n.outm[dest] = struct{}{}
	}
}

func (n *node) removeEdge(dest *node) {
	for i, v := range n.Out {
		if v == dest {
			n.Out = append(n.Out[:i:i], n.Out[i+1:]...)
			delete(n.outm, dest)
			return
		}
	}
}

type graph struct {
	*gen
	ir.TypeCache
	label2codeNode map[int]*node
	land           map[int]int
	lor            map[int]int
}

func newGraph(gen *gen, ops []ir.Operation) (nodes []*node) {
	g := &graph{
		TypeCache:      gen.tc,
		gen:            gen,
		label2codeNode: map[int]*node{},
		land:           map[int]int{},
		lor:            map[int]int{},
	}
	out := make([]operation, len(ops))
	for i, v := range ops {
		out[i] = v
	}
	a := append(splitPoints(ops), len(ops))
	for i := range a[1:] {
		nodes = append(nodes, &node{Ops: out[a[i]:a[i+1]], valid: true})
	}

	g.addEdges(nodes)
	g.computeStackStates(map[*node]struct{}{}, nodes[0], stack{})
	g.processExpressions(map[*node]struct{}{}, nodes[0])
	w := 0
	for _, v := range nodes {
		if v.valid && v.live {
			nodes[w] = v
			w++
		}
	}
	return nodes[:w]
}

func splitPoints(ops []ir.Operation) sort.IntSlice {
	a := sort.IntSlice{0}
	for i, op := range ops {
		switch x := op.(type) {
		case *ir.Jmp:
			if !x.Cond {
				a = append(a, i+1)
			}
		case
			//TODO 	*ir.JmpP,
			*ir.Return,
			*ir.Switch:
			a = append(a, i+1)
		case *ir.Label:
			if !x.LOr && !x.LAnd && !x.Nop && !x.Cond {
				a = append(a, i)
			}
		}
	}
	return a[:sortutil.Dedupe(a)]
}

func (g *graph) addEdges(nodes []*node) {
	// Collect symbol table.
	for _, v := range nodes {
		if x, ok := v.Ops[0].(*ir.Label); ok && !x.LOr && !x.LAnd && !x.Nop && !x.Cond {
			g.label2codeNode[label(x)] = v
		}
	}

	// Complete the graph.
	for i, node := range nodes {
		var op operation
		for _, op = range node.Ops {
			switch x := op.(type) {
			case *ir.Jmp:
				if x.Cond {
					break
				}

				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				node.addEdge(g.label2codeNode[n])
			case *ir.Jz:
				if x.LOp {
					break
				}

				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				node.addEdge(g.label2codeNode[n])
			case *ir.Jnz:
				if x.LOp {
					break
				}

				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				node.addEdge(g.label2codeNode[n])
			case *ir.Switch:
				for _, v := range x.Labels {
					n := int(v.NameID)
					if n == 0 {
						n = -v.Number
					}
					node.addEdge(g.label2codeNode[n])
				}
				n := int(x.Default.NameID)
				if n == 0 {
					n = -x.Default.Number
				}
				node.addEdge(g.label2codeNode[n])
			}
		}
		if i+1 < len(nodes) {
			switch op.(type) {
			case
				*ir.Jmp,
				*ir.Return,
				*ir.Switch:

				// Leaf node, nop.
			default:
				node.Fallthrough = nodes[i+1]
			}
		}
	}
}

func (g *graph) ptrID(t ir.TypeID) ir.TypeID { return g.MustType(t).Pointer().ID() }

func (g *graph) qptrID(t ir.TypeID, address bool) ir.TypeID {
	if address {
		return g.ptrID(t)
	}

	return t
}

/*

Non empty evaluation stack at IR code node boundary.

	Expression "||" Expression
		push 1				[1]
		eval expr			[1 expr1]
		convert to bool if necessary	[1 bool1]
		jnz A				[1]
		eval expr2			[1 expr2]
		convert to bool if necessary	[1 bool2]
		jnz A				[1]
		drop				[]
		push 0				[0]
		.... node boundary .............
		A:				[0/1]
		---- transformation -------------------------------------------
		push 1				[1]
		eval expr			[1 expr1]
		convert to bool if necessary	[1 bool1]
		lop				[bool1]	// was jnz A
		eval expr2			[bool1 expr2]
		convert to bool if necessary	[bool1 bool2]
		lor				[bool1||bool2]	// was jnz A
		// was A:
		... joined node follows

	Expression "&&" Expression
		push 0				[0]
		eval expr			[0 expr1]
		convert to bool if necessary	[0 bool1]
		jz A				[0]
		eval expr2			[0 expr2]
		convert to bool if necessary	[0 bool2]
		jz A				[0]
		drop				[]
		push 1				[1]
		.... node boundary .............
		A:				[0/1]
		---- transformation -------------------------------------------
		see "||"

	Expression '?' ExpressionList ':' Expression
		eval expr			[expr1]
		convert to bool if necessary	[bool1]
		jz 0				[]
		eval exprlist			[exprList]
		jmp 1				[exprList]
		.... node boundary .............
		0: eval expr2			[expr2]
		.... node boundary .............
		1:				[exprList/expr2]
		---- transformation -------------------------------------------
		eval expr			[expr1]
		convert to bool if necessary	[bool1]
		nop				[bool1]
		eval exprlist			[bool1 exprList]
		nop				[bool1 exprList]
		eval expr2			[bool1 exprList expr2]
		ternary				[exprList/expr2]

expr op= expr.

	// a += 56.78;
	variable        	&#0, *float32	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	dup             	*float32	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	load            	*float32	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	convert         	float32, float64	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	const           	0x404c63d70a3d70a4, float64	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:9
	add             	float64	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	convert         	float64, float32	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	store           	float32	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4
	drop            	float32	; ../cc/testdata/tcc-0.9.26/tests/tests2/22_floating_point.c:23:4

	drop(store(func()(*float32, float32){ p := dup(var); return p, *p+56.78 }))

*/

func (g *graph) computeStackStates(m map[*node]struct{}, n *node, s stack) {
	if n == nil || !n.valid {
		return
	}

	if _, ok := m[n]; ok {
		return
	}

	m[n] = struct{}{}
	n.live = true
	if len(s) != 0 {
		TODO("%s: TODO stack(%v): %v\n\t%s", n.Ops[0].Pos(), len(s), n.Ops[0], s)
	}
	for i := 0; i < len(n.Ops); i++ {
		op := n.Ops[i]
		//fmt.Printf("%#05x(%v) %v %v (pre)\n", i, len(n.Ops), op, s) //TODO-
	outer:
		switch x := op.(type) {
		case *ir.Add:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.AllocResult:
			// nop
		case *ir.And:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Argument:
			s = s.pushT(g.qptrID(g.gen.f.t.Arguments[x.Index].ID(), x.Address))
		case *ir.Bool:
			s = s.pop().pushT(idInt32)
		case *ir.Call:
			for i := 0; i < x.Arguments; i++ {
				s = s.pop()
			}
			t := g.tc.MustType(x.TypeID).(*ir.FunctionType)
			for _, v := range t.Results {
				s = s.pushT(v.ID())
			}
		case *ir.CallFP:
			var tos stackItem
			for i := 0; i < x.Arguments+1; i++ {
				tos = s.tos()
				s = s.pop()
			}
			t := g.tc.MustType(tos.TypeID).(*ir.PointerType).Element.(*ir.FunctionType)
			for _, v := range t.Results {
				s = s.pushT(v.ID())
			}
		case *ir.Const32:
			if !x.LOp {
				s = s.push(stackItem{TypeID: x.TypeID, Value: &ir.Int32Value{Value: x.Value}})
			}
		case *ir.Const64:
			s = s.push(stackItem{TypeID: x.TypeID, Value: &ir.Int64Value{Value: x.Value}})
		case *ir.Convert:
			s = s.pop().pushT(x.Result)
		case *ir.Copy:
			s = s.pop()
		case *ir.Const:
			s = s.pushT(x.TypeID)
		case *ir.Cpl:
			s = s.pop().pushT(x.TypeID)
		case *ir.Div:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Drop:
			if !x.LOp {
				s = s.pop()
			}
		case *ir.Dup:
			s = s.pushT(x.TypeID)
		case *ir.Element:
			s = s.pop()    // index
			tos := s.tos() // array
			t := g.tc.MustType(tos.TypeID)
			switch t.Kind() {
			case ir.Pointer:
				t = t.(*ir.PointerType).Element
				switch t.Kind() {
				case ir.Array:
					t = t.(*ir.ArrayType).Item
				}
			default:
				panic("internal error")
			}
			s = s.pop().pushT(g.qptrID(t.ID(), x.Address))
		case *ir.Field:
			t := g.tc.MustType(x.TypeID).(*ir.PointerType).Element.(*ir.StructOrUnionType)
			ft := t.Fields[x.Index]
			if x.Address {
				ft = ft.Pointer()
			}
			s = s.pop().pushT(ft.ID())
		case *ir.Global:
			o := g.obj[x.Index]
			t := g.tc.MustType(o.Base().TypeID)
			switch y := o.(type) {
			case *ir.DataDefinition:
				switch z := y.Value.(type) {
				case *ir.CompositeValue:
					if t.Kind() == ir.Pointer {
						id := ir.TypeID(dict.SID(fmt.Sprintf("*[%v]%v", len(z.Values), t.(*ir.PointerType).Element)))
						s = s.pushT(g.qptrID(id, x.Address))
						break outer
					}
				}
			}
			s = s.pushT(g.qptrID(t.ID(), x.Address))
		case *ir.Jmp:
			// nop
		case *ir.Jnz:
			if !x.LOp {
				s = s.pop()
			}
		case *ir.Jz:
			if !x.LOp {
				s = s.pop()
			}
		case
			*ir.Eq,
			*ir.Geq,
			*ir.Gt,
			*ir.Leq,
			*ir.Lt,
			*ir.Neq:

			s = s.pop().pop().pushT(idInt32)
		case *ir.Load:
			v := s.tos()
			s = s.pop().pushT(g.tc.MustType(v.TypeID).(*ir.PointerType).Element.ID())
		case *ir.Lsh:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Mul:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Nil:
			s = s.pushT(x.TypeID)
		case *ir.Neg:
			s = s.pop().pushT(x.TypeID)
		case *ir.Or:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.PostIncrement:
			if x.Bits != 0 {
				TODO("%s", x.Pos())
				break
			}

			s = s.pop().pushT(x.TypeID)
		case *ir.PreIncrement:
			if x.Bits != 0 {
				TODO("%s", x.Pos())
				break
			}

			s = s.pop().pushT(x.TypeID)
		case *ir.PtrDiff:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Rem:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Rsh:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Result:
			s = s.pushT(g.qptrID(g.gen.f.t.Results[x.Index].ID(), x.Address))
		case *ir.Store:
			v := s.tos()
			s = s.pop().pop().push(v)
		case *ir.StringConst:
			s = s.pushT(x.TypeID)
		case *ir.Sub:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Switch:
			s = s.pop()
		case *ir.Variable:
			nfo := g.gen.f.varNfo[x.Index]
			s = s.pushT(g.qptrID(nfo.def.TypeID, x.Address))
		case *ir.Xor:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Label:
			switch {
			case x.LOr || x.LAnd:
				s = s.pop().pop().pushT(idInt32)
			case x.Cond:
				s = s.pop()
				tos := s.tos()
				s = s.pop().pop().pushT(tos.TypeID)
			}
		case
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope,
			*ir.Not,
			*ir.Return,
			*ir.VariableDeclaration:
			// nop
		default:
			TODO("%s: %T", x.Pos(), x)
		}
		n.Stacks = append(n.Stacks, s)
		// fmt.Printf("%#05x(%v) %v %v\n", i, len(n.Ops), n.Ops[i], s) //TODO-
	}
	s = n.Stacks[len(n.Stacks)-1]
	g.computeStackStates(m, n.Fallthrough, s)
	for _, v := range n.Out {
		g.computeStackStates(m, v, s)
	}
}

func (g *graph) processExpressionList(ops []operation, stacks []stack) (l exprList, _ int) {
	for i, op := range ops {
		var t ir.TypeID
		if s := stacks[i]; len(s) != 0 {
			t = s.tos().TypeID
		}
		switch x := op.(type) {
		case *ir.Call:
			s := len(l) - x.Arguments
			args := l[s:]
			l = l[:s:s]
			l.op(x, t, args)
		case *ir.CallFP:
			s := len(l) - x.Arguments - 1
			args := l[s:]
			l = l[:s:s]
			l.op(x, t, args)
		case *ir.Dup:
			l.unop(x, t)
			tos := l.pop()
			l.push(tos)
			l.push(tos)
		case *ir.Jnz:
			if !x.LOp {
				l.unop(x, t)
			}
		case *ir.Jz:
			if !x.LOp {
				l.unop(x, t)
			}
		case *ir.Drop:
			if !x.LOp {
				l.unop(x, t)
			}
		case
			*ir.Bool,
			*ir.Convert,
			*ir.Cpl,
			*ir.Field,
			*ir.Load,
			*ir.Neg,
			*ir.Not,
			*ir.PostIncrement,
			*ir.PreIncrement,
			*ir.Switch:

			l.unop(x, t)
		case *ir.Label:
			switch {
			case x.LAnd || x.LOr:
				l.binop(x, t)
			case x.Cond:
				c := l.pop()
				b := l.pop()
				a := l.pop()
				l.op(x, b.TypeID, exprList{a, b, c})
			}
		case
			*ir.Add,
			*ir.And,
			*ir.Copy,
			*ir.Div,
			*ir.Element,
			*ir.Eq,
			*ir.Geq,
			*ir.Gt,
			*ir.Leq,
			*ir.Lsh,
			*ir.Lt,
			*ir.Mul,
			*ir.Neq,
			*ir.Or,
			*ir.PtrDiff,
			*ir.Rem,
			*ir.Rsh,
			*ir.Store,
			*ir.Sub,
			*ir.Xor:

			l.binop(x, t)
		case *ir.Const32:
			if !x.LOp {
				l.operand(x, t)
			}
		case
			*ir.Argument,
			*ir.Const,
			*ir.Const64,
			*ir.Global,
			*ir.Nil,
			*ir.Result,
			*ir.StringConst,
			*ir.Variable:

			l.operand(x, t)
		case *ir.Jmp:
			if !x.Cond {
				return l, i
			}
		case
			*ir.EndScope,
			*ir.Return,
			*ir.VariableDeclaration:
			return l, i
		case
			*ir.AllocResult,
			*ir.Arguments,
			*ir.BeginScope:
			// nop
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	}
	return l, len(ops)
}

func (g *graph) processExpressions(m map[*node]struct{}, n *node) {
	if n == nil || !n.valid {
		return
	}

	if _, ok := m[n]; ok {
		return
	}

	m[n] = struct{}{}
	var out []operation
	for i := 0; i < len(n.Ops); {
		switch x := n.Ops[i].(type) {
		case *ir.Const32:
			if !x.LOp {
				// Start of an expression or expression list.
				l, nodes := g.processExpressionList(n.Ops[i:], n.Stacks[i:])
				for _, v := range l {
					out = append(out, newExpr(v, x.Pos()))
				}
				i += nodes
				break
			}

			i++
		case
			*ir.Argument,
			*ir.Call,
			*ir.CallFP,
			*ir.Const64,
			*ir.Global,
			*ir.Nil,
			*ir.Result,
			*ir.StringConst,
			*ir.Variable:
			// Start of an expression or expression list.
			l, nodes := g.processExpressionList(n.Ops[i:], n.Stacks[i:])
			for _, v := range l {
				out = append(out, newExpr(v, x.Pos()))
			}
			i += nodes
		case *ir.Label:
			if !x.LAnd && !x.LOr && !x.Cond && !x.Nop {
				out = append(out, x)
			}
			i++
		case *ir.Jmp:
			if !x.Cond {
				out = append(out, x)
			}
			i++
		case
			*ir.AllocResult,
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope,
			*ir.Return,
			*ir.VariableDeclaration:

			out = append(out, x)
			i++
		default:
			TODO("%s: %T %#05x", x.Pos(), x, i)
		}
	}
	n.Ops = out
	g.processExpressions(m, n.Fallthrough)
	for _, v := range n.Out {
		g.processExpressions(m, v)
	}
}

func varInfo(ops []ir.Operation) (nfo []varNfo) {
	seq := -1
	var a []int
	for _, op := range ops {
		switch x := op.(type) {
		case *ir.BeginScope:
			seq++
			a = append(a, seq)
		case *ir.EndScope:
			a = a[:len(a)-1]
		case *ir.VariableDeclaration:
			nfo = append(nfo, varNfo{x, a[len(a)-1]})
		}
	}
	if len(a) != 0 {
		panic("internal error")
	}
	return nfo
}

// if n%m != 0 { n += m-n%m }. m must be a power of 2.
func roundup(n, m int) int { return (n + m - 1) &^ (m - 1) }

type switchPair struct {
	ir.Value
	*ir.Label
}

type switchPairs []switchPair

func (s switchPairs) Len() int { return len(s) }

func (s switchPairs) Less(i, j int) bool {
	switch x := s[i].Value.(type) {
	case *ir.Int32Value:
		return x.Value < s[j].Value.(*ir.Int32Value).Value
	case *ir.Int64Value:
		return x.Value < s[j].Value.(*ir.Int64Value).Value
	default:
		TODO("%T", x)
	}
	panic("internal error")
}

func (s switchPairs) Swap(i, j int) { s[i], s[j] = s[j], s[i] }

func label(l *ir.Label) int {
	n := int(l.NameID)
	if n == 0 {
		n = -l.Number
	}
	return n
}

func isZeroValue(v ir.Value) bool {
	switch x := v.(type) {
	case nil:
		return true
	case *ir.AddressValue:
		return false
	case *ir.CompositeValue:
		for _, v := range x.Values {
			if !isZeroValue(v) {
				return false
			}
		}
		return true
	case *ir.Int32Value:
		return x.Value == 0
	case *ir.Int64Value:
		return x.Value == 0
	case *ir.Float32Value:
		return x.Value == 0
	case *ir.Float64Value:
		return x.Value == 0
	case *ir.Complex64Value:
		return x.Value == 0
	case *ir.Complex128Value:
		return x.Value == 0
	case *ir.StringValue:
		return false
	case *ir.WideStringValue:
		return false
	default:
		TODO("isZeroValue %T", x)
	}
	panic("internal error")
}

func isTransitiveVoidPtr(t ir.Type) bool {
	for t.Kind() == ir.Pointer {
		if t.ID() == idVoidPtr {
			return true
		}

		t = t.(*ir.PointerType).Element
	}
	return false
}

func isIntegalType(t ir.TypeID) bool {
	switch t {
	case
		idInt16,
		idInt32,
		idInt64,
		idInt8,
		idUint16,
		idUint32,
		idUint64,
		idUint8:

		return true
	}
	return false
}
