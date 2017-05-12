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

const (
	_ xop = iota
	land
	lop
	lor
	nop
	ternary
)

var (
	_ operation = xop(0)

	idFloat64 = ir.TypeID(dict.SID("float64"))
	idInt32   = ir.TypeID(dict.SID("int32"))
	idInt64   = ir.TypeID(dict.SID("int64"))
	idMain    = ir.NameID(dict.SID("main"))
	idUint64  = ir.TypeID(dict.SID("uint64"))
	idVoidPtr = ir.TypeID(dict.SID("*struct{}"))

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

type xop int

// Pos implements operation.
func (xop) Pos() token.Position { return token.Position{} }

type expr struct {
	Expr *exprNode
	token.Position
}

func newExpr(n *exprNode, pos token.Position) *expr { return &expr{n, pos} }

// Pos implements operation.
func (e *expr) Pos() token.Position { return e.Position }

type exprNode struct {
	Childs exprList
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
func (p *exprList) push(e *exprNode)                  { *p = append(*p, e) }
func (p *exprList) unop(op operation, t ir.TypeID)    { p.op(op, t, exprList{p.pop()}) }
func (p exprList) String() string                     { return pretty(p) }

func (p *exprList) op(op operation, t ir.TypeID, childs exprList) {
	p.push(&exprNode{Op: op, TypeID: t, Childs: childs})
}

func (p *exprList) binop(op operation, t ir.TypeID) {
	b := p.pop()
	a := p.pop()
	p.op(op, t, exprList{a, b})
}

func (p *exprList) ternary(t ir.TypeID) {
	c := p.pop()
	b := p.pop()
	a := p.pop()
	p.op(ternary, t, exprList{a, b, c})
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
	invalid     bool
	outm        map[*node]struct{}
}

func (n *node) check() {
	if n.invalid {
		panic("internal error")
	}
}

func (n *node) addEdge(dest *node) {
	n.check()
	dest.check()
	if n.outm == nil {
		n.outm = map[*node]struct{}{}
	}
	if _, ok := n.outm[dest]; !ok {
		n.Out = append(n.Out, dest)
		n.outm[dest] = struct{}{}
	}
}

func (n *node) removeEdge(dest *node) {
	n.check()
	dest.check()
	//TODO if _, ok := c.outm[dest]; !ok {
	//TODO 	panic("internal error")
	//TODO }

	for i, v := range n.Out {
		if v == dest {
			n.Out = append(n.Out[:i:i], n.Out[i+1:]...)
			delete(n.outm, dest)
			return
		}
	}

	//TODO panic("internal error 174")
}

func (n *node) append(m *node) {
	for _, v := range m.Out {
		n.addEdge(v)
	}
	n.removeEdge(m)
	if _, ok := m.Ops[0].(*ir.Label); ok {
		m.Ops[0] = nop
	}
	n.Ops = n.Ops[:len(n.Ops)+len(m.Ops)]
	n.Fallthrough = m.Fallthrough
	m.invalid = true
}

type graph struct {
	*gen
	ir.TypeCache
	label2codeNode map[int]*node
	land           map[int]int
	lor            map[int]int
}

func newGraph(gen *gen, ops []ir.Operation) (nodes []*node, labelsUsed map[int]struct{}) {
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
		nodes = append(nodes, &node{Ops: out[a[i]:a[i+1]]})
	}

	labelsUsed = g.addEdges(nodes)
	g.computeStackStates(map[*node]struct{}{}, nodes[0], stack{})
	g.processExpressions(map[*node]struct{}{}, nodes[0])
	w := 0
	for _, v := range nodes {
		if !v.invalid {
			nodes[w] = v
			w++
		}
	}
	return nodes[:w], labelsUsed
}

func splitPoints(ops []ir.Operation) sort.IntSlice {
	a := sort.IntSlice{0}
	for i, op := range ops {
		switch x := op.(type) {
		case
			//TODO 	*ir.JmpP,
			*ir.Jmp,
			*ir.Return,
			*ir.Switch:
			a = append(a, i+1)
		case *ir.Label:
			a = append(a, i)
		case
			*ir.Add,
			*ir.AllocResult,
			*ir.And,
			*ir.Argument,
			*ir.Arguments,
			*ir.BeginScope,
			*ir.Bool,
			*ir.Call,
			*ir.CallFP,
			*ir.Const32,
			*ir.Const64,
			*ir.Convert,
			*ir.Copy,
			*ir.Div,
			*ir.Drop,
			*ir.Dup,
			*ir.Element,
			*ir.EndScope,
			*ir.Eq,
			*ir.Field,
			*ir.Geq,
			*ir.Global,
			*ir.Gt,
			*ir.Jnz,
			*ir.Jz,
			*ir.Leq,
			*ir.Load,
			*ir.Lt,
			*ir.Mul,
			*ir.Neq,
			*ir.Nil,
			*ir.Not,
			*ir.Or,
			*ir.PostIncrement,
			*ir.PreIncrement,
			*ir.Rem,
			*ir.Result,
			*ir.Store,
			*ir.StringConst,
			*ir.Sub,
			*ir.Variable,
			*ir.VariableDeclaration,
			*ir.Xor:
			// nop
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	}
	return a[:sortutil.Dedupe(a)]
}

func (g *graph) addEdges(nodes []*node) map[int]struct{} {
	for _, v := range nodes {
		v.check()
	}
	// Collect symbol table.
	labelsUsed := map[int]struct{}{}
	for _, v := range nodes {
		if x, ok := v.Ops[0].(*ir.Label); ok {
			g.label2codeNode[label(x)] = v
		}
	}

	// Complete the graph.
	for i, node := range nodes {
		var op operation
		for _, op = range node.Ops {
			switch x := op.(type) {
			case *ir.Jmp:
				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				labelsUsed[n] = struct{}{}
				node.addEdge(g.label2codeNode[n])
			case *ir.Jz:
				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				labelsUsed[n] = struct{}{}
				node.addEdge(g.label2codeNode[n])
				node.addEdge(nodes[i+1]) //TODO- Now it makes one TCC test fail
			case *ir.Jnz:
				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				labelsUsed[n] = struct{}{}
				node.addEdge(g.label2codeNode[n])
			case *ir.Switch:
				for _, v := range x.Labels {
					n := int(v.NameID)
					if n == 0 {
						n = -v.Number
					}
					labelsUsed[n] = struct{}{}
					node.addEdge(g.label2codeNode[n])
				}
				n := int(x.Default.NameID)
				if n == 0 {
					n = -x.Default.Number
				}
				labelsUsed[n] = struct{}{}
				node.addEdge(g.label2codeNode[n])
			case
				*ir.Add,
				*ir.AllocResult,
				*ir.And,
				*ir.Argument,
				*ir.Arguments,
				*ir.BeginScope,
				*ir.Bool,
				*ir.Call,
				*ir.CallFP,
				*ir.Const32,
				*ir.Const64,
				*ir.Convert,
				*ir.Copy,
				*ir.Div,
				*ir.Drop,
				*ir.Dup,
				*ir.Element,
				*ir.EndScope,
				*ir.Eq,
				*ir.Field,
				*ir.Geq,
				*ir.Global,
				*ir.Gt,
				*ir.Label,
				*ir.Leq,
				*ir.Load,
				*ir.Lt,
				*ir.Mul,
				*ir.Neq,
				*ir.Nil,
				*ir.Not,
				*ir.Or,
				*ir.PostIncrement,
				*ir.PreIncrement,
				*ir.Rem,
				*ir.Result,
				*ir.Return,
				*ir.Store,
				*ir.StringConst,
				*ir.Sub,
				*ir.Variable,
				*ir.VariableDeclaration,
				*ir.Xor:
				// nop
			default:
				TODO("%s: %T", x.Pos(), x)
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
	return labelsUsed
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
		lorOp1				[bool1]	// was jnz A
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
	if n == nil {
		return
	}

	if _, ok := m[n]; ok {
		return
	}

	n.check()
	m[n] = struct{}{}
	if len(s) != 0 {
		TODO("%s: TODO stack(%v): %v\n\t%s", n.Ops[0].Pos(), len(s), n.Ops[0], s)
	}
	for i := 0; i < len(n.Ops); i++ {
		op := n.Ops[i]
		// fmt.Printf("%#05x(%v) %v %v (pre)\n", i, len(n.Ops), op, s) //TODO-
		switch x := op.(type) {
		case *ir.Add:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.And:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.AllocResult:
			s = s.pushT(x.TypeID)
		case *ir.Argument:
			s = s.pushT(g.qptrID(g.gen.f.t.Arguments[x.Index].ID(), x.Address))
		case *ir.Bool:
			s = s.pop().pushT(idInt32)
		case *ir.Call:
			for i := 0; i < x.Arguments; i++ {
				s = s.pop()
			}
		case *ir.CallFP:
			for i := 0; i < x.Arguments+1; i++ {
				s = s.pop()
			}
		case *ir.Const32:
			s = s.push(stackItem{TypeID: x.TypeID, Value: &ir.Int32Value{Value: x.Value}})
		case *ir.Const64:
			s = s.push(stackItem{TypeID: x.TypeID, Value: &ir.Int64Value{Value: x.Value}})
		case *ir.Convert:
			s = s.pop().pushT(x.Result)
		case *ir.Copy:
			s = s.pop()
		case *ir.Div:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Drop:
			s = s.pop()
		case *ir.Dup:
			s = s.push(s.tos())
		case *ir.Element:
			t := g.tc.MustType(x.TypeID).(*ir.PointerType).Element
			s = s.pop().pop().pushT(g.qptrID(t.ID(), x.Address))
		case *ir.Field:
			t := g.tc.MustType(x.TypeID).(*ir.PointerType).Element.(*ir.StructOrUnionType)
			ft := t.Fields[x.Index]
			if x.Address {
				ft = ft.Pointer()
			}
			s = s.pop().pushT(ft.ID())
		case *ir.Global:
			s = s.pushT(g.qptrID(g.obj[x.Index].Base().TypeID, x.Address))
		case *ir.Jmp:
			if len(s) == 0 {
				break
			}

			n0 := label(n.Ops[:i+2][i+1].(*ir.Label))
			var found bool
			for j := i - 1; j >= 0; j-- {
				if x, ok := n.Ops[j].(*ir.Jz); ok {
					nn := int(x.NameID)
					if nn == 0 {
						nn = -x.Number
					}
					if nn == n0 {
						n.Ops[j] = nop
						found = true
						break
					}
				}
			}
			if !found {
				panic("internal error")
			}
			n.Ops[i] = nop
			n.append(g.label2codeNode[n0])
			n1 := int(x.NameID)
			if n1 == 0 {
				n1 = -x.Number
			}
			join := g.label2codeNode[n1]
			join.Ops[0] = ternary
			n.append(join)
		case *ir.Jnz:
			s = s.pop()
			nn := int(x.NameID)
			if nn == 0 {
				nn = -x.Number
			}
			switch g.lor[nn] {
			case 0:
				if len(s) != 0 {
					switch x := s[len(s)-1].Value.(type) {
					case *ir.Int32Value:
						if x.Value != 1 {
							break
						}

						s = s.pop()
						n.Ops[i] = lop
						g.lor[nn]++
					}
				}
			case 1:
				s = s.pushT(idInt32)
				g.lor[nn]++
				n.Ops[i] = lor   // jnz A
				n.Ops[i+1] = nop // drop
				n.Ops[i+2] = nop // push 0
				join := g.label2codeNode[nn]
				n.append(join)
				m[join] = struct{}{}
			default:
				TODO("%s: %#05x %v %v", x.Pos(), i, g.lor[nn], s)
			}
		case *ir.Jz:
			s = s.pop()
			nn := int(x.NameID)
			if nn == 0 {
				nn = -x.Number
			}
			switch g.land[nn] {
			case 0:
				if len(s) != 0 {
					switch x := s[len(s)-1].Value.(type) {
					case *ir.Int32Value:
						if x.Value != 0 {
							break
						}

						s = s.pop()
						n.Ops[i] = lop
						g.land[nn]++
					}
				}
			case 1:
				s = s.pushT(idInt32)
				g.land[nn]++
				n.Ops[i] = land  // jz A
				n.Ops[i+1] = nop // drop
				n.Ops[i+2] = nop // push 1
				join := g.label2codeNode[nn]
				n.append(join)
				m[join] = struct{}{}
			default:
				TODO("%s: %#05x %v %v", x.Pos(), i, g.land[nn], s)
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
		case *ir.Mul:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.Nil:
			s = s.pushT(x.TypeID)
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
		case *ir.Rem:
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
		case
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope,
			*ir.Label,
			*ir.Not,
			*ir.Return,
			*ir.VariableDeclaration:
			// nop
		case xop:
			switch x {
			case nop:
				// nop
			case ternary:
				s = s.pop()
			default:
				TODO("%v", x)
			}
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
		case
			*ir.Bool,
			*ir.Convert,
			*ir.Drop,
			*ir.Field,
			*ir.Jnz,
			*ir.Jz,
			*ir.Load,
			*ir.Not,
			*ir.PostIncrement,
			*ir.PreIncrement,
			*ir.Switch:

			l.unop(x, t)
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
			*ir.Lt,
			*ir.Mul,
			*ir.Neq,
			*ir.Or,
			*ir.Rem,
			*ir.Store,
			*ir.Sub,
			*ir.Xor:

			l.binop(x, t)
		case
			*ir.Argument,
			*ir.Const32,
			*ir.Const64,
			*ir.Global,
			*ir.Nil,
			*ir.Result,
			*ir.StringConst,
			*ir.Variable:

			l.operand(x, t)
		case
			*ir.EndScope,
			*ir.Jmp,
			*ir.Return,
			*ir.VariableDeclaration:
			return l, i
		case
			*ir.AllocResult,
			*ir.Arguments,
			*ir.BeginScope:
			// nop
		case xop:
			switch x {
			case nop:
				// nop
			case
				land,
				lop,
				lor:

				l.binop(x, t)
			case ternary:
				l.ternary(t)
			default:
				TODO("%v", x)
			}
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	}
	return l, len(ops)
}

func (g *graph) processExpressions(m map[*node]struct{}, n *node) {
	if n == nil {
		return
	}

	if _, ok := m[n]; ok {
		return
	}

	n.check()
	m[n] = struct{}{}
	var out []operation
	for i := 0; i < len(n.Ops); {
		switch x := n.Ops[i].(type) {
		case
			*ir.Argument,
			*ir.Const32,
			*ir.Global,
			*ir.Result,
			*ir.StringConst,
			*ir.Variable:
			// Start of an expression or expression list.
			l, nodes := g.processExpressionList(n.Ops[i:], n.Stacks[i:])
			for _, v := range l {
				out = append(out, newExpr(v, x.Pos()))
			}
			i += nodes
		case
			*ir.AllocResult,
			*ir.Arguments,
			*ir.BeginScope,
			*ir.Call,
			*ir.EndScope,
			*ir.Jmp,
			*ir.Label,
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
	n := -1
	for _, op := range ops {
		switch x := op.(type) {
		case *ir.BeginScope:
			n++
		case *ir.EndScope:
			n--
		case *ir.VariableDeclaration:
			nfo = append(nfo, varNfo{x, n})
		}
	}
	if n != -1 {
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
