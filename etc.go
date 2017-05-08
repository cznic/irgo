// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package irgo

import (
	"go/token"
	"reflect"
	"sort"

	"github.com/cznic/ir"
	"github.com/cznic/sortutil"
	"github.com/cznic/strutil"
)

var (
	idFloat64 = ir.TypeID(dict.SID("float64"))
	idInt32   = ir.TypeID(dict.SID("int32"))
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

type stackItem struct {
	ir.TypeID
	Value ir.Value
}

type stack []stackItem

func (s stack) pop() stack              { return s[:len(s)-1 : len(s)-1] }
func (s stack) push(v stackItem) stack  { return append(s[:len(s):len(s)], v) }
func (s stack) pushT(t ir.TypeID) stack { return append(s[:len(s):len(s)], stackItem{TypeID: t}) }
func (s stack) tos() stackItem          { return s[len(s)-1] }

type exprNode struct {
	Childs exprList
	Op     operation
	Parent *exprNode //TODO not used.
}

type exprList []*exprNode

func (p *exprList) op(op operation, childs exprList) { p.push(&exprNode{Op: op, Childs: childs}) }
func (p *exprList) operand(op operation)             { p.push(&exprNode{Op: op}) }
func (p *exprList) push(e *exprNode)                 { *p = append(*p, e) }
func (p *exprList) unop(op operation)                { p.op(op, exprList{p.pop()}) }
func (p exprList) String() string                    { return pretty(p) }

func (p *exprList) binop(op operation) {
	b := p.pop()
	a := p.pop()
	p.op(op, exprList{a, b})
}

func (p *exprList) pop() *exprNode {
	s := *p
	r := s[len(s)-1]
	*p = s[:len(s)-1]
	return r
}

type codeNode struct {
	Fallthrough *codeNode
	In, Out     []*codeNode
	Ops         []operation
	Stacks      []stack //TODO not used.
}

type codeGraph struct {
	*gen
	ir.TypeCache
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
		case *ir.Dup:
			TODO("%s: TODO %T", x.Pos(), x)
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	}
	return a[:sortutil.Dedupe(a)]
}

func (g *codeGraph) addEdge(src, dest *codeNode) {
	src.Out = append(src.Out, dest)
	dest.In = append(dest.In, src)
}

func (g *codeGraph) addEdges(nodes []*codeNode) (root *codeNode, labelsUsed map[int]struct{}) {
	// Collect symbol table.
	label2codeNode := map[int]*codeNode{}
	labelsUsed = map[int]struct{}{}
	for _, v := range nodes {
		if x, ok := v.Ops[0].(*ir.Label); ok {
			n := int(x.NameID)
			if n == 0 {
				n = -x.Number
			}
			label2codeNode[n] = v
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
				g.addEdge(node, label2codeNode[n])
			case *ir.Jz:
				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				labelsUsed[n] = struct{}{}
				g.addEdge(node, label2codeNode[n])
				g.addEdge(node, nodes[i+1])
			case *ir.Jnz:
				n := int(x.NameID)
				if n == 0 {
					n = -x.Number
				}
				labelsUsed[n] = struct{}{}
				g.addEdge(node, label2codeNode[n])
				g.addEdge(node, nodes[i+1])
			case *ir.Switch:
				for _, v := range x.Labels {
					n := int(v.NameID)
					if n == 0 {
						n = -v.Number
					}
					labelsUsed[n] = struct{}{}
					g.addEdge(node, label2codeNode[n])
				}
				n := int(x.Default.NameID)
				if n == 0 {
					n = -x.Default.Number
				}
				labelsUsed[n] = struct{}{}
				g.addEdge(node, label2codeNode[n])
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
				*ir.Not,
				*ir.Nil,
				*ir.Or,
				*ir.PostIncrement,
				*ir.PreIncrement,
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
			switch x := op.(type) {
			case
				*ir.BeginScope,
				*ir.Const32,
				*ir.Call,
				*ir.Drop,
				*ir.EndScope,
				*ir.Jnz,
				*ir.Label,
				*ir.Mul,
				*ir.VariableDeclaration:

				node.Fallthrough = nodes[i+1]
				g.addEdge(node, nodes[i+1])
			case
				*ir.Jmp,
				*ir.Return,
				*ir.Switch:
				// nop
			default:
				TODO("%s: %T", x.Pos(), x)
			}
		}
	}
	return nodes[0], labelsUsed
}

func (g *codeGraph) ptrID(t ir.TypeID) ir.TypeID { return g.MustType(t).Pointer().ID() }

func (g *codeGraph) qptrID(t ir.TypeID, address bool) ir.TypeID {
	if address {
		return g.ptrID(t)
	}

	return t
}

func (g *codeGraph) computeStackStates(m map[*codeNode]struct{}, n *codeNode, s stack) *codeNode {
	if n == nil {
		return nil
	}

	if _, ok := m[n]; ok {
		return n
	}

	m[n] = struct{}{}
	if len(s) != 0 {
		TODO("%s: TODO stack", n.Ops[0].Pos())
	}
	for _, op := range n.Ops {
		switch x := op.(type) {
		case *ir.Add:
			s = s.pop().pop().pushT(x.TypeID)
		case *ir.AllocResult:
			s = s.pushT(x.TypeID)
		case *ir.Argument:
			s = s.pushT(g.qptrID(x.TypeID, x.Address))
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
		case *ir.Drop:
			s = s.pop()
		case *ir.Element:
			t := g.tc.MustType(x.TypeID).(*ir.PointerType).Element
			s = s.pop().pop().pushT(t.ID())
		case *ir.Field:
			t := g.tc.MustType(x.TypeID).(*ir.PointerType).Element.(*ir.StructOrUnionType)
			ft := t.Fields[x.Index]
			if x.Address {
				ft = ft.Pointer()
			}
			s = s.pop().pushT(ft.ID())
		case *ir.Global:
			s = s.pushT(g.qptrID(x.TypeID, x.Address))
		case *ir.Jmp:
			// nop
		case *ir.Jnz:
			s = s.pop()
		case *ir.Jz:
			s = s.pop()
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
		case *ir.PostIncrement:
			if x.Bits != 0 {
				TODO("%s", x.Pos())
				break
			}

			s = s.pop().pushT(x.TypeID)
		case *ir.Result:
			s = s.pushT(x.TypeID)
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
			s = s.pushT(x.TypeID)
		case
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope,
			*ir.Label,
			*ir.Return,
			*ir.VariableDeclaration:
			// nop
		default:
			TODO("%s: %T", x.Pos(), x)
		}
		n.Stacks = append(n.Stacks, s)
		//fmt.Printf("%s: %p %v %v\n", op.Pos(), n, op, s) //TODO-
	}
	s = n.Stacks[len(n.Stacks)-1]
	g.computeStackStates(m, n.Fallthrough, s)
	for _, v := range n.Out {
		g.computeStackStates(m, v, s)
	}
	return n
}

func (g *codeGraph) processExpressionList(ops []operation) (l exprList, _ int) {
	for i, op := range ops {
		switch x := op.(type) {
		case *ir.Call:
			s := len(l) - x.Arguments
			args := l[s:]
			l = l[:s:s]
			l.op(x, args)
		case *ir.CallFP:
			s := len(l) - x.Arguments - 1
			args := l[s:]
			l = l[:s:s]
			l.op(x, args)
		case
			*ir.Convert,
			*ir.Drop,
			*ir.Field,
			*ir.Jnz,
			*ir.Jz,
			*ir.Load,
			*ir.PostIncrement,
			*ir.Switch:

			l.unop(x)
		case
			*ir.Add,
			*ir.Copy,
			*ir.Element,
			*ir.Eq,
			*ir.Geq,
			*ir.Gt,
			*ir.Leq,
			*ir.Lt,
			*ir.Mul,
			*ir.Neq,
			*ir.Store,
			*ir.Sub:

			l.binop(x)
		case
			*ir.Argument,
			*ir.Const32,
			*ir.Const64,
			*ir.Global,
			*ir.Nil,
			*ir.Result,
			*ir.StringConst,
			*ir.Variable:

			l.operand(x)
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
		default:
			TODO("%s: %T", x.Pos(), x)
		}
	}
	return l, len(ops)
}

func (g *codeGraph) processExpressions(m map[*codeNode]struct{}, n *codeNode) *codeNode {
	if n == nil {
		return nil
	}

	if _, ok := m[n]; ok {
		return n
	}

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
			l, nodes := g.processExpressionList(n.Ops[i:])
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
			TODO("%s: %T", x.Pos(), x)
		}
	}
	n.Ops = out
	g.processExpressions(m, n.Fallthrough)
	for _, v := range n.Out {
		g.processExpressions(m, v)
	}
	return n
}

func newCodeGraph(gen *gen, ops []ir.Operation) (root *codeNode, labelsUsed map[int]struct{}) {
	g := &codeGraph{
		TypeCache: gen.tc,
		gen:       gen,
	}
	a := append(splitPoints(ops), len(ops))
	var nodes []*codeNode
	for i := range a[1:] {
		m, n := a[i], a[i+1]
		out := make([]operation, n-m)
		for i, v := range ops[m:n] {
			out[i] = v
		}
		nodes = append(nodes, &codeNode{Ops: out})
	}
	root, labelsUsed = g.addEdges(nodes)
	root = g.computeStackStates(map[*codeNode]struct{}{}, root, stack{})
	root = g.processExpressions(map[*codeNode]struct{}{}, root)
	return root, labelsUsed
}

func varInfo(ops []ir.Operation) (decls []*ir.VariableDeclaration, scopes []int) {
	n := -1
	for _, op := range ops {
		switch x := op.(type) {
		case *ir.BeginScope:
			n++
		case *ir.EndScope:
			n--
		case *ir.VariableDeclaration:
			decls = append(decls, x)
			scopes = append(scopes, n)
		}
	}
	if n != -1 {
		panic("internal error")
	}
	return decls, scopes
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
