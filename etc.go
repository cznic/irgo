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
	idMain = ir.NameID(dict.SID("main"))

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

func pretty(v interface{}) string {
	return strutil.PrettyString(v, "", "", hooks)
}

type stackItem struct {
	ir.TypeID
	value ir.Value
}

type stack []stackItem

func (s stack) pop() stack              { return s[:len(s)-1 : len(s)-1] }
func (s stack) push(v stackItem) stack  { return append(s[:len(s):len(s)], v) }
func (s stack) pushT(t ir.TypeID) stack { return append(s[:len(s):len(s)], stackItem{TypeID: t}) }
func (s stack) tos() stackItem          { return s[len(s)-1] }

type enode struct {
	Op     ir.Operation
	Childs []*enode
}

type enodes []*enode

func (p *enodes) op(op ir.Operation, childs []*enode) { p.push(&enode{Op: op, Childs: childs}) }
func (p *enodes) operand(op ir.Operation)             { p.push(&enode{Op: op}) }
func (p *enodes) push(e *enode)                       { *p = append(*p, e) }
func (p *enodes) unop(op ir.Operation)                { p.op(op, []*enode{p.pop()}) }
func (p enodes) String() string                       { return pretty(p) }

func (p *enodes) pop() *enode {
	s := *p
	r := s[len(s)-1]
	*p = s[:len(s)-1]
	return r
}

type gnode struct {
	Expressions []*enode
	in, out     []*gnode
	Ops         []ir.Operation
	stacks      []stack
}

func (n *gnode) size0(m map[*gnode]struct{}) int {
	if _, ok := m[n]; ok {
		return 0
	}

	m[n] = struct{}{}
	r := 1
	for _, v := range n.out {
		r += v.size0(m)
	}
	return r
}

type graph struct {
	*gen
	ir.TypeCache
}

func (n *gnode) size() int { return n.size0(map[*gnode]struct{}{}) }

func splitPoints(ops []ir.Operation) sort.IntSlice {
	a := sort.IntSlice{0}
	for _, op := range ops {
		switch x := op.(type) {
		//TODO case
		//TODO 	*ir.Jmp,
		//TODO 	*ir.JmpP,
		//TODO 	*ir.Jnz,
		//TODO 	*ir.Jz,
		//TODO 	*ir.Return:
		//TODO 	a = append(a, i+1)
		//TODO case *ir.Label:
		//TODO 	a = append(a, i)
		//TODO case *ir.Switch:
		//TODO 	a = append(a, i)
		//TODO 	a = append(a, i+1)
		case
			*ir.AllocResult,
			*ir.Argument,
			*ir.Arguments,
			*ir.BeginScope,
			*ir.Call,
			*ir.CallFP,
			*ir.Const32,
			*ir.Convert,
			*ir.Drop,
			*ir.EndScope,
			*ir.Global,
			*ir.Result,
			*ir.Return,
			*ir.Store,
			*ir.StringConst,
			*ir.Variable,
			*ir.VariableDeclaration:
			// nop
		default:
			TODO("%T", x)
		}
	}
	return a[:sortutil.Dedupe(a)]
}

func (g *graph) addEdges(nodes []*gnode) *gnode {
	// Collect symbol table.
	labels := map[int]*gnode{}
	for _, v := range nodes {
		if x, ok := v.Ops[0].(*ir.Label); ok {
			n := int(x.NameID)
			if n == 0 {
				n = -x.Number
			}
			labels[n] = v
		}
	}

	// Complete the graph.
	for _, node := range nodes {
		for _, op := range node.Ops {
			switch x := op.(type) {
			case
				*ir.AllocResult,
				*ir.Argument,
				*ir.Arguments,
				*ir.BeginScope,
				*ir.Call,
				*ir.CallFP,
				*ir.Const32,
				*ir.Convert,
				*ir.Drop,
				*ir.EndScope,
				*ir.Global,
				*ir.Result,
				*ir.Return,
				*ir.Store,
				*ir.StringConst,
				*ir.Variable,
				*ir.VariableDeclaration:
				// nop
			default:
				TODO("%T", x)
			}
		}
	}
	return nodes[0]
}

func (g *graph) ptrID(t ir.TypeID) ir.TypeID { return g.MustType(t).Pointer().ID() }

func (g *graph) qptrID(t ir.TypeID, address bool) ir.TypeID {
	if address {
		return g.ptrID(t)
	}

	return t
}

func (g *graph) computeStackStates(m map[*gnode]struct{}, n *gnode, stack stack) *gnode {
	if _, ok := m[n]; ok {
		return n
	}

	m[n] = struct{}{}
	for _, op := range n.Ops {
		switch x := op.(type) {
		case *ir.AllocResult:
			stack = stack.pushT(x.TypeID)
		case *ir.Argument:
			stack = stack.pushT(g.qptrID(x.TypeID, x.Address))
		case *ir.Call:
			for i := 0; i < x.Arguments; i++ {
				stack = stack.pop()
			}
		case *ir.CallFP:
			for i := 0; i < x.Arguments+1; i++ {
				stack = stack.pop()
			}
		case *ir.Const32:
			stack = stack.pop().push(stackItem{TypeID: x.TypeID, value: &ir.Int32Value{Value: x.Value}})
		case *ir.Convert:
			stack = stack.pop().pushT(x.Result)
		case *ir.Drop:
			stack = stack.pop()
		case *ir.Global:
			stack = stack.pushT(g.qptrID(x.TypeID, x.Address))
		case *ir.Result:
			stack = stack.pushT(g.qptrID(x.TypeID, x.Address))
		case *ir.Store:
			v := stack.tos()
			stack = stack.pop().push(v)
		case *ir.StringConst:
			stack = stack.pushT(x.TypeID)
		case *ir.Variable:
			stack = stack.pushT(g.qptrID(x.TypeID, x.Address))
		case
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope,
			*ir.Return,
			*ir.VariableDeclaration:
			// nop
		default:
			TODO("%T", x)
		}
		n.stacks = append(n.stacks, stack)
	}
	return n
}

func (g *graph) processExpressionList(ops []ir.Operation) (l enodes, _ int) {
	for i, op := range ops {
		switch x := op.(type) {
		case *ir.Arguments:
			return l, i
		case *ir.Call:
			t := g.MustType(x.TypeID).(*ir.FunctionType)
			r := t.Results
			if len(r) != 0 {
				TODO("%v", r)
				break
			}

			return l, i
		case *ir.CallFP:
			t := g.MustType(x.TypeID).(*ir.PointerType).Element.(*ir.FunctionType)
			r := t.Results
			if len(r) != 0 {
				s := len(l) - x.Arguments
				ch := l[s:]
				l = l[:s:s]
				l.op(x, ch)
				break
			}

			TODO("%v", r)
		case *ir.Convert:
			l.unop(x)
		case
			*ir.Argument,
			*ir.Global:
			l.operand(x)
		default:
			TODO("%T", x)
		}
	}
	panic("TODO")
}

func (g *graph) processExpressions(m map[*gnode]struct{}, n *gnode) *gnode {
	if _, ok := m[n]; ok {
		return n
	}

	m[n] = struct{}{}
	if len(n.in)+len(n.out) != 0 {
		TODO("")
	}

	fmt.Println(pretty(n)) //TODO-
	for i := 0; i < len(n.Ops); i++ {
		switch x := n.Ops[i].(type) {
		case
			*ir.Argument,
			*ir.Global:
			// Start of an expression or expression list.
			l, nodes := g.processExpressionList(n.Ops[i:])
			tail := append([]ir.Operation(nil), n.Ops[i+nodes:]...)
			n.Ops = n.Ops[:i:i]
			n.Expressions = append(n.Expressions[:i:i], l...)
			for range l {
				n.Ops = append(n.Ops, nil)
				//TODO 	n.Expressions[i+j] = v
			}
			n.Ops = append(n.Ops, tail...)
			//TODO i += nodes
			_ = l
			return n
		case
			*ir.Arguments,
			*ir.BeginScope,
			*ir.EndScope:
			// nop
		default:
			TODO("%T", x)
		}
	}
	return n
}

func newGraph(gen *gen, ops []ir.Operation) *gnode {
	g := &graph{
		TypeCache: gen.tc,
		gen:       gen,
	}
	a := append(splitPoints(ops), len(ops))
	var nodes []*gnode
	for i := range a[1:] {
		nodes = append(nodes, &gnode{
			Expressions: make([]*enode, a[i+1]-a[i]),
			Ops:         ops[a[i]:a[i+1]],
		})
	}
	root := g.addEdges(nodes)
	root = g.computeStackStates(map[*gnode]struct{}{}, root, stack{})
	root = g.processExpressions(map[*gnode]struct{}{}, root)
	return root
}

func computeVarDeclScopes(ops []ir.Operation) map[*ir.VariableDeclaration]int {
	r := map[*ir.VariableDeclaration]int{}
	n := -1
	for _, op := range ops {
		switch x := op.(type) {
		case *ir.BeginScope:
			n++
		case *ir.EndScope:
			n++
		case *ir.VariableDeclaration:
			r[x] = n
		}
	}
	return r
}
