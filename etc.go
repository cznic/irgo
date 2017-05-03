// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package irgo

import (
	"github.com/cznic/ir"
	"github.com/cznic/sortutil"
	"sort"
	"unsafe"
)

var (
	idMain = ir.NameID(dict.SID("main"))
)

type node struct {
	ops     []ir.Operation
	in, out nodes
}

type nodes []*node

func (n nodes) Len() int { return len(n) }

func (n nodes) Less(i, j int) bool {
	return uintptr(unsafe.Pointer(n[i])) < uintptr(unsafe.Pointer(n[j]))
}

func (n nodes) Swap(i, j int) { n[i], n[j] = n[j], n[i] }

func newGraph(ops []ir.Operation) *node {
	a := sort.IntSlice{0}
	for i, v := range ops {
		switch v.(type) {
		case
			*ir.Jmp,
			*ir.JmpP,
			*ir.Jnz,
			*ir.Jz,
			*ir.Return:
			a = append(a, i+1)
		case *ir.Label:
			a = append(a, i)
		}
	}
	a = a[:sortutil.Dedupe(a)]
	var nodes nodes
	for i := range a[1:] {
		nodes = append(nodes, &node{ops: ops[a[i]:a[i+1]]})
	}
	labels := map[int]*node{}
	for _, v := range nodes {
		if x, ok := v.ops[0].(*ir.Label); ok {
			n := int(x.NameID)
			if n == 0 {
				n = -x.Number
			}
			labels[n] = v
		}
	}
	panic("TODO")
}
