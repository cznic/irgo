// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build irgo.noopt

package irgo

import (
	"go/format"
	"go/parser"
	"go/token"
)

type opt struct {
	fset *token.FileSet
	g    *gen
	ver  int
}

func newOpt(g *gen) *opt {
	return &opt{
		g: g,
	}
}

func (o *opt) opt() error {
	o.fset = token.NewFileSet()
	root, err := parser.ParseFile(o.fset, "irgo.out", o.g.out.Bytes(), parser.ParseComments)
	if err != nil {
		return nil // noopt is for debugging, want to see the incorrect product anyway.
	}

	o.g.out.Reset()
	return format.Node(o.g.out, o.fset, root)
}
