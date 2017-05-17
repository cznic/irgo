// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build !irgo.noopt

//TODO goto label; label:
//TODO _ = _var
//TODO named(numbered) types

package irgo

import (
	"go/ast"
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

func (o *opt) pos(n ast.Node) token.Position {
	if n == nil {
		return token.Position{}
	}

	return o.fset.Position(n.Pos())
}

func (o *opt) expr(n *ast.Expr) {
	switch x := (*n).(type) {
	case *ast.ArrayType:
		// nop
	case *ast.CallExpr:
		o.expr(&x.Fun)
		for i := range x.Args {
			o.expr(&x.Args[i])
			switch y := x.Args[i].(type) {
			case *ast.ParenExpr:
				x.Args[i] = y.X
			}
		}
	case *ast.BasicLit:
		// nop
	case *ast.BinaryExpr:
		o.expr(&x.X)
		o.expr(&x.Y)
		switch y := x.X.(type) {
		case *ast.CallExpr:
			switch z := y.Fun.(type) {
			case *ast.Ident:
				switch z.Name {
				case "bool2int":
					switch x.Op {
					case token.EQL:
						switch w := x.Y.(type) {
						case *ast.BasicLit:
							if w.Value == "0" {
								*n = &ast.UnaryExpr{
									Op: token.NOT,
									X: &ast.ParenExpr{
										X: y.Args[0],
									},
								}
							}
						}
					case token.NEQ:
						switch w := x.Y.(type) {
						case *ast.BasicLit:
							if w.Value == "0" {
								*n = &ast.ParenExpr{
									X: y.Args[0],
								}
							}
						}
					}
				}
			}
		}
	case *ast.CompositeLit:
		for i := range x.Elts {
			o.expr(&x.Elts[i])
		}
	case *ast.FuncLit:
		o.blockStmt(x.Body)
	case *ast.FuncType:
		// nop
	case *ast.Ident:
		// nop
	case *ast.IndexExpr:
		o.expr(&x.X)
		o.expr(&x.Index)
	case *ast.KeyValueExpr:
		o.expr(&x.Key)
		o.expr(&x.Value)
	case *ast.ParenExpr:
		o.expr(&x.X)
		switch y := x.X.(type) {
		case
			*ast.CallExpr,
			*ast.Ident:
			*n = y
		case *ast.ParenExpr:
			x.X = y.X
		case *ast.UnaryExpr:
			switch y.Op {
			case token.AND:
				*n = y
			}
		}
	case *ast.SelectorExpr:
		o.expr(&x.X)
	case *ast.StarExpr:
		o.expr(&x.X)
		switch y := x.X.(type) {
		case *ast.UnaryExpr:
			switch y.Op {
			case token.AND:
				*n = y.X
			}
		}
	case *ast.StructType:
		// nop
	case *ast.UnaryExpr:
		o.expr(&x.X)
	default:
		TODO("%s: %T", o.pos(x), x)
	}
}

func (o *opt) stmt(n *ast.Stmt) {
	switch x := (*n).(type) {
	case nil:
		// nop
	case *ast.AssignStmt:
		for i := range x.Lhs {
			o.expr(&x.Lhs[i])
		}
		for i := range x.Rhs {
			o.expr(&x.Rhs[i])
		}
		switch y := x.Lhs[0].(type) {
		case *ast.ParenExpr:
			if len(x.Lhs) == 1 {
				x.Lhs[0] = y.X
			}
		}
		switch y := x.Rhs[0].(type) {
		case *ast.ParenExpr:
			if len(x.Rhs) == 1 {
				x.Rhs[0] = y.X
			}
		}
	case *ast.BlockStmt:
		o.blockStmt(x)
	case *ast.BranchStmt:
		// nop
	case *ast.CaseClause:
		for i := range x.List {
			o.expr(&x.List[i])
		}
		for i := range x.Body {
			o.stmt(&x.Body[i])
		}
	case *ast.DeclStmt:
		o.decl(&x.Decl)
	case *ast.EmptyStmt:
		// nop
	case *ast.ExprStmt:
		o.expr(&x.X)
	case *ast.IfStmt:
		o.stmt(&x.Init)
		o.expr(&x.Cond)
		o.blockStmt(x.Body)
		o.stmt(&x.Else)
	case *ast.LabeledStmt:
		o.stmt(&x.Stmt)
	case *ast.ReturnStmt:
		for i := range x.Results {
			o.expr(&x.Results[i])
		}
	case *ast.SwitchStmt:
		o.stmt(&x.Init)
		o.expr(&x.Tag)
		o.blockStmt(x.Body)
	default:
		TODO("%s: %T", o.pos(x), x)
	}
}

func (o *opt) blockStmt(n *ast.BlockStmt) {
	for i := range n.List {
		o.stmt(&n.List[i])
	}
}

func (o *opt) spec(n *ast.Spec) {
	switch x := (*n).(type) {
	case *ast.ValueSpec:
		for i := range x.Values {
			o.expr(&x.Values[i])
		}
	default:
		TODO("%s: %T", o.pos(x), x)
	}
}

func (o *opt) decl(n *ast.Decl) {
	switch x := (*n).(type) {
	case *ast.FuncDecl:
		o.blockStmt(x.Body)
	case *ast.GenDecl:
		for i := range x.Specs {
			o.spec(&x.Specs[i])
		}
	default:
		TODO("%s: %T", o.pos(x), x)
	}
}

func (o *opt) file(n *ast.File) {
	for i := range n.Decls {
		o.decl(&n.Decls[i])
	}
}

func (o *opt) opt() error {
	o.fset = token.NewFileSet()
	root, err := parser.ParseFile(o.fset, "irgo.out", o.g.out.Bytes(), parser.ParseComments)
	if err != nil {
		return err
	}

	o.file(root)
	o.g.out.Reset()
	return format.Node(o.g.out, o.fset, root)
}
