// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package irgo

import (
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"strings"
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

func (o *opt) stmt(n *ast.Stmt) {
	if *n == nil {
		return
	}

	switch x := (*n).(type) {
	case *ast.AssignStmt:
		for i := range x.Lhs {
			o.expr(&x.Lhs[i])
		}
		for i := range x.Rhs {
			o.expr(&x.Rhs[i])
		}
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
	case *ast.ExprStmt:
		switch y := x.X.(type) {
		case *ast.CallExpr:
			o.expr(&x.X)
			switch z := y.Fun.(type) {
			case *ast.Ident:
				switch {
				case z.Name == "drop":
					if zz, ok := y.Args[0].(*ast.CallExpr); ok {
						if zzz, ok := zz.Fun.(*ast.Ident); ok && strings.HasPrefix(zzz.Name, "store_") {
							o.ver++
							x.X = y.Args[0]
						}
					}
				case strings.HasPrefix(z.Name, "store_"):
					if len(y.Args) != 2 {
						o.expr(&x.X)
						return
					}

					var lhs ast.Expr
					switch w := y.Args[0].(type) {
					case *ast.CallExpr:
						lhs = &ast.StarExpr{X: w}
					case *ast.Ident:
						lhs = &ast.StarExpr{X: w}
					case *ast.UnaryExpr:
						lhs = w.X
					default:
						return
						//TODO TODO("%s: %T", o.pos(w), w)
					}
					o.ver++
					*n = &ast.AssignStmt{
						Lhs: []ast.Expr{lhs},
						Tok: token.ASSIGN,
						Rhs: []ast.Expr{y.Args[1]},
					}
					o.stmt(n)
					return
				}
			}
		}
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

func (o *opt) expr(n *ast.Expr) {
	if *n == nil {
		return
	}

	switch x := (*n).(type) {
	case *ast.ArrayType:
		o.expr(&x.Len)
	case *ast.BasicLit:
		// nop
	case *ast.BinaryExpr:
		o.expr(&x.X)
		o.expr(&x.Y)
	case *ast.CallExpr:
		o.expr(&x.Fun)
		for i := range x.Args {
			switch y := x.Args[0].(type) {
			case *ast.ParenExpr:
				o.ver++
				x.Args[i] = y.X
				o.expr(&x.Args[i])
			default:
				o.expr(&x.Args[i])
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
		switch y := x.X.(type) {
		case *ast.CallExpr:
			o.ver++
			*n = y
			o.expr(n)
			return
		case *ast.Ident:
			o.ver++
			*n = y
			return
		case *ast.UnaryExpr:
			o.ver++
			*n = y
			o.expr(n)
			return
		}

		o.expr(&x.X)
	case *ast.SelectorExpr:
		o.expr(&x.X)
	case *ast.StarExpr:
		o.expr(&x.X)
	case *ast.StructType:
		// nop
	case *ast.UnaryExpr:
		o.expr(&x.X)
	default:
		TODO("%s: %T", o.pos(x), x)
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

	ver := -1
	for {
		o.file(root)
		if o.ver == ver {
			break
		}

		ver = o.ver
	}
	o.g.out.Reset()
	return format.Node(o.g.out, o.fset, root)
}
