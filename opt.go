// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build !irgo.noopt

//TODO TCC 21_: crt.Xprintf(tls, str(20), unsafe.Pointer((*int8)(unsafe.Pointer(&_destarray))))
//TODO P2U(U2P(x))

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

func (o *opt) not(n ast.Expr) ast.Expr {
	switch x := n.(type) {
	case *ast.BinaryExpr:
		switch x.Op {
		case token.LEQ:
			x.Op = token.GTR
			return x
		case token.GTR:
			x.Op = token.LEQ
			return x
		case token.LSS:
			x.Op = token.GEQ
			return x
		case token.GEQ:
			x.Op = token.LSS
			return x
		case token.EQL:
			x.Op = token.NEQ
			return x
		case token.NEQ:
			x.Op = token.EQL
			return x
		case token.LOR:
			x.X = o.not(x.X)
			x.Op = token.LAND
			x.Y = o.not(x.Y)
			return x
		case token.LAND:
			x.X = o.not(x.X)
			x.Op = token.LOR
			x.Y = o.not(x.Y)
			return x
		default:
			TODO("%s: %v", o.pos(n), x.Op)
		}
	case *ast.ParenExpr:
		return o.not(x.X)
	default:
		TODO("%s: %T", o.pos(n), x)
	}
	panic("internal error")
}

func (o *opt) expr(n *ast.Expr) {
	switch x := (*n).(type) {
	case nil:
		// nop
	case *ast.ArrayType:
		// nop
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
								*n = &ast.ParenExpr{
									X: o.not(y.Args[0]),
								}
							}
						case *ast.CallExpr:
							switch p := w.Fun.(type) {
							case *ast.Ident:
								switch p.Name {
								case "bool2int":
									x.X = &ast.ParenExpr{
										X: y.Args[0],
									}
									x.Y = &ast.ParenExpr{
										X: w.Args[0],
									}
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
						case *ast.CallExpr:
							switch p := w.Fun.(type) {
							case *ast.Ident:
								switch p.Name {
								case "bool2int":
									x.X = &ast.ParenExpr{
										X: y.Args[0],
									}
									x.Y = &ast.ParenExpr{
										X: w.Args[0],
									}
								}
							}
						}
					}
				}
			}
		}
	case *ast.CallExpr:
		o.expr(&x.Fun)
		for i := range x.Args {
			o.expr(&x.Args[i])
			switch y := x.Args[i].(type) {
			case *ast.ParenExpr:
				x.Args[i] = y.X
			}
		}
		switch y := x.Fun.(type) {
		case *ast.Ident:
			switch y.Name {
			case "float64":
				switch z := x.Args[0].(type) {
				case *ast.BasicLit:
					if strings.IndexByte(z.Value, '.') > 0 {
						*n = z
					}
				case *ast.UnaryExpr:
					if z.Op == token.SUB {
						switch z.X.(type) {
						case *ast.BasicLit:
							*n = z
						}
					}
				}
			}
			/*
			  0: *ast.CallExpr {
			  .  Fun: *ast.ParenExpr {
			  .  .  Lparen: irgo.out:46:86
			  .  .  X: *ast.SelectorExpr {
			  .  .  .  X: *ast.Ident {
			  .  .  .  .  NamePos: irgo.out:46:87
			  .  .  .  .  Name: "unsafe"
			  .  .  .  }
			  .  .  .  Sel: *ast.Ident {
			  .  .  .  .  NamePos: irgo.out:46:94
			  .  .  .  .  Name: "Pointer"
			  .  .  .  }
			  .  .  }
			  .  .  Rparen: irgo.out:46:102
			  .  }
			  .  Lparen: irgo.out:46:103
			  .  Args: []ast.Expr (len = 1) {
			  .  .  0: *ast.CallExpr {
			  .  .  .  Fun: *ast.SelectorExpr {
			  .  .  .  .  X: *ast.Ident {
			  .  .  .  .  .  NamePos: irgo.out:46:104
			  .  .  .  .  .  Name: "unsafe"
			  .  .  .  .  }
			  .  .  .  .  Sel: *ast.Ident {
			  .  .  .  .  .  NamePos: irgo.out:46:111
			  .  .  .  .  .  Name: "Pointer"
			  .  .  .  .  }
			  .  .  .  }
			  .  .  .  Lparen: irgo.out:46:118
			  .  .  .  Args: []ast.Expr (len = 1) {
			  .  .  .  .  0: *ast.UnaryExpr {
			  .  .  .  .  .  OpPos: irgo.out:46:120
			  .  .  .  .  .  Op: &
			  .  .  .  .  .  X: *ast.Ident {
			  .  .  .  .  .  .  NamePos: irgo.out:46:121
			  .  .  .  .  .  .  Name: "_jones"
			  .  .  .  .  .  .  Obj: *(obj @ 464)
			  .  .  .  .  .  }
			  .  .  .  .  }
			  .  .  .  }
			*/
		case *ast.ParenExpr:
			switch z := y.X.(type) {
			case *ast.SelectorExpr:
				switch w := z.X.(type) {
				case *ast.Ident:
					switch w.Name {
					case "unsafe":
						switch z.Sel.Name {
						case "Pointer":
							switch w2 := x.Args[0].(type) {
							case *ast.CallExpr:
								switch w3 := w2.Fun.(type) {
								case *ast.SelectorExpr:
									switch w4 := w3.X.(type) {
									case *ast.Ident:
										switch w4.Name {
										case "unsafe":
											switch w3.Sel.Name {
											case "Pointer":
												x.Args[0] = w2.Args[0]
											}
										}
									}
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
		case *ast.SelectorExpr:
			switch y.X.(type) {
			case *ast.Ident:
				*n = y
			}
		case *ast.UnaryExpr:
			switch y.Op {
			case token.AND, token.MUL:
				*n = y
			}
		}
	case *ast.SelectorExpr:
		o.expr(&x.X)
		switch y := x.X.(type) {
		case *ast.UnaryExpr:
			if y.Op == token.AND {
				x.X = y.X
			}
		}
	case *ast.SliceExpr:
		o.expr(&x.X)
		o.expr(&x.Low)
		o.expr(&x.High)
		o.expr(&x.Max)
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
	case *ast.TypeAssertExpr:
		o.expr(&x.X)
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
		o.body(x.Body)
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

func (o *opt) body(l []ast.Stmt) {
	for i := range l {
		o.stmt(&l[i])
	}
	if len(l) < 2 {
		return
	}

	for i, v := range l {
		if i == len(l)-1 {
			break
		}

		switch x := v.(type) {
		case *ast.AssignStmt:
			if len(x.Lhs) != 1 {
				break
			}

			switch y := x.Lhs[0].(type) {
			case *ast.Ident:
				if y.Name != "r0" {
					break
				}

				switch z := l[i+1].(type) {
				case *ast.ReturnStmt:
					if len(z.Results) != 0 {
						break
					}

					z.Results = x.Rhs
					l[i] = &ast.EmptyStmt{}
				}
			}
		case *ast.LabeledStmt:
		more:
			switch x2 := x.Stmt.(type) {
			case *ast.LabeledStmt:
				x = x2
				goto more
			case *ast.AssignStmt:
				if len(x2.Lhs) != 1 {
					break
				}

				switch y := x2.Lhs[0].(type) {
				case *ast.Ident:
					if y.Name != "r0" {
						break
					}

					switch z := l[i+1].(type) {
					case *ast.ReturnStmt:
						if len(z.Results) != 0 {
							break
						}

						z.Results = x2.Rhs
						x.Stmt = &ast.EmptyStmt{}
					}
				}
			}
		}
	}
}

func (o *opt) blockStmt(n *ast.BlockStmt) {
	o.body(n.List)
}

func (o *opt) spec(n *ast.Spec) {
	switch x := (*n).(type) {
	case *ast.TypeSpec:
		// nop
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
	// ast.Print(o.fset, root)
	o.g.out.Reset()
	return format.Node(o.g.out, o.fset, root)
}
