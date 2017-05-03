// Copyright 2017 The IRGO Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package irgo

import (
	"fmt"
	"go/token"
	"io"
	"os"
	"path"
	"path/filepath"
	"runtime"

	"github.com/cznic/internal/buffer"
	"github.com/cznic/ir"
	"github.com/cznic/xc"
)

var (
	// Testing amends things for tests.
	Testing bool

	dict = xc.Dict
)

//TODO remove me.
func TODO(msg string, more ...interface{}) string { //TODOOK
	_, fn, fl, _ := runtime.Caller(1)
	fmt.Fprintf(os.Stderr, "%s:%d: %v\n", path.Base(fn), fl, fmt.Sprintf(msg, more...))
	os.Stderr.Sync()
	panic(fmt.Errorf("%s:%d: %v", path.Base(fn), fl, fmt.Sprintf(msg, more...)))
}

type cname struct {
	ir.NameID
	exported bool
}

type gen struct {
	builtins  map[int]string // Object#: qualifier.
	mangled   map[cname]ir.NameID
	obj       []ir.Object
	out       *buffer.Bytes
	qualifier func(*ir.FunctionDefinition) string
	tc        ir.TypeCache
}

func newGen(obj []ir.Object, qualifier func(*ir.FunctionDefinition) string) *gen {
	return &gen{
		builtins:  map[int]string{},
		mangled:   map[cname]ir.NameID{},
		obj:       obj,
		out:       &buffer.Bytes{},
		qualifier: qualifier,
		tc:        ir.TypeCache{},
	}
}

func (g *gen) mangle(nm ir.NameID, exported bool) ir.NameID {
	k := cname{nm, exported}
	if x, ok := g.mangled[k]; ok {
		return x
	}

	var buf buffer.Bytes

	defer buf.Close()

	switch {
	case exported:
		buf.WriteByte('X')
	default:
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

func (g *gen) typ0(buf *buffer.Bytes, t ir.Type) {
	switch t.Kind() {
	case ir.Int8:
		buf.WriteString("int8 ")
	case ir.Int32:
		buf.WriteString("int32 ")
	case ir.Uint64:
		buf.WriteString("uint64 ")
	case ir.Float32:
		buf.WriteString("float32 ")
	case ir.Float64:
		buf.WriteString("float64 ")
	case ir.Pointer:
		buf.WriteString("uintptr ")
	default:
		TODO("%v", t.Kind())
	}
}

func (g *gen) typ(t ir.Type) ir.NameID {
	var buf buffer.Bytes

	defer buf.Close()

	g.typ0(&buf, t)
	return ir.NameID(dict.ID(buf.Bytes()))
}

func (g *gen) isBuiltin(i int) (string, bool) {
	if s, ok := g.builtins[i]; ok {
		return s, ok
	}

	f := g.obj[i]
	if x, ok := f.(*ir.FunctionDefinition); ok && len(x.Body) == 1 {
		if _, ok := x.Body[0].(*ir.Panic); ok {
			s := g.qualifier(x)
			g.builtins[i] = s
			return s, true
		}
	}

	return "", false
}

func (g *gen) pos(p token.Position) token.Position {
	if p.Filename != "" {
		p.Filename = filepath.Base(p.Filename)
	}
	return p
}

func (g *gen) functionDefinition(oi int, f *ir.FunctionDefinition) {
	if _, ok := g.isBuiltin(oi); ok {
		return
	}

	var buf buffer.Bytes

	defer buf.Close()

	g.w("func %v(", g.mangle(f.NameID, f.Linkage == ir.ExternalLinkage))
	t := g.tc.MustType(f.TypeID).(*ir.FunctionType)
	switch {
	case f.NameID == idMain && len(t.Arguments) != 2:
		g.w("int32, uintptr) int32")
	default:
		for i, v := range t.Arguments {
			if i < len(f.Arguments) {
				g.w("%v ", g.mangle(f.Arguments[i], false))
			}
			g.w("%s,", g.typ(v))
		}
		g.w(")")
		if len(t.Results) != 0 {
			g.w("%s", g.typ(t.Results[0]))
		}
	}
	g.w("{ // %v\n", g.pos(f.Position))
	_ = newGraph(f.Body)
	g.w("panic(\"TODO181\")\n")
	g.w("}\n\n")
}

func (g *gen) gen() error {
	for i, v := range g.obj {
		switch x := v.(type) {
		case *ir.FunctionDefinition:
			g.functionDefinition(i, x)
		case *ir.DataDefinition:
			g.w("// %s: %s TODO191\n", x.Position, g.mangle(x.NameID, x.Linkage == ir.ExternalLinkage))
		default:
			panic("internal error")
		}
	}
	return nil
}

// New writes Go code generated from obj to out. No package clause is
// generated.  The result is not formatted. The qualifier function is called
// for implementation defined functions.  It must return the package qualifier,
// if any, that should be used to call the implementation defined function.
func New(obj []ir.Object, out io.Writer, qualifier func(*ir.FunctionDefinition) string) (err error) {
	var g *gen
	if !Testing {
		defer func() {
			switch x := recover().(type) {
			case nil:
				_, err = g.out.WriteTo(out)
			case error:
				err = x
			default:
				err = fmt.Errorf("irgo.New: PANIC: %v", x)
			}
			if e := g.out.Close(); e != nil && err == nil {
				err = e
			}
		}()
	}

	g = newGen(obj, qualifier)
	return g.gen()

}
