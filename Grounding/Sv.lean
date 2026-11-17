-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Grounding.Rtl.Netlist
import Grounding.Rtl.Builder
import Grounding.Rtl.Repr

namespace Grounding

open Grounding.Rtl

private opaque SvContextPointed : NonemptyType

/-- Opaque handle to the native elaboration state (slang `Compilation` and
`NetlistContext`); Lean never inspects it. -/
def SvContext : Type := SvContextPointed.type

instance : Nonempty SvContext := SvContextPointed.property

/-- A width-indexed value produced by evaluating an expression. -/
structure ExprValue where
  width : Nat
  value : Value width

/-- Prints the width and the expression (see `Grounding.Rtl.Repr`). -/
instance : Repr ExprValue where
  reprPrec v _ := s!"{v.width}-bit " ++ repr v.value

/-- An elaborated design: the emitted netlist plus a handle that can evaluate
expressions in the scope of the top module. -/
structure Elaborated where
  netlist : Netlist
  context : SvContext

/-- Evaluate SystemVerilog expression text `expr` in the top module's scope. Only
intermediate expression nets are created; no signal or assignment is added. -/
@[extern "grounding_sv_eval"]
opaque evalExprBuilt (context : @& SvContext) (expr : String) :
    IO (Except String BuiltValue)

/-- Evaluate a SystemVerilog expression in the top module's scope. -/
def Elaborated.eval (e : Elaborated) (expr : String) :
    IO (Except String ExprValue) := do
  match ← evalExprBuilt e.context expr with
  | .error msg => pure (.error msg)
  | .ok value => pure (.ok ⟨value.width, value.value⟩)

/-- Elaborate SystemVerilog `source` (top module `top`, or the only one if `top` is
empty) into an RTL netlist. Diagnostics go to stderr; on failure the error message
is returned. -/
@[extern "grounding_read_sv"]
opaque readSv (source : String) (top : String) : IO (Except String Elaborated)

/-- Elaborate a design given slang command-line arguments (source files, `-f`/`-F`
file lists, `+incdir+`, `-D`, `--top`, …). -/
@[extern "grounding_read_sv_args"]
opaque readSvArgs (args : Array String) : IO (Except String Elaborated)

end Grounding
