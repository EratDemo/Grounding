/-
Lean bindings for the native SystemVerilog frontend (`native/driver.cpp`).

The native side exports `grounding_read_sv`, `grounding_read_sv_args`, and
`grounding_sv_eval`. The Lean side exports the `grounding_builder_*` functions
in `Grounding.Rtl.Builder`.
-/

import Grounding.Rtl.Builder

namespace Grounding.Rtl

/-- Opaque handle to the native elaboration state (`grounding::SvState`). -/
opaque SvContextType : NonemptyType
def SvContext : Type := SvContextType.type
instance : Nonempty SvContext := SvContextType.property

/-- A netlist together with the native state needed for expression evaluation. -/
structure Elaborated where
  netlist : Netlist
  context : SvContext

/-- Parse and elaborate `source`, optionally selecting `top`. -/
@[extern "grounding_read_sv"]
opaque readSv (source top : String) : IO (Except String Elaborated)

/-- Parse and elaborate using slang command-line arguments. -/
@[extern "grounding_read_sv_args"]
opaque readSvArgs (args : Array String) : IO (Except String Elaborated)

/-- Evaluate `expr` in the elaborated top module. -/
@[extern "grounding_sv_eval"]
opaque evalExprBuilt (context : @& SvContext) (expr : String) :
    IO (Except String BuiltValue)

end Grounding.Rtl
