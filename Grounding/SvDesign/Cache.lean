-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
State for `sv_design`: live native handles (per process) and the persistent record
of embedded designs. A separate module because `initialize` declarations cannot be
evaluated in the module that declares them.
-/

import Lean.Elab.Command
import Lean.Elab.Term
import Grounding.Sv

namespace Grounding.SvDesign

open Lean

/-- What `sv_design` records about an embedded design (persisted in .olean). -/
structure DesignInfo where
  /-- The constant holding the embedded netlist. -/
  decl : Name
  /-- slang arguments used to elaborate it (re-run to recover the handle). -/
  args : Array String
  /-- `Netlist.fingerprint` of the embedded netlist. -/
  fingerprint : UInt64
  deriving Inhabited

/-- Embedded designs, keyed by `decl`. -/
initialize designExt : SimplePersistentEnvExtension DesignInfo (NameMap DesignInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m d => m.insert d.decl d
    addImportedFn := fun as => as.foldl (fun m ds => ds.foldl (fun m d => m.insert d.decl d) m) {}
  }

/-- Live handles of designs elaborated in this process (keyed by `decl`). The
handle is not persisted: in another process the design is re-elaborated. -/
initialize handleCache : IO.Ref (NameMap Elaborated) ← IO.mkRef {}

def findDesign? (env : Environment) (decl : Name) : Option DesignInfo :=
  (designExt.getState env).find? decl

end Grounding.SvDesign
