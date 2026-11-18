-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Examples.CrossFile.Design
import Grounding.Tactic.DualRail
import Std.Tactic.BVDecide

open Grounding.Rtl

/-! `adder` was embedded by `Examples.CrossFile.Design`, a different module. The
`sv_expr%` terms below need the design's native handle, which is re-created from
the recorded slang arguments and checked against the recorded fingerprint. -/

namespace adder

example {V : Valuation} (h : V.isConsistent adder)
    (ha : V.eval (sv_expr% "a") = TritVec.ofBV 3#8)
    (hb : V.eval (sv_expr% "b") = TritVec.ofBV 4#8) :
    V.eval (sv_expr% "sum") = TritVec.ofBV 7#8 := by
  bv_dual_rail
  bv_decide

example {V : Valuation} (h : V.isConsistent adder)
    (ha : V.eval (sv_expr% adder "a") = TritVec.ofBV 200#8)
    (hb : V.eval (sv_expr% adder "b") = TritVec.ofBV 100#8) :
    V.eval (sv_expr% adder "sum") = TritVec.ofBV 44#8 := by
  bv_dual_rail
  bv_decide

end adder
