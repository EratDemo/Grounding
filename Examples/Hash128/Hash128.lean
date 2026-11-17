-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Grounding
import Grounding.Tactic.DualRail
import Std.Tactic.BVDecide

open Grounding.Rtl

sv_design hash128
  "Examples/Hash128/hash128.sv"

namespace hash128

set_option maxRecDepth 20000

example {V : Valuation} (h : V.isConsistent hash128)
    (h2 : V.eval (sv_expr% "x") = TritVec.ofBV 0#32) :
    V.eval (sv_expr% "acc") = TritVec.ofBV 32#32 := by
  bv_dual_rail
  bv_decide
