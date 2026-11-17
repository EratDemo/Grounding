-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL synchronous transition relation.

`n.Transition V V'` relates the valuation `V` to the valuation `V'` across one
clock step.

Combinational consistency and the environment (inputs and external feedback)
are left to the caller; this predicate describes only the netlist's registers.
-/

import Grounding.Rtl.Valuation

namespace Grounding.Rtl

namespace Register

def clockEdge (V V' : Valuation) (r : Register width) : Prop :=
  if r.clkPolarity then
    (V.eval r.clk).bit0 = Trit.zero ∧ (V'.eval r.clk).bit0 = Trit.one
  else
    (V.eval r.clk).bit0 = Trit.one ∧ (V'.eval r.clk).bit0 = Trit.zero

/-- Boolean form of `clockEdge`. -/
def isClockEdge (V V' : Valuation) (r : Register width) : Bool :=
  if r.clkPolarity then
    (V.eval r.clk).bit0 == Trit.zero && (V'.eval r.clk).bit0 == Trit.one
  else
    (V.eval r.clk).bit0 == Trit.one && (V'.eval r.clk).bit0 == Trit.zero

theorem isClockEdge_iff (V V' : Valuation) (r : Register width) :
    r.isClockEdge V V' = true ↔ r.clockEdge V V' := by
  unfold isClockEdge clockEdge
  cases h : r.clkPolarity <;> simp [Bool.and_eq_true, beq_iff_eq]

/-- Either the old or the new clock level is `X`. -/
def clockX (V V' : Valuation) (r : Register width) : Prop :=
  (V.eval r.clk).bit0 = Trit.x ∨ (V'.eval r.clk).bit0 = Trit.x

/-- Boolean form of `clockX`. -/
def isClockX (V V' : Valuation) (r : Register width) : Bool :=
  (V.eval r.clk).bit0 == Trit.x || (V'.eval r.clk).bit0 == Trit.x

theorem isClockX_iff (V V' : Valuation) (r : Register width) :
    r.isClockX V V' = true ↔ r.clockX V V' := by
  simp [isClockX, clockX, beq_iff_eq]

/-- The value loaded into the register by the step: the first active
asynchronous load in `V'` wins; otherwise an `X` clock level makes `q` all-`X`,
then `d` on a clock edge and `q` without an edge. -/
def nextValue (V V' : Valuation) (r : Register width) : TritVec width :=
  match r.asyncValue V' with
  | some v => v
  | none =>
    if r.isClockX V V' then TritVec.undef width
    else if r.isClockEdge V V' then V.eval r.d else V.eval r.q

end Register

def Netlist.Transition (n : Netlist) (V V' : Valuation) : Prop :=
  ∀ (r : Σ width, Register width), r ∈ n.registers →
    V'.eval r.2.q = r.2.nextValue V V'

end Grounding.Rtl
