-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Rail-level (mux-chain) encoding of `Transition`.

`Transition`/`Register.nextValue` are the specification. This file gives an
equivalent mux-chain form (`Netlist.TransitionMux`/`nextValueMux`) and its rail form
(`Netlist.TransitionRail`), which `bv_dual_rail` translates directly to dual-rail
formulas (`Netlist.Transition.iff_rail`).
-/

import Grounding.Rtl.Transition
import Grounding.Tactic.DualRail.Ev

namespace Grounding.Rtl
open Grounding.Rtl.Rail

namespace Register

/-- First active asynchronous load in `als` under `V'`, else `fallback`.
The first load is outermost, so priority order is preserved. -/
def aloadValue (V V' : Valuation) : List (AsyncLoad width) → TritVec width → TritVec width
  | [], fallback => fallback
  | al :: rest, fallback =>
      TritVec.mux (Trit.ofBool (al.isActive V')) (V'.eval al.value)
        (aloadValue V V' rest fallback)

/-- The clock/async fallback of `nextValueMux`, before the async-load chain. -/
def fallbackConst (V V' : Valuation) (r : Register width) : TritVec width :=
  TritVec.mux (Trit.ofBool (r.isClockX V V')) (TritVec.undef width)
    (TritVec.mux (Trit.ofBool (r.isClockEdge V V')) (V.eval r.d) (V.eval r.q))

/-- Mux form of `nextValue`. -/
def nextValueMux (V V' : Valuation) (r : Register width) : TritVec width :=
  aloadValue V V' r.aloads (fallbackConst V V' r)

theorem aloadValue_eq_asyncValue (V V' : Valuation) :
    ∀ (als : List (AsyncLoad width)) (fallback : TritVec width),
      aloadValue V V' als fallback =
        match als.find? (fun al => al.isActive V') with
        | some al => V'.eval al.value
        | none => fallback
  | [], _ => rfl
  | al :: rest, fallback => by
      rw [aloadValue, List.find?_cons]
      by_cases h : al.isActive V' = true
      · simp [h]
      · simp [h, aloadValue_eq_asyncValue V V' rest fallback]

theorem nextValue_eq_mux (V V' : Valuation) (r : Register width) :
    r.nextValue V V' = r.nextValueMux V V' := by
  unfold nextValue nextValueMux asyncValue fallbackConst
  rw [aloadValue_eq_asyncValue]
  cases h : r.aloads.find? (fun al => al.isActive V') <;>
    simp [TritVec.mux_ofBool]

/-! ### Rail-level encoding: `nextRails` is `nextValue` on `maskOf`/`valOf`. -/

theorem bitvec1_eq_zero (x : BitVec 1) (h : x.getLsbD 0 = false) : x = 0#1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  simpa [hi0, h]

theorem bitvec1_eq_one (x : BitVec 1) (h : x.getLsbD 0 = true) : x = 1#1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  simp [hi0, h]

@[reducible] def activeRail (V : Valuation) (al : AsyncLoad width) : Bool :=
  (Rail.Ev.maskOf (V.eval al.trigger) == 0#1) &&
    (Rail.Ev.valOf (V.eval al.trigger) == (if al.polarity then 1#1 else 0#1))

theorem activeRail_eq (V : Valuation) (al : AsyncLoad width) :
    activeRail V al = al.isActive V := by
  unfold activeRail AsyncLoad.isActive
  have h := Rail.bit0 (Rail.Ev.rail_self (V.eval al.trigger))
  cases hb : (Rail.Ev.maskOf (V.eval al.trigger)).getLsbD 0 <;>
    cases hv : (Rail.Ev.valOf (V.eval al.trigger)).getLsbD 0 <;>
    cases hp : al.polarity <;>
    simp [h.1, hb, hv, bitvec1_eq_zero, bitvec1_eq_one, Rail.trit, Trit.ofBool,
      BitVec.getLsbD_eq_getElem]

@[reducible] def clockXRail (V V' : Valuation) (r : Register width) : Bool :=
  (Rail.Ev.maskOf (V.eval r.clk) != 0#1) ||
    (Rail.Ev.maskOf (V'.eval r.clk) != 0#1)

theorem clockXRail_eq (V V' : Valuation) (r : Register width) :
    clockXRail V V' r = r.isClockX V V' := by
  unfold clockXRail Register.isClockX
  have ho := Rail.bit0 (Rail.Ev.rail_self (V.eval r.clk))
  have hn := Rail.bit0 (Rail.Ev.rail_self (V'.eval r.clk))
  cases ho1 : (Rail.Ev.maskOf (V.eval r.clk)).getLsbD 0 <;>
    cases hn1 : (Rail.Ev.maskOf (V'.eval r.clk)).getLsbD 0 <;>
    simp [ho.1, hn.1, ho1, hn1, bitvec1_eq_zero, bitvec1_eq_one, Rail.trit]

@[reducible] def clockEdgeRail (V V' : Valuation) (r : Register width) : Bool :=
  let xo := Rail.Ev.maskOf (V.eval r.clk)
  let xn := Rail.Ev.maskOf (V'.eval r.clk)
  let vo := Rail.Ev.valOf (V.eval r.clk)
  let vn := Rail.Ev.valOf (V'.eval r.clk)
  if r.clkPolarity then
    (xo == 0#1) && (xn == 0#1) && (vo == 0#1) && (vn == 1#1)
  else
    (xo == 0#1) && (xn == 0#1) && (vo == 1#1) && (vn == 0#1)

theorem clockEdgeRail_eq (V V' : Valuation) (r : Register width) :
    clockEdgeRail V V' r = r.isClockEdge V V' := by
  unfold clockEdgeRail Register.isClockEdge
  have ho := Rail.bit0 (Rail.Ev.rail_self (V.eval r.clk))
  have hn := Rail.bit0 (Rail.Ev.rail_self (V'.eval r.clk))
  cases hp : r.clkPolarity <;>
    cases xo : (Rail.Ev.maskOf (V.eval r.clk)).getLsbD 0 <;>
    cases xn : (Rail.Ev.maskOf (V'.eval r.clk)).getLsbD 0 <;>
    cases vo : (Rail.Ev.valOf (V.eval r.clk)).getLsbD 0 <;>
    cases vn : (Rail.Ev.valOf (V'.eval r.clk)).getLsbD 0 <;>
    simp [xo, xn, vo, vn, ho.1, hn.1, bitvec1_eq_zero, bitvec1_eq_one,
      Rail.trit, Trit.ofBool, beq_iff_eq]

@[reducible] def aloadMask (V V' : Valuation) :
    List (AsyncLoad width) → BitVec width → BitVec width
  | [], fallback => fallback
  | al :: rest, fallback =>
      if activeRail V' al then Rail.Ev.maskOf (V'.eval al.value)
      else aloadMask V V' rest fallback

@[reducible] def aloadVal (V V' : Valuation) :
    List (AsyncLoad width) → BitVec width → BitVec width
  | [], fallback => fallback
  | al :: rest, fallback =>
      if activeRail V' al then Rail.Ev.valOf (V'.eval al.value)
      else aloadVal V V' rest fallback

@[reducible] def aloadRails (V V' : Valuation) (als : List (AsyncLoad width))
    (fallback : BitVec width × BitVec width) : BitVec width × BitVec width :=
  (aloadMask V V' als fallback.1, aloadVal V V' als fallback.2)

@[reducible] def fallbackMask (V V' : Valuation) (r : Register width) : BitVec width :=
  if clockXRail V V' r then BitVec.allOnes width
  else if clockEdgeRail V V' r then Rail.Ev.maskOf (V.eval r.d)
  else Rail.Ev.maskOf (V.eval r.q)

@[reducible] def fallbackVal (V V' : Valuation) (r : Register width) : BitVec width :=
  if clockXRail V V' r then 0#width
  else if clockEdgeRail V V' r then Rail.Ev.valOf (V.eval r.d)
  else Rail.Ev.valOf (V.eval r.q)

@[reducible] def fallbackRails (V V' : Valuation) (r : Register width) : BitVec width × BitVec width :=
  (fallbackMask V V' r, fallbackVal V V' r)

@[reducible] def nextRails (V V' : Valuation) (r : Register width) : BitVec width × BitVec width :=
  aloadRails V V' r.aloads (fallbackRails V V' r)

theorem mux_bool_rails {w : Nat} (cond : Bool) (a b : TritVec w)
    {xa va xb vb : BitVec w} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail.Ev.maskOf (TritVec.mux (Trit.ofBool cond) a b) = (if cond then xa else xb) ∧
    Rail.Ev.valOf (TritVec.mux (Trit.ofBool cond) a b) = (if cond then va else vb) := by
  have hm := Rail.mux (s := Trit.ofBool cond) (xs := false) (vs := cond) (by rfl)
    (by intro h; cases h) ha hb
  exact Rail.Ev.rail_unique (Rail.Ev.rail_self _) (by simpa using hm)

theorem undef_rails (w : Nat) :
    Rail.Ev.maskOf (TritVec.undef w) = BitVec.allOnes w ∧
    Rail.Ev.valOf (TritVec.undef w) = 0#w :=
  Rail.Ev.rail_unique (Rail.Ev.rail_self _) (Rail.undef w)

theorem rails_fallback (V V' : Valuation) (r : Register width) :
    Rail.Ev.maskOf (fallbackConst V V' r) = (fallbackRails V V' r).1 ∧
    Rail.Ev.valOf (fallbackConst V V' r) = (fallbackRails V V' r).2 := by
  unfold fallbackConst fallbackRails fallbackMask fallbackVal
  rw [← clockXRail_eq, ← clockEdgeRail_eq]
  have hd := Rail.Ev.rail_self (V.eval r.d)
  have hq := Rail.Ev.rail_self (V.eval r.q)
  have hedge := mux_bool_rails (clockEdgeRail V V' r) (V.eval r.d) (V.eval r.q) hd hq
  have hedge' : Rail (TritVec.mux (Trit.ofBool (clockEdgeRail V V' r)) (V.eval r.d) (V.eval r.q))
      (if clockEdgeRail V V' r then Rail.Ev.maskOf (V.eval r.d) else Rail.Ev.maskOf (V.eval r.q))
      (if clockEdgeRail V V' r then Rail.Ev.valOf (V.eval r.d) else Rail.Ev.valOf (V.eval r.q)) :=
    Rail.Ev.rail_of_self_eq hedge
  have hu := undef_rails width
  simpa using mux_bool_rails (clockXRail V V' r) (TritVec.undef width)
    (TritVec.mux (Trit.ofBool (clockEdgeRail V V' r)) (V.eval r.d) (V.eval r.q))
    (Rail.Ev.rail_of_self_eq hu) hedge'

theorem rails_aloadValue (V V' : Valuation) :
    ∀ (als : List (AsyncLoad width)) (fallback : TritVec width)
      {fx fv : BitVec width}, Rail fallback fx fv →
      Rail.Ev.maskOf (aloadValue V V' als fallback) =
        (aloadRails V V' als (fx, fv)).1 ∧
      Rail.Ev.valOf (aloadValue V V' als fallback) =
        (aloadRails V V' als (fx, fv)).2
  | [], fallback, fx, fv, hfallback => Rail.Ev.rail_unique (Rail.Ev.rail_self _) hfallback
  | al :: rest, fallback, fx, fv, hfallback => by
      unfold aloadValue aloadRails aloadMask aloadVal
      rw [← activeRail_eq]
      have hval := Rail.Ev.rail_self (V'.eval al.value)
      have hrest := rails_aloadValue V V' rest fallback hfallback
      have hrest' : Rail (aloadValue V V' rest fallback)
          (aloadRails V V' rest (fx, fv)).1 (aloadRails V V' rest (fx, fv)).2 :=
        Rail.Ev.rail_of_self_eq hrest
      simpa [aloadRails] using mux_bool_rails (activeRail V' al) (V'.eval al.value)
        (aloadValue V V' rest fallback) hval hrest'

theorem rails_nextValueMux (V V' : Valuation) (r : Register width) :
    Rail.Ev.maskOf (r.nextValueMux V V') = (r.nextRails V V').1 ∧
    Rail.Ev.valOf (r.nextValueMux V V') = (r.nextRails V V').2 := by
  unfold nextValueMux nextRails
  exact rails_aloadValue V V' r.aloads (fallbackConst V V' r)
    (Rail.Ev.rail_of_self_eq (rails_fallback V V' r))

/-- The register part of `isConsistent` as rail equations: an active asynchronous
load forces `q`, and `aloadValue` with `q` as fallback captures exactly that. -/
theorem register_reset_rails {V : Valuation} {r : Register width}
    (hreg : ∀ v, r.asyncValue V = some v → V.eval r.q = v) :
    Rail.Ev.maskOf (V.eval r.q) = (aloadRails V V r.aloads
      (Rail.Ev.maskOf (V.eval r.q), Rail.Ev.valOf (V.eval r.q))).1 ∧
    Rail.Ev.valOf (V.eval r.q) = (aloadRails V V r.aloads
      (Rail.Ev.maskOf (V.eval r.q), Rail.Ev.valOf (V.eval r.q))).2 := by
  have hreset : V.eval r.q = aloadValue V V r.aloads (V.eval r.q) := by
    rw [aloadValue_eq_asyncValue]
    cases h : r.aloads.find? (fun al => al.isActive V) with
    | none => rfl
    | some al => exact hreg _ (by simp [asyncValue, h])
  have hself := Rail.Ev.rail_self (V.eval r.q)
  have hrails := rails_aloadValue V V r.aloads (V.eval r.q) hself
  exact Rail.Ev.rail_unique hself (Rail.of_eq hreset.symm (Rail.Ev.rail_of_self_eq hrails))

/-- The rail-level transition fact for one register. -/
@[reducible] def railHolds (V V' : Valuation) (r : Register width) : Prop :=
  Rail.Ev.maskOf (V'.eval r.q) = (r.nextRails V V').1 ∧
  Rail.Ev.valOf (V'.eval r.q) = (r.nextRails V V').2

end Register

/-- Rail-level transition facts over a literal register list. -/
@[reducible] def RegistersRail (V V' : Valuation) : List (Σ width, Register width) → Prop
  | [] => True
  | r :: rs => r.2.railHolds V V' ∧ RegistersRail V V' rs

/-- Rail-level form of `Transition`, directly encodable by `bv_dual_rail`. -/
@[reducible] def Netlist.TransitionRail (n : Netlist) (V V' : Valuation) : Prop :=
  RegistersRail V V' n.registers

theorem RegistersRail_iff (V V' : Valuation) (rs : List (Σ width, Register width)) :
    (∀ r ∈ rs, r.2.railHolds V V') ↔ RegistersRail V V' rs := by
  induction rs with
  | nil => simp [RegistersRail]
  | cons r rs ih =>
      simp only [List.mem_cons, forall_eq_or_imp, RegistersRail, ih]

/-- Mux-chain form of `Transition`, used by `bv_dual_rail` for encoding.
Equivalent to `Netlist.Transition` by `Netlist.Transition.iff_mux`. -/
def Netlist.TransitionMux (n : Netlist) (V V' : Valuation) : Prop :=
  ∀ (r : Σ width, Register width), r ∈ n.registers →
    V'.eval r.2.q = r.2.nextValueMux V V'

theorem Netlist.Transition.iff_mux {n : Netlist} {V V' : Valuation} :
    n.Transition V V' ↔ n.TransitionMux V V' := by
  unfold Netlist.Transition Netlist.TransitionMux
  simp only [Register.nextValue_eq_mux]

theorem register_eq_iff_rail (V V' : Valuation) (r : Register width) :
    V'.eval r.q = r.nextValueMux V V' ↔ r.railHolds V V' := by
  constructor
  · intro h
    unfold Register.railHolds
    rw [h]
    exact Register.rails_nextValueMux V V' r
  · intro hh
    have hr' := Register.rails_nextValueMux V V' r
    unfold Register.railHolds at hh
    exact (Rail.Ev.eq_iff_rails (Rail.Ev.rail_self (V'.eval r.q))
      (Rail.Ev.rail_self (r.nextValueMux V V'))).2
      ⟨hh.1.trans hr'.1.symm, hh.2.trans hr'.2.symm⟩

theorem Netlist.TransitionMux.iff_rail {n : Netlist} {V V' : Valuation} :
    n.TransitionMux V V' ↔ n.TransitionRail V V' := by
  unfold Netlist.TransitionMux Netlist.TransitionRail
  constructor
  · intro h
    exact (RegistersRail_iff V V' n.registers).mp
      (fun r hr => (register_eq_iff_rail V V' r.2).mp (h r hr))
  · intro h r hr
    exact (register_eq_iff_rail V V' r.2).mpr
      ((RegistersRail_iff V V' n.registers).mpr h r hr)

/-- The spec `Transition` is equivalent to the rail-level structure. -/
theorem Netlist.Transition.iff_rail {n : Netlist} {V V' : Valuation} :
    n.Transition V V' ↔ n.TransitionRail V V' :=
  Netlist.Transition.iff_mux.trans Netlist.TransitionMux.iff_rail

end Grounding.Rtl
