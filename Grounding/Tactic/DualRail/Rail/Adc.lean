-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Dual-rail encoding of `adc`.
-/

import Grounding.Tactic.DualRail.Rail.Basic
import Grounding.Tactic.DualRail.KitchenSink

namespace Grounding.Rtl.Rail

open TritVec

/-! ### Addition -/

attribute [local simp] Trit.beq_eq_decide

/-- "Some bit `j ≤ i` of the operands is X." -/
def xBelow (as bs : List Trit) (i : Nat) : Prop :=
  ∃ j, j ≤ i ∧ (as.getD j .zero = .x ∨ bs.getD j .zero = .x)

theorem xBelow_cons (a b : Trit) (as bs : List Trit) (i : Nat) :
    xBelow (a :: as) (b :: bs) (i + 1) ↔ (a = .x ∨ b = .x) ∨ xBelow as bs i := by
  constructor
  · rintro ⟨j, hj, h⟩
    cases j with
    | zero => exact Or.inl (by simpa using h)
    | succ j => exact Or.inr ⟨j, by omega, by simpa using h⟩
  · rintro (h | ⟨j, hj, h⟩)
    · exact ⟨0, by omega, by simpa using h⟩
    · exact ⟨j + 1, by omega, by simpa using h⟩

theorem xBelow_zero (a b : Trit) (as bs : List Trit) :
    xBelow (a :: as) (b :: bs) 0 ↔ (a = .x ∨ b = .x) := by
  constructor
  · rintro ⟨j, hj, h⟩; obtain rfl : j = 0 := by omega
    simpa using h
  · intro h; exact ⟨0, Nat.le_refl _, by simpa using h⟩

theorem xBelow_nil (i : Nat) : ¬ xBelow [] [] i := by
  rintro ⟨j, _, h⟩; simp at h

attribute [local instance] Classical.propDecidable in
/-- Bit `i` of the adc result list is X iff the carry-in or some operand bit
`j ≤ i` is X; otherwise it is bit `i` of the natural sum. -/
theorem adcBits_bit : ∀ (as bs : List Trit) (c : Trit) (_hl : as.length = bs.length) (i : Nat)
    (_hi : i < as.length + 1),
    ((adcBits as bs c).1 ++ [(adcBits as bs c).2]).getD i .zero =
      if c = .x ∨ xBelow as bs i then .x
      else Trit.ofBool ((natOf as + natOf bs + (c == .one).toNat).testBit i)
  | [], [], c, _, i, hi => by
    obtain rfl : i = 0 := by simpa using hi
    have := xBelow_nil 0
    cases c <;> simp [adcBits, Trit.ofBool, this]
  | a :: as, b :: bs, c, hl, i, hi => by
    rw [TritVec.adcBits_cons]
    have hl' : as.length = bs.length := by simpa using hl
    cases i with
    | zero =>
      simp only [List.cons_append, List.getD_cons_zero, natOf_cons, xBelow_zero]
      generalize natOf as = A
      generalize natOf bs = B
      cases a <;> cases b <;> cases c <;> simp [Trit.sumT, Trit.ofBool, Trit.not, Nat.testBit_zero] <;> omega
    | succ i =>
      simp only [List.cons_append, List.getD_cons_succ]
      rw [adcBits_bit as bs _ hl' i (by simpa using hi), xBelow_cons, natOf_cons, natOf_cons]
      generalize natOf as = A
      generalize natOf bs = B
      generalize xBelow as bs i = P
      by_cases hP : P
      · simp [hP]
      · simp only [hP, or_false]
        rw [← Nat.testBit_div_two]
        rcases a <;> rcases b <;> rcases c <;> simp [Trit.carT, Trit.ofBool]
        all_goals first
          | rfl
          | (rw [show ∀ k, (A * 2 + B * 2 + k) / 2 = A + B + k / 2 from fun k => by omega]; rfl)
          | (simp only [show (A * 2 + B * 2) / 2 = A + B by omega,
                show (A * 2 + (B * 2 + 1)) / 2 = A + B by omega,
                show (A * 2 + (B * 2 + 1) + 1) / 2 = A + B + 1 by omega,
                show (A * 2 + 1 + B * 2) / 2 = A + B by omega,
                show (A * 2 + 1 + B * 2 + 1) / 2 = A + B + 1 by omega,
                show (A * 2 + 1 + (B * 2 + 1)) / 2 = A + B + 1 by omega,
                show (A * 2 + 1 + (B * 2 + 1) + 1) / 2 = A + B + 1 by omega])
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl


/-- Below the first X of a rail, the trits are the value bits. -/
theorem natOf_testBit_of_rail {c : TritVec w} {x v : BitVec w} (h : Rail c x v) (j : Nat)
    (hj : c.bits.toList.getD j .zero ≠ .x) : (natOf c.bits.toList).testBit j = v.getLsbD j := by
  rw [testBit_natOf]
  by_cases hjw : j < w
  · rw [getD_of_lt _ (by simpa using hjw)] at hj ⊢
    simp only [Vector.getElem_toList] at hj ⊢
    rw [rail_bit h j hjw] at hj ⊢
    cases hx : x[j] <;> cases hv : v[j] <;> simp_all [trit]
  · rw [getD_of_ge _ (by simpa using Nat.le_of_not_lt hjw)]
    simp [BitVec.getLsbD_of_ge v j (Nat.le_of_not_lt hjw)]

/-- The adder on rails. With `m` the X positions of the operands (bit 0 also
when the carry-in is X), every result bit at or above the lowest X is X; the
other bits are those of the two-valued sum of the value rails. -/
theorem adc {a b : TritVec w} {c : Trit} {xa va xb vb : BitVec w} {xc vc : Bool}
    (ha : Rail a xa va) (hb : Rail b xb vb) (hc : c = trit xc vc) (hnc : xc = true → vc = false) :
    Rail (a.adc b c)
      ((xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool xc).setWidth (w + 1)) |||
        -(xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool xc).setWidth (w + 1)))
      ((va.setWidth (w + 1) + vb.setWidth (w + 1) + (BitVec.ofBool vc).setWidth (w + 1)) &&&
        ~~~((xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool xc).setWidth (w + 1)) |||
        -(xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool xc).setWidth (w + 1)))) := by
  generalize hm : xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool xc).setWidth (w + 1) = m
  refine mk (fun i hi => ?_) (fun i hi hx => by simp [BitVec.getElem_and, hx])
  have hbit : (a.adc b c).bits[i] = ((adcBits a.bits.toList b.bits.toList c).1 ++
      [(adcBits a.bits.toList b.bits.toList c).2]).getD i .zero := by
    rw [← TritVec.adc_toList, getD_of_lt _ (by simpa using hi), Vector.getElem_toList]
  rw [hbit, adcBits_bit _ _ _ (by simp) i (by simpa using hi)]
  -- trits of the operands below `i` are X iff the mask bits are
  have hxa : ∀ j, a.bits.toList.getD j .zero = .x ↔ xa.getLsbD j = true := by
    intro j
    by_cases hj : j < w
    · rw [getD_of_lt _ (by simpa using hj), BitVec.getLsbD_eq_getElem hj]
      simp only [Vector.getElem_toList, rail_bit ha j hj]
      cases xa[j] <;> simp [trit]
    · rw [getD_of_ge _ (by simpa using Nat.le_of_not_lt hj),
        BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hj)]
      simp
  have hxb : ∀ j, b.bits.toList.getD j .zero = .x ↔ xb.getLsbD j = true := by
    intro j
    by_cases hj : j < w
    · rw [getD_of_lt _ (by simpa using hj), BitVec.getLsbD_eq_getElem hj]
      simp only [Vector.getElem_toList, rail_bit hb j hj]
      cases xb[j] <;> simp [trit]
    · rw [getD_of_ge _ (by simpa using Nat.le_of_not_lt hj),
        BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hj)]
      simp
  have hcx : c = .x ↔ xc = true := by subst hc; cases xc <;> simp [trit]
  have hmj : ∀ j, j < w + 1 → (m.getLsbD j = true ↔
      xa.getLsbD j = true ∨ xb.getLsbD j = true ∨ (j = 0 ∧ xc = true)) := by
    intro j hj
    subst hm
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool, hj,
      decide_true, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | h) | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · rintro (h | h | ⟨h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h1, h2⟩
  have hX : (c = .x ∨ xBelow a.bits.toList b.bits.toList i) ↔
      ∃ j, j ≤ i ∧ m.getLsbD j = true := by
    rw [hcx]
    constructor
    · rintro (h | ⟨j, hj, h | h⟩)
      · exact ⟨0, Nat.zero_le _, (hmj 0 (by omega)).2 (Or.inr (Or.inr ⟨rfl, h⟩))⟩
      · exact ⟨j, hj, (hmj j (by omega)).2 (Or.inl ((hxa j).1 h))⟩
      · exact ⟨j, hj, (hmj j (by omega)).2 (Or.inr (Or.inl ((hxb j).1 h)))⟩
    · rintro ⟨j, hj, h⟩
      rcases (hmj j (by omega)).1 h with h' | h' | ⟨_, h'⟩
      · exact Or.inr ⟨j, hj, Or.inl ((hxa j).2 h')⟩
      · exact Or.inr ⟨j, hj, Or.inr ((hxb j).2 h')⟩
      · exact Or.inl h'
  have hmx := prefixOr_bit m i hi
  by_cases hXi : c = .x ∨ xBelow a.bits.toList b.bits.toList i
  · have : (m ||| -m)[i] = true := by rw [hmx]; exact decide_eq_true (hX.1 hXi)
    simp [hXi, this, trit]
  · have hmi : (m ||| -m)[i] = false := by
      rw [hmx]; exact decide_eq_false (fun h => hXi (hX.2 h))
    simp only [hXi, ite_false, hmi, trit, Bool.false_eq_true, ite_false, BitVec.getElem_and,
      BitVec.getElem_not, Bool.not_false, Bool.and_true]
    congr 1
    -- value side: the defined low bits agree with the value rails
    have hc' : xc = false := by
      cases h : xc
      · rfl
      · exact absurd (Or.inl (hcx.2 h)) hXi
    have hlow : ∀ j, j ≤ i → a.bits.toList.getD j .zero ≠ .x ∧ b.bits.toList.getD j .zero ≠ .x :=
      fun j hj => ⟨fun h => hXi (Or.inr ⟨j, hj, Or.inl h⟩), fun h => hXi (Or.inr ⟨j, hj, Or.inr h⟩)⟩
    have hA := mod_eq_of_testBit i (fun j hj => natOf_testBit_of_rail ha j (hlow j hj).1)
    have hB := mod_eq_of_testBit i (fun j hj => natOf_testBit_of_rail hb j (hlow j hj).2)
    have hcv : (c == .one).toNat = vc.toNat := by subst hc; subst hc'; cases vc <;> rfl
    -- the natural sum's bit i, with the operands replaced by the value rails
    have hnat : (natOf a.bits.toList + natOf b.bits.toList + (c == .one).toNat).testBit i =
        (va.toNat + vb.toNat + vc.toNat).testBit i := by
      rw [hcv, Nat.add_assoc, Nat.add_assoc]
      apply testBit_add_congr i hA
      rw [Nat.add_mod, hB, ← Nat.add_mod]
    rw [hnat]
    -- the BitVec sum at bit i < w + 1 is the natural sum's bit (no overflow)
    rw [← BitVec.getLsbD_eq_getElem hi, ← BitVec.testBit_toNat]
    have hva := va.isLt
    have hvb := vb.isLt
    have hvc : vc.toNat < 2 := by cases vc <;> decide
    have hpow : 2 ^ w * 2 = 2 ^ (w + 1) := (Nat.pow_succ 2 w).symm
    have hw1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    rw [Nat.mod_eq_of_lt (a := va.toNat) (by omega), Nat.mod_eq_of_lt (a := vb.toNat) (by omega),
      Nat.mod_eq_of_lt (a := vc.toNat) (by omega), Nat.mod_eq_of_lt (a := va.toNat + vb.toNat) (by omega),
      Nat.mod_eq_of_lt (a := va.toNat + vb.toNat + vc.toNat) (by omega)]

end Grounding.Rtl.Rail
