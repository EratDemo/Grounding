-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Dual-rail encoding of `eq`, `eqx`, `ult` and `slt`.
-/

import Grounding.Tactic.DualRail.Rail.Basic
import Grounding.Tactic.DualRail.KitchenSink

namespace Grounding.Rtl.Rail

open TritVec

attribute [local simp] Trit.beq_eq_decide

/-! ### Comparisons -/

/-- A one-bit rail for the trit `t`. -/
theorem fromTrit_rail (t : Trit) (x v : Bool) (h : t = trit x v) (hn : x = true → v = false) :
    Rail (fromTrit t) (BitVec.ofBool x) (BitVec.ofBool v) :=
  mk (fun i hi => by
        obtain rfl : i = 0 := by omega
        simp [fromTrit_bits, h])
     (fun i hi hx => by
        obtain rfl : i = 0 := by omega
        simp at hx ⊢; exact hn hx)

/-- `eqBits` on lists of equal length: 0 as soon as defined bits differ at
some position; else X if any position has an X; else 1. Positions are read
with `getD` (in range by the length hypothesis). -/
theorem eqBits_spec : ∀ (as bs : List Trit), as.length = bs.length →
    eqBits as bs =
      if ∃ j, j < as.length ∧ as.getD j .zero ≠ .x ∧ bs.getD j .zero ≠ .x ∧
          as.getD j .zero ≠ bs.getD j .zero then .zero
      else if ∃ j, j < as.length ∧ (as.getD j .zero = .x ∨ bs.getD j .zero = .x) then .x
      else .one
  | [], [], _ => by simp [eqBits]
  | a :: as, b :: bs, hl => by
    have hl' : as.length = bs.length := by simpa using hl
    have hD : (∃ j, j < (a :: as).length ∧ (a :: as).getD j .zero ≠ .x ∧
        (b :: bs).getD j .zero ≠ .x ∧ (a :: as).getD j .zero ≠ (b :: bs).getD j .zero) ↔
        (a ≠ .x ∧ b ≠ .x ∧ a ≠ b) ∨ ∃ j, j < as.length ∧ as.getD j .zero ≠ .x ∧
          bs.getD j .zero ≠ .x ∧ as.getD j .zero ≠ bs.getD j .zero := by
      constructor
      · rintro ⟨j, h1, h⟩
        cases j with
        | zero => exact Or.inl (by simpa using h)
        | succ j => exact Or.inr ⟨j, by simpa using h1, by simpa using h⟩
      · rintro (h | ⟨j, h1, h⟩)
        · exact ⟨0, by simp, by simpa using h⟩
        · exact ⟨j + 1, by simpa using h1, by simpa using h⟩
    have hX : (∃ j, j < (a :: as).length ∧ ((a :: as).getD j .zero = .x ∨
        (b :: bs).getD j .zero = .x)) ↔
        (a = .x ∨ b = .x) ∨ ∃ j, j < as.length ∧ (as.getD j .zero = .x ∨ bs.getD j .zero = .x) := by
      constructor
      · rintro ⟨j, h1, h⟩
        cases j with
        | zero => exact Or.inl (by simpa using h)
        | succ j => exact Or.inr ⟨j, by simpa using h1, by simpa using h⟩
      · rintro (h | ⟨j, h1, h⟩)
        · exact ⟨0, by simp, by simpa using h⟩
        · exact ⟨j + 1, by simpa using h1, by simpa using h⟩
    simp only [hD, hX]
    simp only [eqBits]
    rw [eqBits_spec as bs hl']
    by_cases hd : ∃ j, j < as.length ∧ as.getD j .zero ≠ .x ∧ bs.getD j .zero ≠ .x ∧
      as.getD j .zero ≠ bs.getD j .zero <;>
    by_cases hx : ∃ j, j < as.length ∧ (as.getD j .zero = .x ∨ bs.getD j .zero = .x) <;>
    simp only [hd, hx, ite_true, ite_false, or_true, or_false] <;>
    cases a <;> cases b <;> simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem getD_toList_rail {c : TritVec w} {x v : BitVec w} (h : Rail c x v) (j : Nat) (hj : j < w) :
    c.bits.toList.getD j .zero = trit x[j] v[j] := by
  rw [getD_of_lt _ (by simpa using hj), Vector.getElem_toList, rail_bit h j hj]


theorem eq {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.eq b)
      (BitVec.ofBool (((~~~(xa ||| xb) &&& (va ^^^ vb)) == 0#w) && (xa ||| xb) != 0#w))
      (BitVec.ofBool (((~~~(xa ||| xb) &&& (va ^^^ vb)) == 0#w) && (xa ||| xb) == 0#w)) := by
  apply fromTrit_rail _ _ _ _ (by
    intro h; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [h.2])
  rw [eqBits_spec _ _ (by simp)]
  simp only [Vector.length_toList]
  have hdiff : (∃ j, j < w ∧ a.bits.toList.getD j .zero ≠ .x ∧ b.bits.toList.getD j .zero ≠ .x ∧
      a.bits.toList.getD j .zero ≠ b.bits.toList.getD j .zero) ↔
      (~~~(xa ||| xb) &&& (va ^^^ vb)) ≠ 0#w := by
    constructor
    · rintro ⟨j, hj, h⟩ heq
      have := congrArg (·[j]) heq
      rw [getD_toList_rail ha j hj, getD_toList_rail hb j hj] at h
      simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or, BitVec.getElem_xor,
        BitVec.getElem_zero] at this
      revert h this
      cases xa[j] <;> cases va[j] <;> cases xb[j] <;> cases vb[j] <;> simp [trit]
    · intro hne
      obtain ⟨j, hj, hbit⟩ := exists_bit_of_ne hne
      refine ⟨j, hj, ?_⟩
      rw [getD_toList_rail ha j hj, getD_toList_rail hb j hj]
      simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or, BitVec.getElem_xor] at hbit
      revert hbit
      cases xa[j] <;> cases va[j] <;> cases xb[j] <;> cases vb[j] <;> simp [trit]
  have hx : (∃ j, j < w ∧ (a.bits.toList.getD j .zero = .x ∨ b.bits.toList.getD j .zero = .x)) ↔
      (xa ||| xb) ≠ 0#w := by
    constructor
    · rintro ⟨j, hj, h⟩ heq
      have := congrArg (·[j]) heq
      rw [getD_toList_rail ha j hj, getD_toList_rail hb j hj] at h
      simp only [BitVec.getElem_or, BitVec.getElem_zero] at this
      revert h this
      cases xa[j] <;> cases va[j] <;> cases xb[j] <;> cases vb[j] <;> simp [trit]
    · intro hne
      obtain ⟨j, hj, hbit⟩ := exists_bit_of_ne hne
      refine ⟨j, hj, ?_⟩
      rw [getD_toList_rail ha j hj, getD_toList_rail hb j hj]
      simp only [BitVec.getElem_or] at hbit
      revert hbit
      cases xa[j] <;> cases va[j] <;> cases xb[j] <;> cases vb[j] <;> simp [trit]
  simp only [hdiff, hx]
  by_cases h2 : (xa ||| xb) = 0#w
  · have hd : (~~~(xa ||| xb) &&& (va ^^^ vb)) = (va ^^^ vb) := by rw [h2]; simp
    rw [hd]
    by_cases h1 : va = vb
    · subst h1; simp [h2, trit, Trit.ofBool]
    · have : (va ^^^ vb) ≠ 0#w := fun h => h1 (BitVec.xor_eq_zero_iff.1 h)
      simp [h2, this, trit, Trit.ofBool]
  · by_cases h1 : (~~~(xa ||| xb) &&& (va ^^^ vb)) = 0#w <;> simp [h1, h2, trit, Trit.ofBool]

/-- `eqx` (`===`): equal including X positions. -/
theorem eqx {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.eqx b) 0#1 (BitVec.ofBool (xa == xb && va == vb)) := by
  have hiff : a = b ↔ (xa = xb ∧ va = vb) := by
    constructor
    · rintro rfl
      constructor
      · ext i hi
        have h1 := rail_bit ha i hi
        have h2 := rail_bit hb i hi
        rw [h1] at h2
        have n1 := rail_norm ha i hi
        have n2 := rail_norm hb i hi
        revert h2 n1 n2
        cases xa[i] <;> cases va[i] <;> cases xb[i] <;> cases vb[i] <;> simp [trit]
      · ext i hi
        have h1 := rail_bit ha i hi
        have h2 := rail_bit hb i hi
        rw [h1] at h2
        have n1 := rail_norm ha i hi
        have n2 := rail_norm hb i hi
        revert h2 n1 n2
        cases xa[i] <;> cases va[i] <;> cases xb[i] <;> cases vb[i] <;> simp [trit]
    · rintro ⟨rfl, rfl⟩
      exact ext_nat fun i hi => by rw [rail_bit ha i hi, rail_bit hb i hi]
  apply fromTrit_rail _ false _ _ (by simp)
  by_cases h : a = b
  · have := hiff.1 h
    simp [h, this, trit]
  · have : ¬(xa = xb ∧ va = vb) := fun h' => h (hiff.2 h')
    simp only [h, ite_false, trit, Bool.false_eq_true]
    simp only [not_and] at this
    by_cases hx : xa = xb
    · have hv := this hx
      simp [hx, hv, Trit.ofBool]
    · simp [hx, Trit.ofBool]

theorem ult {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.ult b) (BitVec.ofBool (anyX xa xb)) (BitVec.ofBool (!anyX xa xb && va.ult vb)) := by
  rw [ult_spec, hasUndef_iff ha, hasUndef_iff hb]
  by_cases h : (xa != 0#w || xb != 0#w) = true
  · simp only [h, ite_true]
    exact fromTrit_rail _ _ _ (by simp [trit]) (by simp)
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and]
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    rw [tieDownX_eq ha h.1, tieDownX_eq hb h.2, ← fromTrit_ofBool]
    exact fromTrit_rail _ _ _ (by simp [trit, BitVec.ult_eq_decide, BitVec.lt_def]) (by simp)

theorem slt {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.slt b) (BitVec.ofBool (anyX xa xb)) (BitVec.ofBool (!anyX xa xb && va.slt vb)) := by
  rw [slt_spec, hasUndef_iff ha, hasUndef_iff hb]
  by_cases h : (xa != 0#w || xb != 0#w) = true
  · simp only [h, ite_true]
    exact fromTrit_rail _ _ _ (by simp [trit]) (by simp)
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and]
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    rw [tieDownX_eq ha h.1, tieDownX_eq hb h.2, ← fromTrit_ofBool]
    exact fromTrit_rail _ _ _ (by simp [trit]) (by simp)

end Grounding.Rtl.Rail
