-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Small `List`/`Nat`/`BitVec` facts used by the dual-rail proofs that have no better home.
Nothing here mentions `Rail`.
-/

import Init.Data.BitVec.Lemmas

namespace Grounding.Rtl.Rail

/-- Bit `i` of `m ||| -m` is set iff some bit `j ≤ i` of `m` is set. -/
theorem prefixOr_bit (m : BitVec w) (i : Nat) (hi : i < w) :
    (m ||| -m)[i] = decide (∃ j, j ≤ i ∧ m.getLsbD j = true) := by
  rw [BitVec.getElem_or, BitVec.getElem_neg]
  by_cases h : m[i] = true
  · simp only [h, Bool.true_or, Bool.true_bne]
    exact (decide_eq_true ⟨i, Nat.le_refl _, by rw [BitVec.getLsbD_eq_getElem hi]; exact h⟩).symm
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_or, Bool.false_bne, decide_eq_decide]
    constructor
    · rintro ⟨j, hj, hm⟩; exact ⟨j, by omega, hm⟩
    · rintro ⟨j, hj, hm⟩
      refine ⟨j, ?_, hm⟩
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hj
      · rw [BitVec.getLsbD_eq_getElem hi, h] at hm; cases hm

theorem getD_of_lt {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_of_ge {l : List α} {i : Nat} (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- Bit `i` of a sum depends only on the summands modulo `2^(i+1)`. -/
theorem testBit_add_congr {a b a' b' : Nat} (i : Nat) (ha : a % 2 ^ (i + 1) = a' % 2 ^ (i + 1))
    (hb : b % 2 ^ (i + 1) = b' % 2 ^ (i + 1)) : (a + b).testBit i = (a' + b').testBit i := by
  have : (a + b) % 2 ^ (i + 1) = (a' + b') % 2 ^ (i + 1) := by
    rw [Nat.add_mod, ha, hb, ← Nat.add_mod]
  have h1 := Nat.testBit_mod_two_pow (a + b) (i + 1) i
  have h2 := Nat.testBit_mod_two_pow (a' + b') (i + 1) i
  rw [this] at h1
  simpa using h1.symm.trans h2

/-- Two naturals agreeing on bits `0..i` agree modulo `2^(i+1)`. -/
theorem mod_eq_of_testBit {a b : Nat} (i : Nat) (h : ∀ j, j ≤ i → a.testBit j = b.testBit j) :
    a % 2 ^ (i + 1) = b % 2 ^ (i + 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < i + 1
  · simp [hj, h j (by omega)]
  · simp [hj]

theorem exists_bit_of_ne {y : BitVec w} (hne : y ≠ 0#w) : ∃ j, ∃ hj : j < w, y[j] = true := by
  apply Classical.byContradiction
  intro hn
  apply hne
  ext j hj
  cases h : y[j]
  · simp
  · exact absurd ⟨j, hj, h⟩ hn

end Grounding.Rtl.Rail
