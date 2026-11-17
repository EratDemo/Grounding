-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL: basic lemmas about the `TritVec` operations.
-/

import Grounding.Rtl.TritVec

namespace Grounding.Rtl

namespace TritVec

@[simp] theorem not_bits (a : TritVec w) (i : Nat) (h : i < w) :
    (not_ a).bits[i] = Trit.not a.bits[i] := by
  simp [not_]

@[simp] theorem and_bits (a b : TritVec w) (i : Nat) (h : i < w) :
    (and_ a b).bits[i] = Trit.and a.bits[i] b.bits[i] := by
  simp [and_, Vector.get]

@[simp] theorem or_bits (a b : TritVec w) (i : Nat) (h : i < w) :
    (or_ a b).bits[i] = Trit.or a.bits[i] b.bits[i] := by
  simp [or_, Vector.get]

@[simp] theorem xor_bits (a b : TritVec w) (i : Nat) (h : i < w) :
    (xor_ a b).bits[i] = Trit.xor a.bits[i] b.bits[i] := by
  simp [xor_, Vector.get]

@[simp] theorem mux_bits (s : Trit) (a b : TritVec w) (i : Nat) (h : i < w) :
    (mux s a b).bits[i] = Trit.mux s a.bits[i] b.bits[i] := by
  simp [mux, Vector.get]

@[simp] theorem slice_bits (a : TritVec sw) (o : Nat) (hw : o + w ≤ sw) (i : Nat) (h : i < w) :
    (slice a o w hw).bits[i] = a.bits[o + i] := by
  simp [slice, Vector.get]

@[simp] theorem zero_bits (i : Nat) (h : i < w) : (zero w).bits[i] = Trit.zero := by simp [zero]
@[simp] theorem ones_bits (i : Nat) (h : i < w) : (ones w).bits[i] = Trit.one := by simp [ones]
@[simp] theorem undef_bits (i : Nat) (h : i < w) : (undef w).bits[i] = Trit.x := by simp [undef]

theorem ext' {a b : TritVec w} (h : ∀ i : Fin w, a.bits[i] = b.bits[i]) : a = b := by
  obtain ⟨va⟩ := a
  obtain ⟨vb⟩ := b
  congr 1
  exact Vector.ext fun i hi => h ⟨i, hi⟩

theorem bits_ne_x_of_hasUndef {c : TritVec w} (h : c.hasUndef = false) (i : Nat) (hi : i < w) :
    c.bits[i] ≠ Trit.x := by
  simp only [hasUndef, List.any_eq_false, beq_iff_eq] at h
  exact h _ (by simp)

theorem fromTrit_bits (t : Trit) (i : Nat) (h : i < 1) : (fromTrit t).bits[i] = t := by
  simp [fromTrit]

theorem adcBits_cons (a : Trit) (as : List Trit) (b : Trit) (bs : List Trit) (c : Trit) :
    adcBits (a :: as) (b :: bs) c =
      ((Trit.sumT a b c) :: (adcBits as bs (Trit.carT a b c)).1,
       (adcBits as bs (Trit.carT a b c)).2) := by
  rfl

/-- Casting a `TritVec` along a width equation preserves its bit list. -/
theorem cast_toList {w w' : Nat} (h : w = w') (c : TritVec w) :
    (h ▸ c).bits.toList = c.bits.toList := by
  subst h; rfl

theorem adc_toList (a b : TritVec w) (cin : Trit) :
    (adc a b cin).bits.toList =
      (adcBits a.bits.toList b.bits.toList cin).1 ++
        [(adcBits a.bits.toList b.bits.toList cin).2] := by
  unfold adc ofList
  simp only
  rw [cast_toList]
  simp

@[simp] theorem mux_ofBool (b : Bool) (a c : TritVec width) :
    TritVec.mux (Trit.ofBool b) a c = if b then a else c := by
  cases b
  · apply congrArg TritVec.mk
    apply Vector.ext
    intro i hi
    simp [Trit.mux, Trit.ofBool, Vector.get]
  · apply congrArg TritVec.mk
    apply Vector.ext
    intro i hi
    simp [Trit.mux, Trit.ofBool, Vector.get]

end TritVec

end Grounding.Rtl
