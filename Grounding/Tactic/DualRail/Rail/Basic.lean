-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL: two-rail (dual-rail) encoding of constants for `bv_decide`.

A `TritVec w` is represented by two bit-vectors: `x` (the X mask) and `v` (the
value, zero under X). `Rail c x v` says `c` is exactly that pair:

  bit i of c = X     ↔ x[i]
  bit i of c = 1     ↔ ¬x[i] ∧ v[i]
  bit i of c = 0     ↔ ¬x[i] ∧ ¬v[i]

Every operator gets a lemma: if the operands are encoded by `(xa, va)`, … then
the result is encoded by a `BitVec` formula. Unlike a two-valued translation,
nothing assumes X-freedom: statements about X propagation are in scope for
`bv_decide`.
-/

import Grounding.Rtl.TritVecOfBV

namespace Grounding.Rtl.Rail

open TritVec

/-- The trit of a (mask, value) bit pair (value bits under X are ignored). -/
def trit (x v : Bool) : Trit := if x then .x else Trit.ofBool v

/-- `c` is encoded by the mask `x` and the value `v`, with `v` zero under X. -/
def Rail (c : TritVec w) (x v : BitVec w) : Prop :=
  (∀ i (h : i < w), c.bits[i] = trit x[i] v[i]) ∧ v &&& x = 0#w

theorem rail_bit {c : TritVec w} {x v} (h : Rail c x v) (i : Nat) (hi : i < w) :
    c.bits[i] = trit x[i] v[i] := h.1 i hi

theorem rail_norm {c : TritVec w} {x v} (h : Rail c x v) (i : Nat) (hi : i < w) :
    x[i] = true → v[i] = false := by
  intro hx
  have := congrArg (·[i]) h.2
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at this
  simpa [hx] using this

theorem mk {c : TritVec w} {x v : BitVec w}
    (hb : ∀ i (h : i < w), c.bits[i] = trit x[i] v[i])
    (hn : ∀ i (h : i < w), x[i] = true → v[i] = false) : Rail c x v := by
  refine ⟨hb, ?_⟩
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  cases hx : x[i] <;> simp [hn i hi, hx]

/-! ### Trits of the encoding -/

@[simp] theorem trit_true (v : Bool) : trit true v = .x := rfl
@[simp] theorem trit_false (v : Bool) : trit false v = Trit.ofBool v := rfl

/-! ### Two-valued constants, X constants -/

theorem ofBV (a : BitVec w) : Rail (TritVec.ofBV a) 0#w a :=
  mk (fun i hi => by simp) (fun i hi h => by simp at h)

theorem const (c : TritVec w) (x v : BitVec w)
    (hb : ∀ i (h : i < w), c.bits[i] = trit x[i] v[i])
    (hn : ∀ i (h : i < w), x[i] = true → v[i] = false) : Rail c x v := mk hb hn

/-! ### Bitwise operations -/

theorem not {c : TritVec w} {x v} (h : Rail c x v) : Rail c.not_ x (~~~v &&& ~~~x) := by
  refine mk (fun i hi => ?_) (fun i hi hx => by simp [hx])
  rw [not_bits _ _ hi, rail_bit h i hi]
  cases hx : x[i] <;> cases hv : v[i] <;> simp [hx, hv, trit, Trit.not, Trit.ofBool]

/-- Defined zero / defined one of a rail pair. -/
abbrev zeroR (x v : BitVec w) : BitVec w := ~~~x &&& ~~~v
abbrev oneR (x v : BitVec w) : BitVec w := ~~~x &&& v

theorem and {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.and_ b) (~~~(zeroR xa va ||| zeroR xb vb) &&& ~~~(oneR xa va &&& oneR xb vb))
      (oneR xa va &&& oneR xb vb) := by
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · rw [and_bits _ _ _ hi, rail_bit ha i hi, rail_bit hb i hi]
    have na := rail_norm ha i hi
    have nb := rail_norm hb i hi
    cases hxa : xa[i] <;> cases hva : va[i] <;> cases hxb : xb[i] <;> cases hvb : vb[i] <;>
      simp_all [trit, Trit.and, Trit.ofBool]
  · simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or] at hx ⊢
    revert hx
    cases xa[i] <;> cases va[i] <;> cases xb[i] <;> cases vb[i] <;> simp

theorem or {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.or_ b) (~~~(oneR xa va ||| oneR xb vb) &&& ~~~(zeroR xa va &&& zeroR xb vb))
      (oneR xa va ||| oneR xb vb) := by
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · rw [or_bits _ _ _ hi, rail_bit ha i hi, rail_bit hb i hi]
    have na := rail_norm ha i hi
    have nb := rail_norm hb i hi
    cases hxa : xa[i] <;> cases hva : va[i] <;> cases hxb : xb[i] <;> cases hvb : vb[i] <;>
      simp_all [trit, Trit.or, Trit.ofBool]
  · simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or] at hx ⊢
    revert hx
    cases xa[i] <;> cases va[i] <;> cases xb[i] <;> cases vb[i] <;> simp

theorem xor {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.xor_ b) (xa ||| xb) ((va ^^^ vb) &&& ~~~(xa ||| xb)) := by
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · rw [xor_bits _ _ _ hi, rail_bit ha i hi, rail_bit hb i hi]
    cases hxa : xa[i] <;> cases hva : va[i] <;> cases hxb : xb[i] <;> cases hvb : vb[i] <;>
      simp [hxa, hva, hxb, hvb, trit, Trit.xor, Trit.ofBool]
  · simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or] at hx ⊢
    simp [hx]

/-- `mux s a b` with a one-bit selector rail `(xs, vs)`. -/
theorem mux {s : Trit} {a b : TritVec w} {xs vs : Bool} {xa va xb vb}
    (hs : s = trit xs vs) (hns : xs = true → vs = false)
    (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (TritVec.mux s a b)
      (bif xs then xa ||| xb ||| (va ^^^ vb) else bif vs then xa else xb)
      (bif xs then va &&& ~~~(xa ||| xb ||| (va ^^^ vb)) else bif vs then va else vb) := by
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · rw [mux_bits _ _ _ _ hi, rail_bit ha i hi, rail_bit hb i hi, hs]
    have na := rail_norm ha i hi
    have nb := rail_norm hb i hi
    cases xs <;> cases vs <;> simp at hns <;>
      cases hxa : xa[i] <;> cases hva : va[i] <;> cases hxb : xb[i] <;> cases hvb : vb[i] <;>
      simp_all [trit, Trit.mux, Trit.ofBool]
  · have na := rail_norm ha i hi
    have nb := rail_norm hb i hi
    cases xs <;> cases vs <;> simp at hns <;>
      simp only [Bool.cond_true, Bool.cond_false, BitVec.getElem_and, BitVec.getElem_not,
        BitVec.getElem_or, BitVec.getElem_xor] at hx ⊢ <;>
      revert hx na nb <;>
      cases xa[i] <;> cases va[i] <;> cases xb[i] <;> cases vb[i] <;> simp

/-- The selector of a one-bit rail. -/
theorem bit0 {c : TritVec 1} {x v : BitVec 1} (h : Rail c x v) :
    c.bit0 = trit (x.getLsbD 0) (v.getLsbD 0) ∧ (x.getLsbD 0 = true → v.getLsbD 0 = false) := by
  refine ⟨?_, fun hx => ?_⟩
  · have := rail_bit h 0 (by omega)
    simpa [TritVec.bit0, Vector.get, BitVec.getLsbD_eq_getElem] using this
  · exact by simpa [BitVec.getLsbD_eq_getElem] using rail_norm h 0 (by omega) (by
      simpa [BitVec.getLsbD_eq_getElem] using hx)

/-- Every bit of `bif b then allOnes n else 0#n` is `b`. -/
theorem cond_allOnes_getElem {n : Nat} (b : Bool) {i : Nat} (hi : i < n) :
    (cond b (BitVec.allOnes n) (0#n))[i] = b := by
  cases b <;> simp

/-- Replicating a one-bit constant: the mask/value are all ones exactly when
the bit is X / one. -/
theorem replicate (n : Nat) {c : TritVec 1} {x v : BitVec 1} (h : Rail c x v) :
    Rail (TritVec.replicate n c)
      (bif x.getLsbD 0 then BitVec.allOnes n else 0#n)
      (bif v.getLsbD 0 then BitVec.allOnes n else 0#n) := by
  have hb := (bit0 h).1
  have hn := (bit0 h).2
  have hbits : ∀ i (hi : i < n), (TritVec.replicate n c).bits[i] = c.bit0 := by
    intro i hi
    simp [TritVec.replicate, Vector.getElem_replicate]
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · rw [hbits i hi, hb, cond_allOnes_getElem (x.getLsbD 0) hi, cond_allOnes_getElem (v.getLsbD 0) hi]
  · rw [cond_allOnes_getElem (x.getLsbD 0) hi] at hx
    rw [cond_allOnes_getElem (v.getLsbD 0) hi]
    exact hn hx

/-! ### Selects and concatenation -/

theorem slice {c : TritVec sw} {x v} (h : Rail c x v) (o : Nat) (hw : o + w ≤ sw) :
    Rail (c.slice o w hw) (x.extractLsb' o w) (v.extractLsb' o w) := by
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · rw [slice_bits _ _ _ _ hi, rail_bit h (o + i) (by omega)]
    simp [BitVec.getLsbD_eq_getElem (show o + i < sw by omega)]
  · simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem (show o + i < sw by omega)]
      at hx ⊢
    exact rail_norm h _ _ hx

theorem appendW {a : TritVec n} {b : TritVec (w - n)} {xa va xb vb} (hn : n ≤ w)
    (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.appendW b w) ((xa ++ xb).cast (by omega)) ((va ++ vb).cast (by omega)) := by
  refine mk (fun i hi => ?_) (fun i hi hx => ?_)
  · simp only [TritVec.appendW, TritVec.ofArrayD, Vector.getElem_ofFn, BitVec.getElem_cast,
      BitVec.getElem_append]
    rw [Array.getD_eq_getD_getElem?]
    by_cases hm : i < w - n
    · rw [Array.getElem?_append_left (by simpa using hm)]
      simp [hm, rail_bit hb i hm]
    · rw [Array.getElem?_append_right (by simpa using hm)]
      simp [hm, show i - (w - n) < n by omega, rail_bit ha _ (show i - (w - n) < n by omega)]
  · simp only [BitVec.getElem_cast, BitVec.getElem_append] at hx ⊢
    split <;> rename_i hm <;> simp only [hm, dite_true, dite_false] at hx ⊢
    · exact rail_norm hb _ _ hx
    · exact rail_norm ha _ _ hx

theorem empty (c : TritVec 0) : Rail c 0#0 0#0 :=
  mk (fun i hi => absurd hi (by omega)) (fun i hi => absurd hi (by omega))

/-! ### Comparisons and arithmetic: any X ↦ all X -/

/-- The rail of an all-X-or-defined operation: if either operand has an X
bit, everything is X; otherwise the two-valued result `r`. -/
abbrev anyX (xa : BitVec w) (xb : BitVec k) : Bool := xa != 0#w || xb != 0#k

theorem hasUndef_iff {c : TritVec w} {x v} (h : Rail c x v) : c.hasUndef = (x != 0#w) := by
  by_cases hx : x = 0#w
  · subst hx
    rw [show (0#w != 0#w) = false by simp, hasUndef_eq_false_iff]
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    simp only [Vector.length_toList] at hi
    simp [rail_bit h i hi, trit]
  · rw [show (x != 0#w) = true by simpa using hx]
    obtain ⟨i, hi, hxi⟩ : ∃ i, ∃ hi : i < w, x[i] = true := by
      apply Classical.byContradiction
      intro hne
      apply hx
      ext i hi
      simp only [BitVec.getElem_zero]
      cases hxi : x[i]
      · rfl
      · exact absurd ⟨i, hi, hxi⟩ hne
    have hc : c.bits[i] = Trit.x := by simp [rail_bit h i hi, hxi]
    simp only [hasUndef, List.any_eq_true, beq_iff_eq]
    exact ⟨_, List.getElem_mem (by simpa using hi), by simpa using hc⟩

theorem tieDownX_eq {c : TritVec w} {x v} (h : Rail c x v) (hx : x = 0#w) : tieDownX c = v := by
  ext i hi
  rw [tieDownX_getElem _ _ hi, rail_bit h i hi]
  subst hx
  cases hv : v[i] <;> simp [trit]

theorem undef (w : Nat) : Rail (TritVec.undef w) (BitVec.allOnes w) 0#w :=
  mk (fun i hi => by simp [trit]) (fun i hi _ => by simp)

/-- `ite` on `Rail`: a two-way choice between encodings. -/
theorem ite {c₁ c₂ : TritVec w} {x₁ v₁ x₂ v₂} (b : Bool) (h₁ : Rail c₁ x₁ v₁) (h₂ : Rail c₂ x₂ v₂) :
    Rail (if b then c₁ else c₂) (bif b then x₁ else x₂) (bif b then v₁ else v₂) := by
  cases b <;> simpa

theorem mul {a b : TritVec w} {xa va xb vb} (ha : Rail a xa va) (hb : Rail b xb vb) :
    Rail (a.mul b) (bif anyX xa xb then BitVec.allOnes w else 0#w)
      (bif anyX xa xb then 0#w else va * vb) := by
  rw [TritVec.mul, hasUndef_iff ha, hasUndef_iff hb]
  by_cases h : (xa != 0#w || xb != 0#w) = true
  · simpa [h] using ite true (undef w) (ofBV (va * vb))
  · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h
    rw [tieDownX_eq ha h.1, tieDownX_eq hb h.2]
    simpa [h.1, h.2] using ofBV (va * vb)

/-- A one-bit result `fromTrit t` from a two-valued Boolean or all X. -/
theorem fromTrit_anyX (any : Bool) (r : Bool) :
    Rail (if any then fromTrit .x else fromTrit (Trit.ofBool r))
      (bif any then 1#1 else 0#1) (bif any then 0#1 else BitVec.ofBool r) := by
  cases any
  · simp only [Bool.false_eq_true, ite_false, Bool.cond_false, fromTrit_ofBool]
    exact ofBV _
  · simp only [ite_true, Bool.cond_true]
    exact mk (fun i hi => by obtain rfl : i = 0 := by omega
                             simp [fromTrit_bits, trit]) (fun _ _ _ => by simp)

/-- Move a rail proof across an equality of constants. -/
theorem of_eq {c c' : TritVec w} (h : c = c') {x v : BitVec w} (hr : Rail c x v) : Rail c' x v :=
  h ▸ hr


end Grounding.Rtl.Rail
