-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL: `TritVec` operations on embedded `BitVec` constants.
-/

import Grounding.Rtl.TritVecLemmas

namespace Grounding.Rtl

namespace Trit

/-- `==` on trits is decidable equality; as a local simp lemma it lets `simp`
evaluate comparisons of literals. -/
theorem beq_eq_decide (a b : Trit) : (a == b) = decide (a = b) := rfl

attribute [local simp] beq_eq_decide

@[simp, grind =] theorem ofBool_true : ofBool true = one := rfl
@[simp, grind =] theorem ofBool_false : ofBool false = zero := rfl

@[simp] theorem ofBool_ne_x (b : Bool) : ofBool b ≠ x := by cases b <;> decide

@[simp] theorem ofBool_beq_one (b : Bool) : (ofBool b == one) = b := by cases b <;> rfl

theorem ofBool_beq_one_of_ne_x {t : Trit} (h : t ≠ x) : ofBool (t == one) = t := by
  cases t <;> first | rfl | exact absurd rfl h

theorem ofBool_not (a : Bool) : not (ofBool a) = ofBool (!a) := by cases a <;> rfl
theorem ofBool_and (a b : Bool) : and (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl
theorem ofBool_or (a b : Bool) : or (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl
theorem ofBool_xor (a b : Bool) : xor (ofBool a) (ofBool b) = ofBool (a ^^ b) := by
  cases a <;> cases b <;> rfl

end Trit

namespace TritVec

attribute [local simp] Trit.beq_eq_decide

/-! ### The number denoted by a trit list -/

/-- The natural number denoted by an LSB-first trit list, reading X as 0. -/
def natOf (l : List Trit) : Nat := (BitVec.ofBoolListLE (l.map (· == Trit.one))).toNat

@[simp] theorem natOf_nil : natOf [] = 0 := rfl

theorem natOf_cons (t : Trit) (l : List Trit) :
    natOf (t :: l) = natOf l * 2 + (t == Trit.one).toNat := by
  simp only [natOf]
  exact BitVec.toNat_concat _ _

theorem natOf_append_single (l : List Trit) (t : Trit) :
    natOf (l ++ [t]) = natOf l + 2 ^ l.length * (t == Trit.one).toNat := by
  induction l with
  | nil => simp [natOf_cons]
  | cons a l ih =>
    simp only [List.cons_append, natOf_cons, ih, List.length_cons, Nat.pow_succ]
    grind

theorem natOf_lt (l : List Trit) : natOf l < 2 ^ l.length := by
  simpa [natOf] using (BitVec.ofBoolListLE (l.map (· == Trit.one))).isLt

theorem testBit_natOf (l : List Trit) (i : Nat) :
    (natOf l).testBit i = (l.getD i .zero == .one) := by
  rw [natOf, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  cases h : l[i]? <;> simp [h]

theorem toNat_tieDownX (c : TritVec w) : (tieDownX c).toNat = natOf c.bits.toList := by
  simp [tieDownX, natOf]

theorem tieDownX_getElem (c : TritVec w) (i : Nat) (h : i < w) :
    (tieDownX c)[i] = (c.bits[i] == Trit.one) := by
  rw [← BitVec.getLsbD_eq_getElem, tieDownX_getLsbD, List.getD_eq_getElem?_getD]
  simp [h]

/-! ### `ofBV` and `tieDownX` -/

theorem ext_nat {a b : TritVec w} (h : ∀ i (hi : i < w), a.bits[i] = b.bits[i]) : a = b :=
  TritVec.ext' fun i => h i.1 i.2

theorem hasUndef_eq_false_iff (c : TritVec w) :
    c.hasUndef = false ↔ ∀ t ∈ c.bits.toList, t ≠ Trit.x := by
  simp only [hasUndef, List.any_eq_false, beq_iff_eq, ne_eq]

@[simp, grind =] theorem ofBV_bits (v : BitVec w) (i : Nat) (h : i < w) :
    (ofBV v).bits[i] = Trit.ofBool v[i] := by
  simp [ofBV]

@[simp] theorem ofBV_get (v : BitVec w) (i : Fin w) :
    (ofBV v).bits.get i = Trit.ofBool v[i.1] :=
  ofBV_bits v i.1 i.2

@[simp, grind =] theorem hasUndef_ofBV (v : BitVec w) : (ofBV v).hasUndef = false := by
  rw [hasUndef_eq_false_iff]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  simp at hi
  simp

@[simp, grind =] theorem tieDownX_ofBV (v : BitVec w) : tieDownX (ofBV v) = v := by
  ext i hi
  rw [tieDownX_getElem _ _ hi, ofBV_bits, Trit.ofBool_beq_one]

/-- An X-free constant is the `ofBV` of its two-valued projection (`grind` uses it to
turn X-free signals into `BitVec`s). -/
@[grind =] theorem ofBV_tieDownX {c : TritVec w} (h : c.hasUndef = false) : ofBV (tieDownX c) = c := by
  apply ext_nat
  intro i hi
  rw [ofBV_bits, tieDownX_getElem]
  exact Trit.ofBool_beq_one_of_ne_x (bits_ne_x_of_hasUndef h i hi)

@[grind inj] theorem ofBV_injective : Function.Injective (ofBV : BitVec w → TritVec w) :=
  fun a b h => by rw [← tieDownX_ofBV a, h, tieDownX_ofBV]

@[simp] theorem ofBV_inj {a b : BitVec w} : ofBV a = ofBV b ↔ a = b :=
  ⟨fun h => ofBV_injective h, fun h => h ▸ rfl⟩

/-- A constant without X is `ofBV` of its projection. -/
theorem eq_ofBV_of_hasUndef {c : TritVec w} (h : c.hasUndef = false) : ∃ v, c = ofBV v :=
  ⟨tieDownX c, (ofBV_tieDownX h).symm⟩

/-- A single-bit constant whose bit is not X is `ofBV` of a bit. -/
theorem exists_ofBV_of_bit0 {c : TritVec 1} (h : c.bit0 ≠ Trit.x) : ∃ v, c = ofBV v := by
  obtain ⟨⟨⟨l⟩, hl⟩⟩ := c
  match l, hl with
  | [t], _ =>
    have h' : t ≠ Trit.x := by simpa [bit0, Vector.get] using h
    cases t with
    | zero => exact ⟨0#1, rfl⟩
    | one => exact ⟨1#1, rfl⟩
    | x => exact absurd rfl h'

@[simp, grind =] theorem hasUndef_undef : (undef w).hasUndef = decide (0 < w) := by
  cases w <;> simp [hasUndef, undef, List.replicate_succ]

theorem toList_inj {a b : TritVec w} : a.bits.toList = b.bits.toList ↔ a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  simp [Vector.toList_inj]

/-- Two X-free constants are equal iff their projections are. -/
theorem eq_iff_tieDownX {a b : TritVec w} (ha : a.hasUndef = false) (hb : b.hasUndef = false) :
    a = b ↔ tieDownX a = tieDownX b :=
  ⟨fun h => h ▸ rfl, fun h => by rw [← ofBV_tieDownX ha, ← ofBV_tieDownX hb, h]⟩

@[grind =] theorem fromTrit_ofBool (b : Bool) : fromTrit (Trit.ofBool b) = ofBV (BitVec.ofBool b) := by
  apply ext_nat
  intro i hi
  obtain rfl : i = 0 := by omega
  simp [fromTrit_bits]

theorem fromTrit_x : fromTrit Trit.x = undef 1 := rfl
theorem fromTrit_zero : fromTrit Trit.zero = ofBV 0#1 := fromTrit_ofBool false
theorem fromTrit_one : fromTrit Trit.one = ofBV 1#1 := fromTrit_ofBool true

@[simp, grind =] theorem bit0_ofBV (v : BitVec 1) : (ofBV v).bit0 = Trit.ofBool v[0] :=
  ofBV_bits v 0 (by omega)

/-! ### Bitwise operations, selects and concatenation -/

@[simp, grind =] theorem not_ofBV (a : BitVec w) : (ofBV a).not_ = ofBV (~~~a) :=
  ext_nat fun i hi => by simp [Trit.ofBool_not]

@[simp, grind =] theorem and_ofBV (a b : BitVec w) : (ofBV a).and_ (ofBV b) = ofBV (a &&& b) :=
  ext_nat fun i hi => by simp [Trit.ofBool_and]

@[simp, grind =] theorem or_ofBV (a b : BitVec w) : (ofBV a).or_ (ofBV b) = ofBV (a ||| b) :=
  ext_nat fun i hi => by simp [Trit.ofBool_or]

@[simp, grind =] theorem xor_ofBV (a b : BitVec w) : (ofBV a).xor_ (ofBV b) = ofBV (a ^^^ b) :=
  ext_nat fun i hi => by simp [Trit.ofBool_xor]

@[simp, grind =] theorem mux_ofBV (s : Bool) (a b : BitVec w) :
    mux (Trit.ofBool s) (ofBV a) (ofBV b) = ofBV (if s then a else b) := by
  cases s <;> exact ext_nat fun i hi => by simp [Trit.mux]

@[simp, grind =] theorem mux_zero (a b : TritVec w) : mux Trit.zero a b = b :=
  ext_nat fun _ _ => by simp [Trit.mux]

@[simp, grind =] theorem mux_one (a b : TritVec w) : mux Trit.one a b = a :=
  ext_nat fun _ _ => by simp [Trit.mux]

@[simp, grind =] theorem slice_ofBV (a : BitVec sw) (o : Nat) (h : o + w ≤ sw) :
    (ofBV a).slice o w h = ofBV (a.extractLsb' o w) :=
  ext_nat fun i hi => by simp [BitVec.getLsbD_eq_getElem (show o + i < sw by omega)]

@[simp, grind =] theorem concat_ofBV (a : BitVec w₁) (b : BitVec w₂) :
    (ofBV a).concat (ofBV b) = ofBV ((b ++ a).cast (Nat.add_comm _ _)) :=
  ext_nat fun i hi => by
    simp only [concat, Vector.getElem_ofFn, ofBV_get, ofBV_bits, BitVec.getElem_cast,
      BitVec.getElem_append]
    split <;> rfl

/-! ### Addition -/

theorem adc_bit {a b c : Trit} (ha : a ≠ .x) (hb : b ≠ .x) (hc : c ≠ .x) :
    Trit.sumT a b c ≠ .x ∧ Trit.carT a b c ≠ .x ∧
    (Trit.sumT a b c == .one).toNat + 2 * (Trit.carT a b c == .one).toNat =
      (a == .one).toNat + (b == .one).toNat + (c == .one).toNat := by
  cases a <;> cases b <;> cases c <;> first | decide | exact absurd rfl ‹_›

theorem adcBits_defined : ∀ (as bs : List Trit) (c : Trit), as.length = bs.length →
    (∀ t ∈ as, t ≠ .x) → (∀ t ∈ bs, t ≠ .x) → c ≠ .x →
    (∀ t ∈ (adcBits as bs c).1, t ≠ .x) ∧ (adcBits as bs c).2 ≠ .x ∧
    natOf (adcBits as bs c).1 + 2 ^ as.length * ((adcBits as bs c).2 == .one).toNat =
      natOf as + natOf bs + (c == .one).toNat
  | [], [], c, _, _, _, hc => by simp [adcBits, hc]
  | a :: as, b :: bs, c, hl, ha, hb, hc => by
    obtain ⟨hs, hk, hbit⟩ := adc_bit (ha a (by simp)) (hb b (by simp)) hc
    obtain ⟨h1, h2, h3⟩ := adcBits_defined as bs (Trit.carT a b c) (by simpa using hl)
      (fun t ht => ha t (by simp [ht])) (fun t ht => hb t (by simp [ht])) hk
    rw [TritVec.adcBits_cons]
    refine ⟨?_, h2, ?_⟩
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hs
      · exact h1 t ht
    · simp only [natOf_cons, List.length_cons, Nat.pow_succ]
      grind
  | [], _ :: _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _, _ => by simp at hl

theorem adc_defined {a b : TritVec w} {c : Trit} (ha : a.hasUndef = false)
    (hb : b.hasUndef = false) (hc : c ≠ .x) :
    adc a b c = ofBV (BitVec.ofNat (w + 1)
      ((tieDownX a).toNat + (tieDownX b).toNat + (c == .one).toNat)) := by
  obtain ⟨h1, h2, h3⟩ := adcBits_defined a.bits.toList b.bits.toList c (by simp)
    ((hasUndef_eq_false_iff a).1 ha) ((hasUndef_eq_false_iff b).1 hb) hc
  have hd : (adc a b c).hasUndef = false := by
    rw [hasUndef_eq_false_iff, TritVec.adc_toList]
    intro t ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact h1 t ht
    · exact h2
  rw [← ofBV_tieDownX hd, ofBV_inj]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_tieDownX, TritVec.adc_toList, natOf_append_single,
    adcBits_length _ _ _ (by simp), BitVec.toNat_ofNat, toNat_tieDownX, toNat_tieDownX]
  simp only [Vector.length_toList] at h3 ⊢
  rw [h3, Nat.mod_eq_of_lt]
  have := natOf_lt a.bits.toList
  have := natOf_lt b.bits.toList
  have : (c == .one).toNat ≤ 1 := Bool.toNat_le _
  simp only [Vector.length_toList] at *
  rw [Nat.pow_succ]
  omega

/-- On X-free operands `adc` is `BitVec` addition one bit wider. -/
@[simp, grind =] theorem adc_ofBV (a b : BitVec w) (c : Bool) :
    adc (ofBV a) (ofBV b) (Trit.ofBool c) =
      ofBV (a.setWidth (w + 1) + b.setWidth (w + 1) + (BitVec.ofBool c).setWidth (w + 1)) := by
  rw [adc_defined (hasUndef_ofBV a) (hasUndef_ofBV b) (Trit.ofBool_ne_x c), ofBV_inj,
    tieDownX_ofBV, tieDownX_ofBV, Trit.ofBool_beq_one, ← BitVec.toNat_ofBool,
    BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_toNat,
    BitVec.ofNat_toNat]

/-- The low `w` bits of `adc`: `w`-bit addition (this is how `+` is built). -/
@[simp, grind =] theorem add_ofBV (a b : BitVec w) (c : Bool) (h : 0 + w ≤ w + 1) :
    (adc (ofBV a) (ofBV b) (Trit.ofBool c)).slice 0 w h =
      ofBV (a + b + (BitVec.ofBool c).setWidth w) := by
  rw [adc_defined (hasUndef_ofBV a) (hasUndef_ofBV b) (Trit.ofBool_ne_x c), slice_ofBV, ofBV_inj,
    tieDownX_ofBV, tieDownX_ofBV, Trit.ofBool_beq_one]
  have hr : a + b + (BitVec.ofBool c).setWidth w =
      BitVec.ofNat w (a.toNat + b.toNat + c.toNat) := by
    rw [← BitVec.toNat_ofBool, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]
  rw [hr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ w))

/-- `add_ofBV` with a literal carry-in of 0 (the common `a + b`). -/
@[simp, grind =] theorem add_ofBV_zero (a b : BitVec w) (h : 0 + w ≤ w + 1) :
    (adc (ofBV a) (ofBV b) Trit.zero).slice 0 w h = ofBV (a + b) := by
  have := add_ofBV a b false h
  simp only [Trit.ofBool_false] at this
  rw [this]
  simp

@[simp, grind =] theorem adc_ofBV_zero (a b : BitVec w) :
    adc (ofBV a) (ofBV b) Trit.zero = ofBV (a.setWidth (w + 1) + b.setWidth (w + 1)) := by
  have := adc_ofBV a b false
  simp only [Trit.ofBool_false] at this
  rw [this]
  simp

@[simp, grind =] theorem adc_ofBV_one (a b : BitVec w) :
    adc (ofBV a) (ofBV b) Trit.one =
      ofBV (a.setWidth (w + 1) + b.setWidth (w + 1) + 1#(w + 1)) := by
  have := adc_ofBV a b true
  simp only [Trit.ofBool_true] at this
  rw [this]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero w))]

/-! ### Multiplication -/

/-- Any X gives all X; otherwise `BitVec` multiplication. -/
@[grind =] theorem mul_spec (a b : TritVec w) :
    mul a b = if a.hasUndef || b.hasUndef then undef w
      else ofBV (tieDownX a * tieDownX b) := rfl

@[simp, grind =] theorem mul_ofBV (a b : BitVec w) : mul (ofBV a) (ofBV b) = ofBV (a * b) := by
  simp [mul_spec]

/-- Only a nonzero width can hold an X. -/
@[grind →] theorem pos_of_hasUndef {c : TritVec w} (h : c.hasUndef = true) : 0 < w := by
  cases w with
  | zero => simp [hasUndef, List.eq_nil_of_length_eq_zero (c.bits.toList.length_eq_zero_iff.mpr
      (by simp))] at h
  | succ => omega

@[simp, grind =] theorem hasUndef_mul (a b : TritVec w) :
    (mul a b).hasUndef = (a.hasUndef || b.hasUndef) := by
  rw [mul_spec]
  split
  · rename_i h
    rw [hasUndef_undef, h]
    simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simpa using pos_of_hasUndef h
  · rename_i h
    rw [hasUndef_ofBV]
    simpa using h

/-! ### Comparisons -/

theorem ultBits_aux : ∀ (as bs : List Trit) (r : Trit), as.length = bs.length →
    (∀ t ∈ as, t ≠ .x) → (∀ t ∈ bs, t ≠ .x) →
    (as.zip bs).foldl (fun r (p : Trit × Trit) =>
      if p.1 == p.2 then r else if p.1 == Trit.zero then Trit.one else Trit.zero) r =
      if natOf as < natOf bs then .one else if natOf bs < natOf as then .zero else r
  | [], [], r, _, _, _ => by simp
  | a :: as, b :: bs, r, hl, ha, hb => by
    have ha0 := ha a (by simp)
    have hb0 := hb b (by simp)
    rw [List.zip_cons_cons, List.foldl_cons,
      ultBits_aux as bs _ (by simpa using hl) (fun t ht => ha t (by simp [ht]))
        (fun t ht => hb t (by simp [ht])),
      natOf_cons, natOf_cons]
    generalize natOf as = A
    generalize natOf bs = B
    cases a <;> cases b <;> simp at ha0 hb0 ⊢ <;> repeat' split
    all_goals first | rfl | (exfalso; omega)
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl

theorem ultBits_defined (as bs : List Trit) (hl : as.length = bs.length)
    (ha : ∀ t ∈ as, t ≠ .x) (hb : ∀ t ∈ bs, t ≠ .x) :
    ultBits as bs = Trit.ofBool (decide (natOf as < natOf bs)) := by
  refine (ultBits_aux as bs .zero hl ha hb).trans ?_
  by_cases h : natOf as < natOf bs
  · simp [h]
  · simp [h]

/-- Any X gives X; otherwise unsigned `BitVec` comparison. -/
@[grind =] theorem ult_spec (a b : TritVec w) :
    ult a b = if a.hasUndef || b.hasUndef then undef 1
      else ofBV (BitVec.ofBool (decide (tieDownX a < tieDownX b))) := by
  unfold ult
  split
  · rfl
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    rw [ultBits_defined _ _ (by simp) ((hasUndef_eq_false_iff a).1 h.1)
      ((hasUndef_eq_false_iff b).1 h.2), fromTrit_ofBool]
    simp only [BitVec.lt_def, toNat_tieDownX]

@[simp, grind =] theorem ult_ofBV (a b : BitVec w) :
    ult (ofBV a) (ofBV b) = ofBV (BitVec.ofBool (decide (a < b))) := by
  simp [ult_spec]

theorem msb?_defined {c : TritVec (n + 1)} (h : c.hasUndef = false) :
    c.msb? = some (Trit.ofBool (tieDownX c).msb) := by
  rw [msb?, List.getLast?_eq_getElem?, BitVec.msb_eq_getLsbD_last,
    BitVec.getLsbD_eq_getElem (by omega), tieDownX_getElem _ _ (by omega),
    Trit.ofBool_beq_one_of_ne_x (bits_ne_x_of_hasUndef h _ (by omega))]
  simp

/-- Any X gives X; otherwise signed `BitVec` comparison. -/
@[grind =] theorem slt_spec (a b : TritVec w) :
    slt a b = if a.hasUndef || b.hasUndef then undef 1
      else ofBV (BitVec.ofBool ((tieDownX a).slt (tieDownX b))) := by
  unfold slt
  split
  · rfl
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    cases w with
    | zero =>
      have h0 : ∀ c : TritVec 0, c.msb? = none := by
        intro c
        rw [msb?, List.getLast?_eq_none_iff, ← List.length_eq_zero_iff]
        simp
      have : (tieDownX a).slt (tieDownX b) = false := by
        rw [BitVec.eq_nil (tieDownX a), BitVec.eq_nil (tieDownX b)]; rfl
      rw [h0, h0, this, ← fromTrit_ofBool]
      rfl
    | succ n =>
      rw [msb?_defined h.1, msb?_defined h.2]
      have hu : ultBits a.bits.toList b.bits.toList =
          Trit.ofBool ((tieDownX a).ult (tieDownX b)) := by
        rw [ultBits_defined _ _ (by simp) ((hasUndef_eq_false_iff a).1 h.1)
          ((hasUndef_eq_false_iff b).1 h.2), BitVec.ult_eq_decide, toNat_tieDownX,
          toNat_tieDownX]
      simp only [hu, BitVec.slt_eq_ult]
      generalize ha : tieDownX a = A
      generalize hb : tieDownX b = B
      cases hA : A.msb <;> cases hB : B.msb
      · simp [fromTrit_ofBool]
      · have := BitVec.ult_eq_msb_of_msb_neq (x := A) (y := B) (by simp [hA, hB])
        simp [hB, this, fromTrit_zero]
      · have := BitVec.ult_eq_msb_of_msb_neq (x := A) (y := B) (by simp [hA, hB])
        simp [hB, this, fromTrit_one]
      · simp [fromTrit_ofBool]

@[simp, grind =] theorem slt_ofBV (a b : BitVec w) :
    slt (ofBV a) (ofBV b) = ofBV (BitVec.ofBool (a.slt b)) := by
  simp [slt_spec]

theorem eqBits_defined : ∀ (as bs : List Trit), as.length = bs.length →
    (∀ t ∈ as, t ≠ .x) → (∀ t ∈ bs, t ≠ .x) →
    eqBits as bs = Trit.ofBool (decide (as = bs))
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, hl, ha, hb => by
    have ha0 := ha a (by simp)
    have hb0 := hb b (by simp)
    simp only [eqBits]
    rw [eqBits_defined as bs (by simpa using hl) (fun t ht => ha t (by simp [ht]))
      (fun t ht => hb t (by simp [ht]))]
    by_cases h : as = bs <;> cases a <;> cases b <;> simp_all [Trit.ofBool]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- On X-free operands `==` is `BitVec` equality. (With X it can still be
0: a defined mismatch decides.) -/
theorem eq_defined {a b : TritVec w} (ha : a.hasUndef = false) (hb : b.hasUndef = false) :
    eq a b = ofBV (BitVec.ofBool (decide (tieDownX a = tieDownX b))) := by
  rw [eq, eqBits_defined _ _ (by simp) ((hasUndef_eq_false_iff a).1 ha)
    ((hasUndef_eq_false_iff b).1 hb), fromTrit_ofBool]
  simp only [toList_inj, eq_iff_tieDownX ha hb]

@[simp, grind =] theorem eq_ofBV (a b : BitVec w) :
    eq (ofBV a) (ofBV b) = ofBV (BitVec.ofBool (decide (a = b))) := by
  simp [eq_defined]

@[simp, grind =] theorem eqx_ofBV (a b : BitVec w) :
    eqx (ofBV a) (ofBV b) = ofBV (BitVec.ofBool (decide (a = b))) := by
  rw [← fromTrit_ofBool]
  by_cases h : a = b <;> simp [eqx, h]

/-! ### Shifts -/

/-- No one bit of `l` sits at an absolute position (`idx + j`) of 32 or more. -/
def FitsShift (l : List Trit) (idx : Nat) : Prop :=
  ∀ j (h : j < l.length), 32 ≤ idx + j → l[j] ≠ .one

instance (l : List Trit) (idx : Nat) : Decidable (FitsShift l idx) := by
  unfold FitsShift; infer_instance

theorem fitsShift_cons (t : Trit) (ts : List Trit) (idx : Nat) :
    FitsShift (t :: ts) idx ↔ (32 ≤ idx → t ≠ .one) ∧ FitsShift ts (idx + 1) := by
  constructor
  · intro h
    exact ⟨fun hi => h 0 (by simp) (by omega),
      fun j hj hi => h (j + 1) (by simp; omega) (by omega)⟩
  · rintro ⟨h0, h1⟩ j hj hi
    cases j with
    | zero => exact h0 (by omega)
    | succ j => exact h1 j (by simpa using hj) (by omega)

theorem shiftAmountAux_spec : ∀ (l : List Trit) (idx : Nat),
    shiftAmountAux l idx = if FitsShift l idx then some (natOf l) else none
  | [], _ => by simp [shiftAmountAux, FitsShift]
  | t :: ts, idx => by
    simp only [shiftAmountAux, shiftAmountAux_spec ts (idx + 1)]
    by_cases h1 : FitsShift ts (idx + 1) <;> by_cases ht : t = .one <;>
      by_cases hi : 32 ≤ idx <;> simp [h1, ht, hi, fitsShift_cons, natOf_cons]

theorem fitsShift_iff (l : List Trit) : FitsShift l 0 ↔ natOf l < 2 ^ 32 := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_natOf, List.getD_eq_getElem?_getD]
    by_cases hl : i < l.length
    · simp [hl, h i hl (by omega)]
    · simp [hl]
  · intro h j hj hi hone
    have hb := testBit_natOf l j
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))),
      List.getD_eq_getElem?_getD] at hb
    simp [hj, hone] at hb

theorem shiftAmount?_ofBV (m : BitVec k) :
    shiftAmount? (ofBV m) = if m.toNat < 2 ^ 32 then some m.toNat else none := by
  rw [shiftAmount?, shiftAmountAux_spec, ← toNat_tieDownX, tieDownX_ofBV]
  by_cases h : FitsShift (ofBV m).bits.toList 0
  · have h' := (fitsShift_iff _).1 h
    rw [← toNat_tieDownX, tieDownX_ofBV] at h'
    simp [h, h']
  · have h' := mt (fitsShift_iff _).2 h
    rw [← toNat_tieDownX, tieDownX_ofBV] at h'
    simp [h, h']

theorem shiftBy_of_hasUndef (left : Bool) (f : Trit) (stride : Nat)
    (a : TritVec w) {m : TritVec k}
    (h : m.hasUndef = true) : shiftBy left f stride a m = undef w := by
  simp [shiftBy, h]

@[simp, grind =] theorem shl_ofBV (a : BitVec w) (m : BitVec k) (hw : w ≤ 2 ^ 32) :
    shl (ofBV a) (ofBV m) = ofBV (a <<< m) := by
  rw [BitVec.shiftLeft_eq']
  unfold shl shiftBy
  rw [hasUndef_ofBV, shiftAmount?_ofBV]
  by_cases hm : m.toNat < 2 ^ 32
  · have hge : ¬ m.toNat * 1 ≥ 2 ^ 32 := by omega
    simp only [hm, hge, ite_true, Bool.false_eq_true, ite_false]
    apply ext_nat
    intro i hi
    simp only [Vector.getElem_ofFn, ofBV_bits, BitVec.getElem_shiftLeft]
    by_cases hs : m.toNat ≤ i
    · simp [hs, show ¬ i < m.toNat by omega]
    · simp [hs, show i < m.toNat by omega]
  · simp only [hm, ite_false, Bool.false_eq_true]
    rw [BitVec.shiftLeft_eq_zero (by omega)]
    exact ext_nat fun i hi => by simp

@[simp, grind =] theorem ushr_ofBV (a : BitVec w) (m : BitVec k) (hw : w ≤ 2 ^ 32) :
    ushr (ofBV a) (ofBV m) = ofBV (a >>> m) := by
  rw [BitVec.ushiftRight_eq']
  unfold ushr shiftBy
  rw [hasUndef_ofBV, shiftAmount?_ofBV]
  by_cases hm : m.toNat < 2 ^ 32
  · have hge : ¬ m.toNat * 1 ≥ 2 ^ 32 := by omega
    simp only [hm, hge, ite_true, Bool.false_eq_true, ite_false]
    apply ext_nat
    intro i hi
    simp only [Vector.getElem_ofFn, ofBV_bits,
      BitVec.getElem_ushiftRight]
    by_cases hs : i + m.toNat < w
    · simp [hs, Nat.add_comm]
    · simp [hs, BitVec.getLsbD_of_ge a _ (show w ≤ m.toNat + i by omega)]
  · simp only [hm, ite_false, Bool.false_eq_true]
    exact ext_nat fun i hi => by
      simp [BitVec.getLsbD_of_ge a _ (show w ≤ m.toNat + i by omega)]

theorem sign_ofBV (a : BitVec (n + 1)) : sign (ofBV a) = Trit.ofBool a.msb := by
  rw [sign, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega)]
  simp

@[simp, grind =] theorem sshr_ofBV (a : BitVec w) (m : BitVec k) (hw : w ≤ 2 ^ 32) :
    sshr (ofBV a) (ofBV m) = ofBV (a.sshiftRight' m) := by
  cases w with
  | zero => exact ext_nat fun i hi => absurd hi (by omega)
  | succ n =>
    rw [BitVec.sshiftRight_eq']
    unfold sshr shiftBy
    rw [hasUndef_ofBV, shiftAmount?_ofBV, sign_ofBV]
    by_cases hm : m.toNat < 2 ^ 32
    · have hge : ¬ m.toNat * 1 ≥ 2 ^ 32 := by omega
      simp only [hm, hge, ite_true, ite_false, Bool.false_eq_true]
      apply ext_nat
      intro i hi
      simp only [Vector.getElem_ofFn, ofBV_bits,
        BitVec.getElem_sshiftRight]
      by_cases hs : i + m.toNat < n + 1
      · simp [hs, Nat.add_comm]
      · simp [hs, show ¬ m.toNat + i < n + 1 by omega]
    · simp only [hm, ite_false, Bool.false_eq_true]
      exact ext_nat fun i hi => by
        simp [BitVec.getElem_sshiftRight, show ¬ m.toNat + i < n + 1 by omega]

/-! ### Replication and strided shifts -/

/-- The amount of a strided shift: `m * stride` in a bit vector wide enough to
hold the product. -/
def stridedAmount (m : BitVec k) (stride : Nat) : BitVec (k + stride + 1) :=
  m.setWidth (k + stride + 1) * BitVec.ofNat (k + stride + 1) stride

@[simp, grind =] theorem stridedAmount_toNat (m : BitVec k) (stride : Nat) :
    (stridedAmount m stride).toNat = m.toNat * stride := by
  unfold stridedAmount
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by omega), BitVec.toNat_ofNat]
  have hm : m.toNat < 2 ^ k := m.isLt
  have hs : stride < 2 ^ (k + stride + 1) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hs2 : stride < 2 ^ (stride + 1) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hprod : m.toNat * stride < 2 ^ (k + stride + 1) := by
    calc m.toNat * stride < 2 ^ k * 2 ^ (stride + 1) :=
          Nat.mul_lt_mul_of_lt_of_lt hm hs2
      _ = 2 ^ (k + stride + 1) := by rw [← Nat.pow_add, Nat.add_assoc]
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hprod]

/-- An X-filling right shift by a zero amount is the identity. -/
@[simp, grind =] theorem xshrStride_zero (stride : Nat) (a : BitVec w) (k : Nat) :
    TritVec.xshrStride stride (ofBV a) (ofBV (0#k)) = ofBV a := by
  unfold TritVec.xshrStride TritVec.shiftBy
  rw [hasUndef_ofBV, shiftAmount?_ofBV]
  simp
  apply ext_nat
  intro i hi
  simp

@[simp, grind =] theorem stridedAmount_zero (k stride : Nat) :
    stridedAmount (0#k) stride = 0#(k + stride + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [stridedAmount_toNat]

@[simp, grind =] theorem BitVec.replicate_bit_zero (n : Nat) :
    BitVec.replicate n (0#1) = 0#(1 * n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_replicate]
  simp

@[simp, grind =] theorem tieDownX_replicate (n : Nat) (c : TritVec 1) :
    tieDownX (TritVec.replicate n c) =
      BitVec.cast (Nat.one_mul n) (BitVec.replicate n (tieDownX c)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [tieDownX_getLsbD, BitVec.getLsbD_cast, BitVec.getLsbD_replicate, tieDownX_getLsbD]
  simp [TritVec.replicate, TritVec.bit0, Vector.get, hi, Nat.mod_one]

@[simp, grind =] theorem hasUndef_replicate (n : Nat) (c : TritVec 1) :
    (TritVec.replicate n c).hasUndef =
      if n = 0 then false else (c.bits.get 0 == Trit.x) := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [TritVec.hasUndef, TritVec.replicate, Vector.toList_replicate, List.any_replicate,
        Nat.succ_ne_zero, ite_false, TritVec.bit0]
      rfl

@[simp, grind =] theorem replicate_ofBV (n : Nat) (b : BitVec 1) :
    TritVec.replicate n (ofBV b) =
      ofBV (BitVec.cast (Nat.one_mul n) (BitVec.replicate n b)) := by
  apply ext_nat
  intro i hi
  simp [TritVec.replicate, TritVec.bit0, Vector.get, BitVec.getElem_cast,
    BitVec.getElem_replicate, Nat.mod_one]

theorem shlStride_ofBV (a : BitVec w) (m : BitVec k) (stride : Nat)
    (hw : w ≤ 2 ^ 32) (hs : 1 ≤ stride) :
    TritVec.shlStride stride (ofBV a) (ofBV m) =
      ofBV (a <<< stridedAmount m stride) := by
  rw [BitVec.shiftLeft_eq', stridedAmount_toNat]
  unfold TritVec.shlStride TritVec.shiftBy
  rw [hasUndef_ofBV, shiftAmount?_ofBV]
  by_cases hm : m.toNat < 2 ^ 32
  · simp only [hm, Bool.false_eq_true, ite_false, ite_true]
    split
    · rw [BitVec.shiftLeft_eq_zero (by omega)]
      exact ext_nat fun i hi => by simp
    · apply ext_nat
      intro i hi
      simp only [Vector.getElem_ofFn, ofBV_bits, BitVec.getElem_shiftLeft]
      by_cases hle : m.toNat * stride ≤ i
      · simp [hle, show ¬ i < m.toNat * stride by omega]
      · simp [hle, show i < m.toNat * stride by omega]
  · have hge : 2 ^ 32 ≤ m.toNat * stride := by
      have hm32 : 2 ^ 32 ≤ m.toNat := Nat.le_of_not_lt hm
      exact Nat.le_trans hm32 (by simpa using Nat.mul_le_mul_left m.toNat hs)
    simp only [hm, Bool.false_eq_true, ite_false]
    rw [BitVec.shiftLeft_eq_zero (by omega)]
    exact ext_nat fun i hi => by simp


@[simp, grind =] theorem shlStride_ofBV_nat (a : BitVec w) (m : BitVec k) (stride : Nat)
    (hw : w ≤ 2 ^ 32) (hs : 1 ≤ stride) :
    TritVec.shlStride stride (ofBV a) (ofBV m) = ofBV (a <<< (m.toNat * stride)) := by
  rw [shlStride_ofBV _ _ _ hw hs, BitVec.shiftLeft_eq', stridedAmount_toNat]

theorem ushrStride_ofBV (a : BitVec w) (m : BitVec k) (stride : Nat)
    (hw : w ≤ 2 ^ 32) (hs : 1 ≤ stride) :
    TritVec.ushrStride stride (ofBV a) (ofBV m) =
      ofBV (a >>> stridedAmount m stride) := by
  rw [BitVec.ushiftRight_eq', stridedAmount_toNat]
  unfold TritVec.ushrStride TritVec.shiftBy
  rw [hasUndef_ofBV, shiftAmount?_ofBV]
  by_cases hm : m.toNat < 2 ^ 32
  · simp only [hm, Bool.false_eq_true, ite_false, ite_true]
    split
    · rw [BitVec.ushiftRight_eq_zero (by omega)]
      exact ext_nat fun i hi => by simp
    · apply ext_nat
      intro i hi
      simp only [Vector.getElem_ofFn, ofBV_bits, BitVec.getElem_ushiftRight]
      by_cases hlt : i + m.toNat * stride < w
      · simp [hlt, Nat.add_comm]
      · simp [hlt, BitVec.getLsbD_of_ge a _ (show w ≤ m.toNat * stride + i by omega)]
  · have hge : 2 ^ 32 ≤ m.toNat * stride := by
      have hm32 : 2 ^ 32 ≤ m.toNat := Nat.le_of_not_lt hm
      exact Nat.le_trans hm32 (by simpa using Nat.mul_le_mul_left m.toNat hs)
    simp only [hm, Bool.false_eq_true, ite_false]
    rw [BitVec.ushiftRight_eq_zero (by omega)]
    exact ext_nat fun i hi => by simp


@[simp, grind =] theorem ushrStride_ofBV_nat (a : BitVec w) (m : BitVec k) (stride : Nat)
    (hw : w ≤ 2 ^ 32) (hs : 1 ≤ stride) :
    TritVec.ushrStride stride (ofBV a) (ofBV m) = ofBV (a >>> (m.toNat * stride)) := by
  rw [ushrStride_ofBV _ _ _ hw hs, BitVec.ushiftRight_eq', stridedAmount_toNat]

theorem sshrStride_ofBV (a : BitVec w) (m : BitVec k) (stride : Nat)
    (hw : w ≤ 2 ^ 32) (hs : 1 ≤ stride) :
    TritVec.sshrStride stride (ofBV a) (ofBV m) =
      ofBV (a.sshiftRight' (stridedAmount m stride)) := by
  cases w with
  | zero => exact ext_nat fun i hi => absurd hi (by omega)
  | succ n =>
    rw [BitVec.sshiftRight_eq', stridedAmount_toNat]
    unfold TritVec.sshrStride TritVec.shiftBy
    rw [hasUndef_ofBV, shiftAmount?_ofBV, sign_ofBV]
    by_cases hm : m.toNat < 2 ^ 32
    · simp only [hm, Bool.false_eq_true, ite_false, ite_true]
      split
      · exact ext_nat fun i hi => by
          simp [BitVec.getElem_sshiftRight, show ¬ m.toNat * stride + i < n + 1 by omega]
      · apply ext_nat
        intro i hi
        simp only [Vector.getElem_ofFn, ofBV_bits, BitVec.getElem_sshiftRight]
        by_cases hlt : i + m.toNat * stride < n + 1
        · simp [hlt, Nat.add_comm]
        · simp [hlt, show ¬ m.toNat * stride + i < n + 1 by omega]
    · have hge : 2 ^ 32 ≤ m.toNat * stride := by
        have hm32 : 2 ^ 32 ≤ m.toNat := Nat.le_of_not_lt hm
        exact Nat.le_trans hm32 (by simpa using Nat.mul_le_mul_left m.toNat hs)
      simp only [hm, Bool.false_eq_true, ite_false]
      exact ext_nat fun i hi => by
        simp [BitVec.getElem_sshiftRight, show ¬ m.toNat * stride + i < n + 1 by omega]


@[simp, grind =] theorem sshrStride_ofBV_nat (a : BitVec w) (m : BitVec k) (stride : Nat)
    (hw : w ≤ 2 ^ 32) (hs : 1 ≤ stride) :
    TritVec.sshrStride stride (ofBV a) (ofBV m) = ofBV (a.sshiftRight (m.toNat * stride)) := by
  rw [sshrStride_ofBV _ _ _ hw hs, BitVec.sshiftRight_eq', stridedAmount_toNat]

end TritVec

end Grounding.Rtl
