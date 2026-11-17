-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Arithmetic of the Ibex slow multiplier, restated as window invariants on the
datapath registers (`MullWin`, `MulhWin`):

* MULL: after the IDLE load and `j` COMP steps, `op_a_shift = A << (j+1)`,
  `op_b_shift = B >> (j+1)` and `accum[31:0] = a * (b mod 2^(j+1))`.
* MULH (Baugh-Wooley, 33-bit operands): `op_a_shift = A`,
  `op_b_shift = B >> (j+1)` and `accum·2^(j+1) + low = Σ_{i≤j} pp_i·2^i + 2^33`
  for some `low < 2^(j+1)` (the bits shifted out).
-/
import Std.Tactic.BVDecide

namespace IbexMultidivSlow

/-! ### Datapath vocabulary (the RTL formulas as `BitVec` functions) -/

/-- `op_a_ext` / `op_b_ext`: `{x[31] & signed, x}`. -/
def ext33 (s : Bool) (x : BitVec 32) : BitVec 33 := BitVec.ofBool (s && x.msb) ++ x

/-- Baugh-Wooley partial product `op_a_bw_pp`: `b0 ? pa : 0` with bit 32 inverted. -/
def bwpp (pa : BitVec 33) (b0 : Bool) : BitVec 33 := (bif b0 then pa else 0#33) ^^^ 0x100000000#33

/-- The ALU's 34-bit sum `{1'b0, x} + {1'b0, y}`. -/
def add34 (x y : BitVec 33) : BitVec 34 := x.setWidth 34 + y.setWidth 34

/-- 64-bit operand extension (signed or zero) for the high half of the product. -/
def extendVal (signed : Bool) (x : BitVec 32) : BitVec 64 :=
  if signed then BitVec.signExtend 64 x else BitVec.setWidth 64 x

/-- MULL is the low 32 bits of the product; MULH is the high 32 bits of the
product of the operands extended per their signedness. -/
def mulSpec (hi sa sb : Bool) (a b : BitVec 32) : BitVec 32 :=
  if hi then ((extendVal sa a) * (extendVal sb b)).extractLsb' 32 32 else a * b

/-- The LAST-state result: `accum` plus the last partial product (inverted for
MULH), low 32 bits. -/
def lastResult (hi : Bool) (pa pb acc : BitVec 33) : BitVec 32 :=
  (acc + bif hi then ~~~(bwpp pa (pb.getLsbD 0)) else bwpp pa (pb.getLsbD 0)).extractLsb' 0 32

theorem mod_two_pow_succ (b j : Nat) :
    b % 2 ^ (j + 1) = b % 2 ^ j + (bif b.testBit j then 2 ^ j else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ j) with h | h <;> simp [h]

theorem ext33_low (s : Bool) (x : BitVec 32) : (ext33 s x).setWidth 32 = x := by
  unfold ext33; bv_decide

theorem ext33_bit (s : Bool) (x : BitVec 32) {i : Nat} (hi : i < 32) :
    (ext33 s x).getLsbD i = x.getLsbD i := by
  have := congrArg (·.getLsbD i) (ext33_low s x)
  simpa [BitVec.getLsbD_setWidth, hi] using this

theorem bwpp_low (pa : BitVec 33) (c : Bool) :
    (bwpp pa c).setWidth 32 = (bif c then pa.setWidth 32 else 0#32) := by
  unfold bwpp; cases c <;> simp <;> bv_decide

theorem extract0_eq_setWidth (x : BitVec 33) : x.extractLsb' 0 32 = x.setWidth 32 := by
  ext i hi; simp

/-- The MULH partial products, as naturals. -/
def ppN (A B : BitVec 33) (i : Nat) : Nat := (bwpp A (B.getLsbD i)).toNat

/-- `Σ_{i<k} ppN A B i * 2^i`. -/
def ppSum (A B : BitVec 33) : Nat → Nat
  | 0 => 0
  | k + 1 => ppSum A B k + ppN A B k * 2 ^ k

/-- A partial product as an integer: `c·A + 2^32` (`A` signed). -/
theorem bwpp_int (A : BitVec 33) (c : Bool) :
    ((bwpp A c).toNat : Int) = (bif c then A.toInt else 0) + 2 ^ 32 := by
  have key : ∀ x : BitVec 33, ((x ^^^ 0x100000000#33).toNat : Int) = x.toInt + 2 ^ 32 := by
    intro x
    rw [BitVec.toInt_eq_msb_cond]
    have hx := x.isLt
    by_cases hm : x.msb = true
    · have : x ^^^ 0x100000000#33 = x - 0x100000000#33 := by
        revert hm; bv_decide
      rw [this, BitVec.toNat_sub]
      have : 2 ^ 32 ≤ x.toNat := by
        have := (BitVec.msb_eq_true_iff_two_mul_ge (x := x)).1 hm; simp at this; omega
      simp [hm]; omega
    · have : x ^^^ 0x100000000#33 = x + 0x100000000#33 := by
        revert hm; bv_decide
      rw [this, BitVec.toNat_add]
      have : x.toNat < 2 ^ 32 := by
        have := (BitVec.msb_eq_false_iff_two_mul_lt (x := x)).1 (by simpa using hm); simp at this; omega
      simp [hm]; omega
  unfold bwpp
  cases c
  · rw [Bool.cond_false, key]; simp
  · rw [Bool.cond_true, key]; simp

/-- The sum of the first `k` partial products, as an integer. -/
theorem ppSum_int (A B : BitVec 33) (k : Nat) :
    (ppSum A B k : Int) = A.toInt * ((B.toNat % 2 ^ k : Nat) : Int) + (2 ^ k - 1) * 2 ^ 32 := by
  induction k with
  | zero => simp [ppSum]
  | succ k ih =>
    rw [ppSum, Int.natCast_add, Int.natCast_mul, ih, ppN, bwpp_int, mod_two_pow_succ, BitVec.testBit_toNat]
    cases B.getLsbD k <;> simp <;> grind

theorem ext33_toInt (s : Bool) (x : BitVec 32) :
    (ext33 s x).toInt = if s then x.toInt else (x.toNat : Int) := by
  have hz : ∀ x : BitVec 32, (ext33 false x) = x.setWidth 33 := by intro x; unfold ext33; bv_decide
  have hs : ∀ x : BitVec 32, (ext33 true x) = x.signExtend 33 := by intro x; unfold ext33; bv_decide
  cases s
  · rw [hz, BitVec.toInt_setWidth]; simp
    have := x.isLt
    rw [Int.bmod_eq_of_le] <;> omega
  · rw [hs, BitVec.toInt_signExtend_of_le (by omega)]; rfl

/-- `extendVal` as a 64-bit value of the integer operand. -/
theorem extendVal_eq (s : Bool) (x : BitVec 32) :
    extendVal s x = BitVec.ofInt 64 (ext33 s x).toInt := by
  rw [ext33_toInt]
  unfold extendVal
  cases s
  · simp only [Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    simp
  · simp only [ite_true]
    rw [← BitVec.toInt_signExtend_of_le (v := 64) (x := x) (by omega), BitVec.ofInt_toInt]

theorem toInt_split (B : BitVec 33) :
    B.toInt = ((B.setWidth 32).toNat : Int) - (bif B.getLsbD 32 then 2 ^ 32 else 0) := by
  rw [BitVec.toInt_eq_msb_cond, BitVec.toNat_setWidth]
  have hm : B.msb = B.getLsbD 32 := by simp [BitVec.msb_eq_getLsbD_last]
  have h := mod_two_pow_succ B.toNat 32
  rw [BitVec.testBit_toNat, Nat.mod_eq_of_lt B.isLt] at h
  rw [hm]
  cases hb : B.getLsbD 32 <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h ⊢ <;> simp <;> omega

/-- The last MULH step in bits: `(acc + ~p)[31:0]` is bits 32..63 of the full
sum `acc·2^32 + low + (~p)·2^32`. -/
theorem last_bits (acc p : BitVec 33) (low : Nat) (hlow : low < 2 ^ 32) :
    ((acc + ~~~p).extractLsb' 0 32).toNat =
      ((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low) % 2 ^ 64 / 2 ^ 32 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_add, Nat.shiftRight_zero]
  have h1 : ((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low) % 2 ^ 64 / 2 ^ 32 =
      (acc.toNat + (~~~p).toNat) % 2 ^ 32 := by
    generalize acc.toNat + (~~~p).toNat = n
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mod_mul_right_div_self,
      Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [h1, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 33)]

/-! ### MULL -/

def MullWin (sa sb : Bool) (a b : BitVec 32) (j : Nat) (pa pb acc : BitVec 33) : Prop :=
  pa = ext33 sa a <<< (j + 1) ∧ pb = ext33 sb b >>> (j + 1) ∧
  acc.setWidth 32 = a * (b.setWidth (j + 1)).setWidth 32

theorem MullWin.zero (sa sb : Bool) (a b : BitVec 32) :
    MullWin sa sb a b 0 (ext33 sa a <<< 1) (ext33 sb b >>> 1) (bwpp (ext33 sa a) (b.getLsbD 0)) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [bwpp_low, ← BitVec.mulRec_eq_mul_signExtend_setWidth, BitVec.mulRec_zero_eq,
    ext33_low]
  cases b.getLsbD 0 <;> rfl

theorem MullWin.step {sa sb : Bool} {a b : BitVec 32} {j : Nat} {pa pb acc : BitVec 33}
    (hj : j < 31) (h : MullWin sa sb a b j pa pb acc) :
    MullWin sa sb a b (j + 1) (pa <<< 1) (pb >>> 1) (acc + bwpp pa (pb.getLsbD 0)) := by
  obtain ⟨hpa, hpb, hacc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [hpa, ← BitVec.shiftLeft_add]
  · rw [hpb, ← BitVec.shiftRight_add]
  · rw [BitVec.setWidth_add _ _ (show 32 ≤ 33 by omega), hacc, bwpp_low, hpa, hpb,
      BitVec.getLsbD_ushiftRight, Nat.add_zero, ext33_bit sb b (show j + 1 < 32 by omega)]
    rw [← BitVec.mulRec_eq_mul_signExtend_setWidth, ← BitVec.mulRec_eq_mul_signExtend_setWidth,
      BitVec.mulRec_succ_eq]
    congr 1
    have hsh : (ext33 sa a <<< (j + 1)).setWidth 32 = a <<< (j + 1) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
      by_cases h : i < j + 1
      · simp [h]
      · have hi33 : i < 33 := by omega
        have := ext33_bit sa a (i := i - (j + 1)) (by omega)
        simp [h, hi33, this]
    cases b.getLsbD (j + 1) <;> simp [hsh]

/-- When LAST is reached (the shifted multiplier is zero, or all 31 COMP steps
are done) the window holds the product. -/
theorem MullWin.result {sa sb : Bool} {a b : BitVec 32} {j : Nat} {pa pb acc : BitVec 33}
    (hj : j < 32) (h : MullWin sa sb a b j pa pb acc) (hend : pb = 0#33 ∨ j = 31) :
    lastResult false pa pb acc = a * b := by
  obtain ⟨hpa, hpb, hacc⟩ := h
  have hbz : ∀ i, j < i → i < 32 → b.getLsbD i = false := by
    rcases hend with hz | rfl
    · intro i h1 h2
      have := congrArg (·.getLsbD (i - (j + 1))) (hpb.symm.trans hz)
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero] at this
      rw [show j + 1 + (i - (j + 1)) = i by omega, ext33_bit sb b h2] at this
      exact this
    · intro i h1 h2; omega
  have hpp : pa.setWidth 32 = 0#32 ∨ pb = 0#33 := by
    rcases hend with hz | rfl
    · exact Or.inr hz
    · exact Or.inl (by rw [hpa]; ext i hi; simp)
  have hb : (b.setWidth (j + 1)).setWidth 32 = b := by
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth]
    rw [← BitVec.getLsbD_eq_getElem]
    by_cases h : i < j + 1
    · simp [h]
    · simp [h, hbz i (by omega) hi]
  unfold lastResult
  rw [Bool.cond_false, extract0_eq_setWidth, BitVec.setWidth_add _ _ (by omega), hacc, hb,
    bwpp_low]
  rcases hpp with hz | hz <;> rw [hz] <;> cases pb.getLsbD 0 <;> simp

/-! ### MULH (Baugh-Wooley) -/

def MulhWin (sa sb : Bool) (a b : BitVec 32) (j : Nat) (pa pb acc : BitVec 33) : Prop :=
  pa = ext33 sa a ∧ pb = ext33 sb b >>> (j + 1) ∧
  ∃ low < 2 ^ (j + 1),
    acc.toNat * 2 ^ (j + 1) + low = ppSum (ext33 sa a) (ext33 sb b) (j + 1) + 2 ^ 33

theorem MulhWin.zero (sa sb : Bool) (a b : BitVec 32) :
    MulhWin sa sb a b 0 (ext33 sa a) (ext33 sb b >>> 1)
      ((bwpp (ext33 sa a) (b.getLsbD 0) >>> 1) ||| 0x100000000#33) := by
  refine ⟨rfl, rfl, (bwpp (ext33 sa a) (b.getLsbD 0)).toNat % 2, by omega, ?_⟩
  have h1 : ((bwpp (ext33 sa a) (b.getLsbD 0) >>> 1) ||| 0x100000000#33).toNat =
      (bwpp (ext33 sa a) (b.getLsbD 0)).toNat / 2 + 2 ^ 32 := by
    have hor : ∀ x : BitVec 33, (x >>> 1) ||| 0x100000000#33 = (x >>> 1) + 0x100000000#33 := by
      intro x; bv_decide
    rw [hor, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (bwpp (ext33 sa a) (b.getLsbD 0)).isLt
    simp; omega
  simp only [ppSum, ppN, h1, ext33_bit sb b (show 0 < 32 by omega)]
  omega

theorem MulhWin.step {sa sb : Bool} {a b : BitVec 32} {j : Nat} {pa pb acc : BitVec 33}
    (h : MulhWin sa sb a b j pa pb acc) :
    MulhWin sa sb a b (j + 1) pa (pb >>> 1)
      ((add34 acc (bwpp pa (pb.getLsbD 0))).extractLsb' 1 33) := by
  obtain ⟨hpa, hpb, low, hlow, h⟩ := h
  subst hpa hpb
  refine ⟨rfl, by rw [← BitVec.shiftRight_add], ?_⟩
  generalize ext33 sa a = A at h ⊢
  generalize ext33 sb b = B at h ⊢
  let p := bwpp A ((B >>> (j + 1)).getLsbD 0)
  have hp : p.toNat = ppN A B (j + 1) := by simp [p, ppN, Nat.add_comm]
  have hs : (add34 acc p).toNat = acc.toNat + p.toNat := by
    unfold add34; rw [BitVec.toNat_add]; simp [BitVec.toNat_setWidth]
    have := acc.isLt; have := p.isLt; omega
  have hx : ((add34 acc p).extractLsb' 1 33).toNat = (acc.toNat + p.toNat) / 2 := by
    rw [BitVec.extractLsb'_toNat, hs, Nat.shiftRight_eq_div_pow]
    have := acc.isLt; have := p.isLt; simp; omega
  refine ⟨low + ((acc.toNat + p.toNat) % 2) * 2 ^ (j + 1), ?_, ?_⟩
  · have h2 : (acc.toNat + p.toNat) % 2 ≤ 1 := by omega
    have h3 : (acc.toNat + p.toNat) % 2 * 2 ^ (j + 1) ≤ 2 ^ (j + 1) :=
      Nat.le_trans (Nat.mul_le_mul_right _ h2) (by simp)
    rw [Nat.pow_succ 2 (j + 1)]; omega
  · rw [hx, ppSum, ← hp, Nat.pow_succ 2 (j + 1)]
    have hd := Nat.div_add_mod (acc.toNat + p.toNat) 2
    have h' : acc.toNat * 2 ^ (j + 1) + low = ppSum A B (j + 1) + 2 ^ 33 := h
    have e1 : (acc.toNat + p.toNat) / 2 * (2 ^ (j + 1) * 2) + (acc.toNat + p.toNat) % 2 * 2 ^ (j + 1)
        = (acc.toNat + p.toNat) * 2 ^ (j + 1) := by
      generalize acc.toNat + p.toNat = n at hd ⊢
      generalize 2 ^ (j + 1) = P
      conv => rhs; rw [← hd]
      rw [Nat.add_mul, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm (n / 2) 2, Nat.mul_assoc]
    calc (acc.toNat + p.toNat) / 2 * (2 ^ (j + 1) * 2) + (low + (acc.toNat + p.toNat) % 2 * 2 ^ (j + 1))
        = (acc.toNat + p.toNat) * 2 ^ (j + 1) + low := by omega
      _ = (acc.toNat * 2 ^ (j + 1) + low) + p.toNat * 2 ^ (j + 1) := by rw [Nat.add_mul]; omega
      _ = ppSum A B (j + 1) + p.toNat * 2 ^ (j + 1) + 2 ^ 33 := by rw [h']; omega

/-- MULH is the high half of the product, after all 31 COMP steps. -/
theorem MulhWin.result {sa sb : Bool} {a b : BitVec 32} {pa pb acc : BitVec 33}
    (h : MulhWin sa sb a b 31 pa pb acc) :
    lastResult true pa pb acc = ((extendVal sa a) * (extendVal sb b)).extractLsb' 32 32 := by
  obtain ⟨hpa, hpb, low, hlow, hinv⟩ := h
  rw [hpa, hpb, extendVal_eq, extendVal_eq, ← BitVec.ofInt_mul]
  generalize ext33 sa a = A at hinv ⊢
  generalize ext33 sb b = B at hinv ⊢
  unfold lastResult
  simp only [Bool.cond_true]
  have hbit : (B >>> (31 + 1)).getLsbD 0 = B.getLsbD 32 := by simp
  rw [hbit]
  generalize hp : bwpp A (B.getLsbD 32) = p
  have hpI : (p.toNat : Int) = (bif B.getLsbD 32 then A.toInt else 0) + 2 ^ 32 := by
    rw [← hp, bwpp_int]
  have hS := ppSum_int A B 32
  have hBI := toInt_split B
  rw [BitVec.toNat_setWidth] at hBI
  have hnot : ((~~~p).toNat : Int) = 2 ^ 33 - 1 - p.toNat := by
    rw [BitVec.toNat_not]; have := p.isLt; omega
  have hlow32 : low < 2 ^ 32 := by simpa using hlow
  have hinvI : (acc.toNat : Int) * 2 ^ 32 + low = A.toInt * ((B.toNat % 2 ^ 32 : Nat) : Int) +
      (2 ^ 32 - 1) * 2 ^ 32 + 2 ^ 33 := by
    have h1 : ((acc.toNat * 2 ^ (31 + 1) + low : Nat) : Int) = (ppSum A B 32 : Int) + 2 ^ 33 := by
      exact_mod_cast hinv
    rw [hS] at h1
    simpa using h1
  have htot : ((((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low : Nat) : Int)) =
      A.toInt * B.toInt + 2 ^ 64 * 2 := by
    have e : ((((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low : Nat) : Int)) =
        ((acc.toNat : Int) * 2 ^ 32 + low) + ((~~~p).toNat : Int) * 2 ^ 32 := by
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]; grind
    rw [e, hinvI, hnot, hpI, hBI]
    cases B.getLsbD 32 <;> simp only [Bool.cond_true, Bool.cond_false] <;> grind
  apply BitVec.eq_of_toNat_eq
  rw [last_bits acc p low hlow32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofInt]
  have hmod : ((((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low) % 2 ^ 64 : Nat) : Int) =
      (A.toInt * B.toInt) % ((2 ^ 64 : Nat) : Int) := by
    rw [Int.natCast_emod, htot]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    rw [Int.add_mul_emod_self_left]
  have hlt : ((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hq : ((acc.toNat + (~~~p).toNat) * 2 ^ 32 + low) % 2 ^ 64 =
      ((A.toInt * B.toInt) % ((2 ^ 64 : Nat) : Int)).toNat := by omega
  rw [hq]
  have : ((A.toInt * B.toInt) % ((2 ^ 64 : Nat) : Int)).toNat / 2 ^ 32 < 2 ^ 32 := by
    have h0 := Int.emod_nonneg (A.toInt * B.toInt) (show ((2 ^ 64 : Nat) : Int) ≠ 0 by decide)
    have h1 := Int.emod_lt_of_pos (A.toInt * B.toInt) (show (0 : Int) < ((2 ^ 64 : Nat) : Int) by decide)
    omega
  rw [Nat.mod_eq_of_lt this]

/-- The multiplier's result, MULL or MULH, from its final window. -/
theorem result_correct {hi sa sb : Bool} {a b : BitVec 32} {j : Nat} {pa pb acc : BitVec 33}
    (hj : j ≤ 31)
    (h : (hi = false ∧ MullWin sa sb a b j pa pb acc ∧ (pb = 0#33 ∨ j = 31)) ∨
         (hi = true ∧ MulhWin sa sb a b j pa pb acc ∧ j = 31)) :
    lastResult hi pa pb acc = mulSpec hi sa sb a b := by
  rcases h with ⟨rfl, hw, he⟩ | ⟨rfl, hw, rfl⟩
  · simpa [mulSpec] using MullWin.result (by omega) hw he
  · simpa [mulSpec] using MulhWin.result hw

end IbexMultidivSlow
