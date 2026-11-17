-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Dual-rail encoding of the shifts, including the strided (barrel) forms.
-/

import Grounding.Tactic.DualRail.Rail.Basic
import Grounding.Tactic.DualRail.KitchenSink

namespace Grounding.Rtl.Rail

open TritVec

attribute [local simp] Trit.beq_eq_decide

/-! ### Shifts (any X in the amount ↦ all X) -/

theorem shl {a : TritVec w} {m : TritVec k} {xa va xm vm} (hw : w ≤ 2 ^ 32)
    (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.shl m) (bif xm != 0#k then BitVec.allOnes w else xa <<< vm)
      (bif xm != 0#k then 0#w else va <<< vm) := by
  by_cases h : (xm != 0#k) = true
  · rw [TritVec.shl, shiftBy_of_hasUndef _ _ _ _ (by rw [hasUndef_iff hm]; exact h)]
    simpa [h] using undef w
  · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    simp only [h, bne_self_eq_false, Bool.cond_false]
    have hmo : m = TritVec.ofBV vm := by
      rw [← tieDownX_eq hm h, ofBV_tieDownX (by rw [hasUndef_iff hm, h]; rfl)]
    subst hmo
    unfold TritVec.shl shiftBy
    rw [hasUndef_ofBV, shiftAmount?_ofBV]
    simp only [Bool.false_eq_true, ite_false]
    by_cases hlt : vm.toNat < 2 ^ 32
    · have hge : ¬ 4294967296 ≤ vm.toNat := by omega
      simp [hlt, hge]
      refine mk (fun i hi => ?_) (fun i hi hx => ?_)
      · simp only [Vector.getElem_ofFn, BitVec.getElem_shiftLeft]
        by_cases hs : vm.toNat ≤ i
        · simp [hs, show ¬ i < vm.toNat by omega, Vector.get, rail_bit ha (i - vm.toNat) (by omega)]
        · simp [hs, show i < vm.toNat by omega, trit]
      · simp only [BitVec.getElem_shiftLeft] at hx ⊢
        by_cases hs : i < vm.toNat
        · simp [hs]
        · simp only [hs, decide_false, Bool.not_false, Bool.true_and] at hx ⊢
          exact rail_norm ha _ _ hx
    · simp only [hlt, ite_false]
      rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_zero (by omega),
        BitVec.shiftLeft_eq_zero (by omega)]
      exact mk (fun i hi => by simp [trit]) (fun i hi h => by simp at h)

theorem ushr {a : TritVec w} {m : TritVec k} {xa va xm vm} (hw : w ≤ 2 ^ 32)
    (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.ushr m) (bif xm != 0#k then BitVec.allOnes w else xa >>> vm)
      (bif xm != 0#k then 0#w else va >>> vm) := by
  by_cases h : (xm != 0#k) = true
  · rw [TritVec.ushr, shiftBy_of_hasUndef _ _ _ _ (by rw [hasUndef_iff hm]; exact h)]
    simpa [h] using undef w
  · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    simp only [h, bne_self_eq_false, Bool.cond_false]
    have hmo : m = TritVec.ofBV vm := by
      rw [← tieDownX_eq hm h, ofBV_tieDownX (by rw [hasUndef_iff hm, h]; rfl)]
    subst hmo
    unfold TritVec.ushr shiftBy
    rw [hasUndef_ofBV, shiftAmount?_ofBV]
    simp only [Bool.false_eq_true, ite_false]
    by_cases hlt : vm.toNat < 2 ^ 32
    · have hge : ¬ 4294967296 ≤ vm.toNat := by omega
      simp [hlt, hge]
      refine mk (fun i hi => ?_) (fun i hi hx => ?_)
      · simp only [Vector.getElem_ofFn, BitVec.getElem_ushiftRight]
        by_cases hs : i + vm.toNat < w
        · simp [hs, Vector.get, rail_bit ha (i + vm.toNat) hs, Nat.add_comm]
        · simp [hs, trit, BitVec.getLsbD_of_ge _ _ (show w ≤ vm.toNat + i by omega)]
      · simp only [BitVec.getElem_ushiftRight] at hx ⊢
        by_cases hs : vm.toNat + i < w
        · rw [BitVec.getLsbD_eq_getElem hs] at hx ⊢; exact rail_norm ha _ _ hx
        · simp [BitVec.getLsbD_of_ge _ _ (show w ≤ vm.toNat + i by omega)] at hx
    · simp only [hlt, ite_false]
      rw [BitVec.ushiftRight_eq', BitVec.ushiftRight_eq', BitVec.ushiftRight_eq_zero (by omega),
        BitVec.ushiftRight_eq_zero (by omega)]
      exact mk (fun i hi => by simp [trit]) (fun i hi h => by simp at h)

/-- A right shift by a defined amount with fill trit `trit fx fv`: bit `i` of
the result rails is bit `vm + i` of the operand rails, or the fill beyond the
top. `X`, `Y` are any bit-vectors with exactly these bits. -/
theorem shiftR_rail {a : TritVec w} {xa va : BitVec w} (vm : BitVec k) (fx fv : Bool)
    (hw : w ≤ 2 ^ 32) (hnf : fx = true → fv = false) (ha : Rail a xa va) (X Y : BitVec w)
    (hX : ∀ i (hi : i < w), X[i] = if h : vm.toNat + i < w then xa[vm.toNat + i] else fx)
    (hY : ∀ i (hi : i < w), Y[i] = if h : vm.toNat + i < w then va[vm.toNat + i] else fv) :
    Rail (shiftBy false (trit fx fv) 1 a (TritVec.ofBV vm)) X Y := by
  unfold shiftBy
  rw [hasUndef_ofBV, shiftAmount?_ofBV]
  simp only [Bool.false_eq_true, ite_false]
  by_cases hlt : vm.toNat < 2 ^ 32
  · have hge : ¬ 4294967296 ≤ vm.toNat := by omega
    simp [hlt, hge]
    refine mk (fun i hi => ?_) (fun i hi hx => ?_)
    · simp only [Vector.getElem_ofFn, hX i hi, hY i hi]
      by_cases hs : i + vm.toNat < w
      · simp [hs, Vector.get, rail_bit ha (i + vm.toNat) hs, Nat.add_comm]
      · simp [hs, show ¬ vm.toNat + i < w by omega]
    · rw [hX i hi] at hx
      rw [hY i hi]
      by_cases hs : vm.toNat + i < w
      · simp only [hs, dite_true] at hx ⊢; exact rail_norm ha _ _ hx
      · simp only [hs, dite_false] at hx ⊢; exact hnf hx
  · simp only [hlt, ite_false]
    have hw' : ∀ i, i < w → ¬ vm.toNat + i < w := fun i hi h => by
      have h32 : 2 ^ 32 ≤ vm.toNat := Nat.le_of_not_lt hlt
      omega
    exact mk (fun i hi => by simp [hX i hi, hY i hi, hw' i hi])
      (fun i hi hx => by
        simp only [hX i hi, hw' i hi, dite_false] at hx; simp [hY i hi, hw' i hi, hnf hx])

theorem sign_rail {a : TritVec (n + 1)} {xa va : BitVec (n + 1)} (ha : Rail a xa va) :
    TritVec.sign a = trit xa.msb va.msb ∧ (xa.msb = true → va.msb = false) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last,
    BitVec.getLsbD_eq_getElem (by omega), BitVec.getLsbD_eq_getElem (by omega)]
  refine ⟨?_, rail_norm ha _ _⟩
  simp only [TritVec.sign, Nat.add_one_ne_zero, dite_false, Vector.get]
  exact rail_bit ha n (by omega)

/-- Any width-0 constant is encoded by any width-0 rails. -/
theorem rail_zero (c : TritVec 0) (x v : BitVec 0) : Rail c x v :=
  mk (fun i hi => absurd hi (by omega)) (fun i hi => absurd hi (by omega))

/-- Defined shift amount from its rails. -/
theorem ofBV_of_rail {m : TritVec k} {xm vm : BitVec k} (hm : Rail m xm vm) (h : xm = 0#k) :
    m = TritVec.ofBV vm := by
  rw [← tieDownX_eq hm h, ofBV_tieDownX (by rw [hasUndef_iff hm, h]; rfl)]

theorem sshr {a : TritVec w} {m : TritVec k} {xa va xm vm} (hw : w ≤ 2 ^ 32)
    (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.sshr m) (bif xm != 0#k then BitVec.allOnes w else xa.sshiftRight' vm)
      (bif xm != 0#k then 0#w else va.sshiftRight' vm) := by
  by_cases h : (xm != 0#k) = true
  · rw [TritVec.sshr, shiftBy_of_hasUndef _ _ _ _ (by rw [hasUndef_iff hm]; exact h)]
    simpa [h] using undef w
  · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    simp only [h, bne_self_eq_false, Bool.cond_false]
    cases w with
    | zero => exact rail_zero _ _ _
    | succ n =>
    rw [ofBV_of_rail hm h, TritVec.sshr, (sign_rail ha).1]
    apply shiftR_rail vm _ _ hw (sign_rail ha).2 ha
    · intro i hi
      show (xa.sshiftRight vm.toNat)[i] = _
      exact BitVec.getElem_sshiftRight hi
    · intro i hi
      show (va.sshiftRight vm.toNat)[i] = _
      exact BitVec.getElem_sshiftRight hi

theorem xshr {a : TritVec w} {m : TritVec k} {xa va xm vm} (hw : w ≤ 2 ^ 32)
    (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.xshr m) (bif xm != 0#k then BitVec.allOnes w else
        (xa >>> vm) ||| ~~~(BitVec.allOnes w >>> vm))
      (bif xm != 0#k then 0#w else va >>> vm) := by
  by_cases h : (xm != 0#k) = true
  · rw [TritVec.xshr, shiftBy_of_hasUndef _ _ _ _ (by rw [hasUndef_iff hm]; exact h)]
    simpa [h] using undef w
  · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    simp only [h, bne_self_eq_false, Bool.cond_false]
    rw [ofBV_of_rail hm h, TritVec.xshr, show Trit.x = trit true false from rfl]
    apply shiftR_rail vm true false hw (by simp) ha
    · intro i hi
      simp only [BitVec.ushiftRight_eq', BitVec.getElem_or, BitVec.getElem_ushiftRight,
        BitVec.getElem_not, BitVec.getLsbD_allOnes]
      by_cases hs : vm.toNat + i < w
      · simp [hs]
      · simp [hs, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hs)]
    · intro i hi
      simp only [BitVec.ushiftRight_eq', BitVec.getElem_ushiftRight]
      by_cases hs : vm.toNat + i < w
      · simp [hs]
      · simp [hs, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hs)]

/-! ### Strided shifts (reduced to stride 1 by the amount `m * stride`) -/

theorem shiftBy_stride (left : Bool) (f : Trit) (a : TritVec w) (m : BitVec k) {stride : Nat}
    (hs : 1 ≤ stride) :
    shiftBy left f stride a (TritVec.ofBV m) =
      shiftBy left f 1 a (TritVec.ofBV (stridedAmount m stride)) := by
  unfold shiftBy
  simp only [hasUndef_ofBV, shiftAmount?_ofBV, stridedAmount_toNat, Nat.mul_one]
  have hle : m.toNat ≤ m.toNat * stride := Nat.le_mul_of_pos_right _ hs
  by_cases h1 : m.toNat < 2 ^ 32
  · by_cases h2 : m.toNat * stride < 2 ^ 32
    · simp [h1, h2]
    · simp [h1, h2, Nat.le_of_not_lt h2]
  · have h2 : ¬ m.toNat * stride < 2 ^ 32 := by omega
    simp [h1, h2]

theorem shiftBy_strided (left : Bool) (f : Trit) (a : TritVec w) {m : TritVec k} {xm vm : BitVec k}
    {stride : Nat} (hs : 1 ≤ stride) (hm : Rail m xm vm) :
    shiftBy left f stride a m =
      bif xm != 0#k then TritVec.undef w
      else shiftBy left f 1 a (TritVec.ofBV (stridedAmount vm stride)) := by
  by_cases h : (xm != 0#k) = true
  · rw [shiftBy_of_hasUndef _ _ _ _ (by rw [hasUndef_iff hm]; exact h), h]; rfl
  · simp only [Bool.not_eq_true] at h
    rw [h, Bool.cond_false]
    simp only [bne_eq_false_iff_eq] at h
    rw [ofBV_of_rail hm h, shiftBy_stride _ _ _ _ hs]

/-- Barrel shifter: stage `j` shifts by the literal `stride * 2 ^ j` iff bit `j`
of the amount is set (one mux per amount bit, no multiplication). -/
def barrel (sh : Nat → BitVec w → BitVec w) (vm : BitVec k) (stride : Nat) :
    Nat → BitVec w → BitVec w
  | 0, x => x
  | j + 1, x => bif vm.getLsbD j then sh (stride * 2 ^ j) (barrel sh vm stride j x)
      else barrel sh vm stride j x

theorem barrel_spec (sh : Nat → BitVec w → BitVec w) (h0 : ∀ x, sh 0 x = x)
    (hadd : ∀ a b x, sh b (sh a x) = sh (a + b) x) (vm : BitVec k) (stride : Nat) :
    ∀ j x, barrel sh vm stride j x = sh (vm.toNat % 2 ^ j * stride) x
  | 0, x => by simp [barrel, Nat.mod_one, h0]
  | j + 1, x => by
    rw [barrel, barrel_spec sh h0 hadd vm stride j x, Nat.mod_pow_succ, ← BitVec.testBit_toNat,
      Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (vm.toNat / 2 ^ j) with h | h
    · simp [h]
    · simp only [h, decide_true, Bool.cond_true, hadd]
      congr 1
      rw [Nat.add_mul, Nat.mul_one, Nat.mul_comm (2 ^ j)]

theorem barrel_full (sh : Nat → BitVec w → BitVec w) (h0 : ∀ x, sh 0 x = x)
    (hadd : ∀ a b x, sh b (sh a x) = sh (a + b) x) (vm : BitVec k) (stride : Nat) (x : BitVec w) :
    barrel sh vm stride k x = sh (vm.toNat * stride) x := by
  rw [barrel_spec sh h0 hadd, Nat.mod_eq_of_lt vm.isLt]

theorem shlStride {a : TritVec w} {m : TritVec k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.shlStride stride m)
      (bif xm != 0#k then BitVec.allOnes w else barrel (fun n x => x <<< n) vm stride k xa)
      (bif xm != 0#k then 0#w else barrel (fun n x => x <<< n) vm stride k va) := by
  rw [TritVec.shlStride, shiftBy_strided _ _ _ hs hm]
  cases xm != 0#k
  · have := shl hw ha (Rail.ofBV (stridedAmount vm stride))
    simp only [bne_self_eq_false, Bool.cond_false, BitVec.shiftLeft_eq', stridedAmount_toNat] at this
    have hb := barrel_full (fun n (x : BitVec w) => x <<< n) (fun x => BitVec.shiftLeft_zero x)
      (fun a b x => (BitVec.shiftLeft_add x a b).symm) vm stride
    simp only [Bool.cond_false, hb]
    exact this
  · exact undef w

theorem ushrStride {a : TritVec w} {m : TritVec k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.ushrStride stride m)
      (bif xm != 0#k then BitVec.allOnes w else barrel (fun n x => x >>> n) vm stride k xa)
      (bif xm != 0#k then 0#w else barrel (fun n x => x >>> n) vm stride k va) := by
  rw [TritVec.ushrStride, shiftBy_strided _ _ _ hs hm]
  cases xm != 0#k
  · have := ushr hw ha (Rail.ofBV (stridedAmount vm stride))
    simp only [bne_self_eq_false, Bool.cond_false, BitVec.ushiftRight_eq', stridedAmount_toNat]
      at this
    have hb := barrel_full (fun n (x : BitVec w) => x >>> n) (fun x => BitVec.ushiftRight_zero x)
      (fun a b x => (BitVec.shiftRight_add x a b).symm) vm stride
    simp only [Bool.cond_false, hb]
    exact this
  · exact undef w

theorem sshrStride {a : TritVec w} {m : TritVec k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.sshrStride stride m)
      (bif xm != 0#k then BitVec.allOnes w else
        barrel (fun n x => x.sshiftRight n) vm stride k xa)
      (bif xm != 0#k then 0#w else barrel (fun n x => x.sshiftRight n) vm stride k va) := by
  rw [TritVec.sshrStride, shiftBy_strided _ _ _ hs hm]
  cases xm != 0#k
  · have := sshr hw ha (Rail.ofBV (stridedAmount vm stride))
    simp only [bne_self_eq_false, Bool.cond_false, BitVec.sshiftRight_eq', stridedAmount_toNat]
      at this
    have hb := barrel_full (fun n (x : BitVec w) => x.sshiftRight n)
      (fun x => BitVec.sshiftRight_zero) (fun a b x => BitVec.sshiftRight_add.symm) vm stride
    simp only [Bool.cond_false, hb]
    exact this
  · exact undef w

theorem xshr_mask_eq (xa : BitVec w) (s : Nat) :
    (xa >>> s) ||| ~~~(BitVec.allOnes w >>> s) = ~~~(~~~xa >>> s) := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_ushiftRight,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_not]
  by_cases h : s + i < w
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt h)]

theorem xshrStride {a : TritVec w} {m : TritVec k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : Rail a xa va) (hm : Rail m xm vm) :
    Rail (a.xshrStride stride m)
      (bif xm != 0#k then BitVec.allOnes w else
        barrel (fun n x => ~~~(~~~x >>> n)) vm stride k xa)
      (bif xm != 0#k then 0#w else barrel (fun n x => x >>> n) vm stride k va) := by
  rw [TritVec.xshrStride, shiftBy_strided _ _ _ hs hm]
  cases xm != 0#k
  · have := xshr hw ha (Rail.ofBV (stridedAmount vm stride))
    simp only [bne_self_eq_false, Bool.cond_false, BitVec.ushiftRight_eq', stridedAmount_toNat,
      xshr_mask_eq] at this
    have hb := barrel_full (fun n (x : BitVec w) => x >>> n) (fun x => BitVec.ushiftRight_zero x)
      (fun a b x => (BitVec.shiftRight_add x a b).symm) vm stride
    have hbx := barrel_full (fun n (x : BitVec w) => ~~~(~~~x >>> n))
      (fun x => by simp) (fun a b x => by simp [BitVec.shiftRight_add]) vm stride
    simp only [Bool.cond_false, hb, hbx]
    exact this
  · exact undef w

end Grounding.Rtl.Rail
