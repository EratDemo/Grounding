-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Evaluation-level rail lemmas: one per `Value` node (`Rail.Ev.*`), the `maskOf`/`valOf`
atoms, and the lemmas the tactic uses to close goals and read hypotheses.
-/

import Grounding.Tactic.DualRail.Rail.Basic
import Grounding.Tactic.DualRail.Rail.Adc
import Grounding.Tactic.DualRail.Rail.Compare
import Grounding.Tactic.DualRail.Rail.Shift
import Grounding.Tactic.DualRail.ValuationConcat

namespace Grounding.Rtl

/-- Peel the first assignment off a consistency hypothesis over a literal list. -/
theorem Assignment.cons_split {P : Assignment → Prop} {a : Assignment} {l : List Assignment}
    (h : ∀ x ∈ a :: l, P x) : P a ∧ ∀ x ∈ l, P x :=
  ⟨h a (List.Mem.head _), fun x hx => h x (List.Mem.tail _ hx)⟩

end Grounding.Rtl

/-! ### Evaluation-level lemmas (one per `Value` node), used by `bv_dual_rail` -/

namespace Grounding.Rtl.Rail.Ev

open Grounding.Rtl.TritVec (tieDownX tieDownX_getElem)

variable {V : Valuation}

/-- `V.eval v` is encoded by `(x, v')`. -/
abbrev IsR (V : Valuation) (e : Value w) (x v : BitVec w) : Prop := Rail (V.eval e) x v

theorem signal (s : Signal w) {x v} (h : Rail (V s) x v) : IsR V (.signal s) x v := h
theorem const (c : TritVec w) {x v} (h : Rail c x v) : IsR V (.const c) x v := h
theorem not {a : Value w} {x v} (h : IsR V a x v) : IsR V (.not a) x (~~~v &&& ~~~x) := Rail.not h
theorem and {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.and a b) (~~~(Rail.zeroR xa va ||| Rail.zeroR xb vb) &&& ~~~(Rail.oneR xa va &&& Rail.oneR xb vb))
      (Rail.oneR xa va &&& Rail.oneR xb vb) := Rail.and ha hb
theorem or {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.or a b) (~~~(Rail.oneR xa va ||| Rail.oneR xb vb) &&& ~~~(Rail.zeroR xa va &&& Rail.zeroR xb vb))
      (Rail.oneR xa va ||| Rail.oneR xb vb) := Rail.or ha hb
theorem xor {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.xor a b) (xa ||| xb) ((va ^^^ vb) &&& ~~~(xa ||| xb)) := Rail.xor ha hb
theorem mux {s : Value 1} {a b : Value w} {xs vs xa va xb vb} (hs : IsR V s xs vs)
    (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.mux s a b)
      (bif xs.getLsbD 0 then xa ||| xb ||| (va ^^^ vb) else bif vs.getLsbD 0 then xa else xb)
      (bif xs.getLsbD 0 then va &&& ~~~(xa ||| xb ||| (va ^^^ vb)) else bif vs.getLsbD 0 then va else vb) :=
  have h := Rail.bit0 hs
  Rail.mux h.1 h.2 ha hb
theorem adc {a b : Value w} {c : Value 1} {xa va xb vb xc vc} (ha : IsR V a xa va) (hb : IsR V b xb vb)
    (hc : IsR V c xc vc) :
    IsR V (.adc a b c)
      ((xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool (xc.getLsbD 0)).setWidth (w + 1)) |||
        -(xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool (xc.getLsbD 0)).setWidth (w + 1)))
      ((va.setWidth (w + 1) + vb.setWidth (w + 1) + (BitVec.ofBool (vc.getLsbD 0)).setWidth (w + 1)) &&&
        ~~~((xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool (xc.getLsbD 0)).setWidth (w + 1)) |||
        -(xa.setWidth (w + 1) ||| xb.setWidth (w + 1) ||| (BitVec.ofBool (xc.getLsbD 0)).setWidth (w + 1)))) :=
  have h := Rail.bit0 hc
  Rail.adc ha hb h.1 h.2
theorem mul {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.mul a b) (bif Rail.anyX xa xb then BitVec.allOnes w else 0#w)
      (bif Rail.anyX xa xb then 0#w else va * vb) := Rail.mul ha hb
theorem replicate (n : Nat) {a : Value 1} {x v : BitVec 1} (h : IsR V a x v) :
    IsR V (.replicate n a) (bif x.getLsbD 0 then BitVec.allOnes n else 0#n)
      (bif v.getLsbD 0 then BitVec.allOnes n else 0#n) := Rail.replicate n h
theorem eq {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.eq a b)
      (BitVec.ofBool (((~~~(xa ||| xb) &&& (va ^^^ vb)) == 0#w) && (xa ||| xb) != 0#w))
      (BitVec.ofBool (((~~~(xa ||| xb) &&& (va ^^^ vb)) == 0#w) && (xa ||| xb) == 0#w)) := Rail.eq ha hb
theorem eqx {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.eqx a b) 0#1 (BitVec.ofBool (xa == xb && va == vb)) := Rail.eqx ha hb
theorem ult {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.ult a b) (BitVec.ofBool (Rail.anyX xa xb)) (BitVec.ofBool (!Rail.anyX xa xb && va.ult vb)) :=
  Rail.ult ha hb
theorem slt {a b : Value w} {xa va xb vb} (ha : IsR V a xa va) (hb : IsR V b xb vb) :
    IsR V (.slt a b) (BitVec.ofBool (Rail.anyX xa xb)) (BitVec.ofBool (!Rail.anyX xa xb && va.slt vb)) :=
  Rail.slt ha hb
theorem shl {a : Value w} {m : Value k} {xa va xm vm} (hw : w ≤ 2 ^ 32) (ha : IsR V a xa va)
    (hm : IsR V m xm vm) :
    IsR V (.shl 1 k a m) (bif xm != 0#k then BitVec.allOnes w else xa <<< vm)
      (bif xm != 0#k then 0#w else va <<< vm) := Rail.shl hw ha hm
theorem ushr {a : Value w} {m : Value k} {xa va xm vm} (hw : w ≤ 2 ^ 32) (ha : IsR V a xa va)
    (hm : IsR V m xm vm) :
    IsR V (.ushr 1 k a m) (bif xm != 0#k then BitVec.allOnes w else xa >>> vm)
      (bif xm != 0#k then 0#w else va >>> vm) := Rail.ushr hw ha hm
theorem sshr {a : Value w} {m : Value k} {xa va xm vm} (hw : w ≤ 2 ^ 32) (ha : IsR V a xa va)
    (hm : IsR V m xm vm) :
    IsR V (.sshr 1 k a m) (bif xm != 0#k then BitVec.allOnes w else xa.sshiftRight' vm)
      (bif xm != 0#k then 0#w else va.sshiftRight' vm) := Rail.sshr hw ha hm
theorem xshr {a : Value w} {m : Value k} {xa va xm vm} (hw : w ≤ 2 ^ 32) (ha : IsR V a xa va)
    (hm : IsR V m xm vm) :
    IsR V (.xshr 1 k a m) (bif xm != 0#k then BitVec.allOnes w else
        (xa >>> vm) ||| ~~~(BitVec.allOnes w >>> vm))
      (bif xm != 0#k then 0#w else va >>> vm) := Rail.xshr hw ha hm

/-! Strided shifts: `X`/`Y` are the unrolled barrel stages (built by the tactic,
`hX`/`hY` by `rfl`), so `bv_decide` sees one constant-shift mux per amount bit. -/

theorem shlStride {a : Value w} {m : Value k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : IsR V a xa va) (hm : IsR V m xm vm) {X Y : BitVec w}
    (hX : Rail.barrel (fun n x => x <<< n) vm stride k xa = X)
    (hY : Rail.barrel (fun n x => x <<< n) vm stride k va = Y) :
    IsR V (.shl stride k a m) (bif xm != 0#k then BitVec.allOnes w else X)
      (bif xm != 0#k then 0#w else Y) := hX ▸ hY ▸ Rail.shlStride hw hs ha hm
theorem ushrStride {a : Value w} {m : Value k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : IsR V a xa va) (hm : IsR V m xm vm) {X Y : BitVec w}
    (hX : Rail.barrel (fun n x => x >>> n) vm stride k xa = X)
    (hY : Rail.barrel (fun n x => x >>> n) vm stride k va = Y) :
    IsR V (.ushr stride k a m) (bif xm != 0#k then BitVec.allOnes w else X)
      (bif xm != 0#k then 0#w else Y) := hX ▸ hY ▸ Rail.ushrStride hw hs ha hm
theorem sshrStride {a : Value w} {m : Value k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : IsR V a xa va) (hm : IsR V m xm vm) {X Y : BitVec w}
    (hX : Rail.barrel (fun n x => x.sshiftRight n) vm stride k xa = X)
    (hY : Rail.barrel (fun n x => x.sshiftRight n) vm stride k va = Y) :
    IsR V (.sshr stride k a m) (bif xm != 0#k then BitVec.allOnes w else X)
      (bif xm != 0#k then 0#w else Y) := hX ▸ hY ▸ Rail.sshrStride hw hs ha hm
theorem xshrStride {a : Value w} {m : Value k} {xa va xm vm} {stride : Nat} (hw : w ≤ 2 ^ 32)
    (hs : 1 ≤ stride) (ha : IsR V a xa va) (hm : IsR V m xm vm) {X Y : BitVec w}
    (hX : Rail.barrel (fun n x => ~~~(~~~x >>> n)) vm stride k xa = X)
    (hY : Rail.barrel (fun n x => x >>> n) vm stride k va = Y) :
    IsR V (.xshr stride k a m) (bif xm != 0#k then BitVec.allOnes w else X)
      (bif xm != 0#k then 0#w else Y) := hX ▸ hY ▸ Rail.xshrStride hw hs ha hm
theorem partSelect {sw o : Nat} {src : Value sw} {h : o + w ≤ sw} {x v} (ha : IsR V src x v) :
    IsR V (.partSelect sw src o h) (x.extractLsb' o w) (v.extractLsb' o w) := Rail.slice ha o h
theorem concat_nil (w : Nat) (h : (([] : List (Σ w, Value w)).map (·.1)).toArray.foldl Nat.add 0 = w) :
    IsR V (Value.concatList w [] h) 0#w 0#w := by
  have : w = 0 := by simpa using h.symm
  subst this
  exact Rail.empty _
theorem concat_cons {n w : Nat} {v : Value n} {ps : List (Σ w, Value w)}
    {h : ((⟨n, v⟩ :: ps : List (Σ w, Value w)).map (·.1)).toArray.foldl Nat.add 0 = w}
    {xa va xb vb} (hn : n ≤ w) (hv : IsR V v xa va)
    (hr : IsR V (Value.concatList (w - n) ps (concatList_tail h)) xb vb) :
    IsR V (Value.concatList w (⟨n, v⟩ :: ps) h) ((xa ++ xb).cast (by omega)) ((va ++ vb).cast (by omega)) := by
  unfold IsR
  rw [Valuation.eval_concatList_cons]
  exact Rail.appendW hn hv hr

/-- Every constant has a rail encoding: `(maskOf c, valOf c)`. -/
def maskOf (c : TritVec w) : BitVec w :=
  tieDownX ⟨c.bits.map fun t => if t == .x then Trit.one else Trit.zero⟩
def valOf (c : TritVec w) : BitVec w := tieDownX c

theorem maskOf_getElem (c : TritVec w) (i : Nat) (hi : i < w) : (maskOf c)[i] = (c.bits[i] == .x) := by
  rw [maskOf, tieDownX_getElem _ _ hi]
  simp only [Vector.getElem_map]
  cases c.bits[i] <;> rfl

theorem valOf_getElem (c : TritVec w) (i : Nat) (hi : i < w) : (valOf c)[i] = (c.bits[i] == .one) :=
  tieDownX_getElem _ _ hi

theorem rail_self (c : TritVec w) : Rail c (maskOf c) (valOf c) :=
  Rail.mk (fun i hi => by
      rw [maskOf_getElem _ _ hi, valOf_getElem _ _ hi]
      cases c.bits[i] <;> rfl)
    (fun i hi hx => by
      rw [maskOf_getElem _ _ hi] at hx
      rw [valOf_getElem _ _ hi]
      revert hx; cases c.bits[i] <;> simp)

theorem rail_of_self_eq {c : TritVec w} {x v : BitVec w} (h : maskOf c = x ∧ valOf c = v) :
    Rail c x v := h.1 ▸ h.2 ▸ rail_self c

/-- Rails determine the constant. -/
theorem rail_unique {c : TritVec w} {x v x' v'} (h : Rail c x v) (h' : Rail c x' v') :
    x = x' ∧ v = v' := by
  constructor
  · ext i hi
    have a := Rail.rail_bit h i hi
    have b := Rail.rail_bit h' i hi
    rw [a] at b
    have na := Rail.rail_norm h i hi
    have nb := Rail.rail_norm h' i hi
    revert b na nb
    cases x[i] <;> cases v[i] <;> cases x'[i] <;> cases v'[i] <;> simp [Rail.trit, Trit.ofBool]
  · ext i hi
    have a := Rail.rail_bit h i hi
    have b := Rail.rail_bit h' i hi
    rw [a] at b
    have na := Rail.rail_norm h i hi
    have nb := Rail.rail_norm h' i hi
    revert b na nb
    cases x[i] <;> cases v[i] <;> cases x'[i] <;> cases v'[i] <;> simp [Rail.trit, Trit.ofBool]

/-- Equality of constants through their rails. -/
theorem eq_iff_rails {c d : TritVec w} {x v x' v'} (h : Rail c x v) (h' : Rail d x' v') :
    c = d ↔ x = x' ∧ v = v' := by
  constructor
  · rintro rfl; exact rail_unique h h'
  · rintro ⟨rfl, rfl⟩
    exact TritVec.ext_nat fun i hi => by rw [Rail.rail_bit h i hi, Rail.rail_bit h' i hi]

/-- `ofBV a` on rails. -/
theorem rail_ofBV_iff {c : TritVec w} {x v : BitVec w} (h : Rail c x v) (a : BitVec w) :
    c = TritVec.ofBV a ↔ x = 0#w ∧ v = a := eq_iff_rails h (Rail.ofBV a)

/-- The rail facts of a signal: `x = maskOf (V s)`, `v = valOf (V s)` define
the atoms; the `Rail` statement is what the translation needs. -/
theorem signal_self (s : Signal w) : IsR V (.signal s) (maskOf (V s)) (valOf (V s)) := rail_self _

/-- The equation of a signal-target assignment, on rails. -/
theorem assign_signal {s : Signal w} {src : Value w} {x v}
    (heq : V.eval (.signal s) = V.eval src) (hs : IsR V src x v) :
    maskOf (V s) = x ∧ valOf (V s) = v := by
  unfold IsR at hs; rw [← heq] at hs; exact rail_unique (rail_self _) hs

/-- A hypothesis `V s = ofBV a`, on rails. -/
theorem input_ofBV {s : Signal w} {a : BitVec w} (h : V s = TritVec.ofBV a) :
    maskOf (V s) = 0#w ∧ valOf (V s) = a :=
  rail_unique (rail_self _) (h ▸ Rail.ofBV a)

/-- Rewrite a goal's `V s` through its rails: `P (V s)` from `P c` for the
unique `c` with these rails — used for goals `V s = ofBV a` and `V s = V t`. -/
theorem goal_eq_ofBV {s : Signal w} {a : BitVec w} (h : maskOf (V s) = 0#w ∧ valOf (V s) = a) :
    V s = TritVec.ofBV a := (rail_ofBV_iff (rail_self _) a).2 h

theorem goal_eq {s : Signal w} {t : Signal w}
    (h : maskOf (V s) = maskOf (V t) ∧ valOf (V s) = valOf (V t)) : V s = V t :=
  (eq_iff_rails (rail_self _) (rail_self _)).2 h

/-- Equality of two arbitrary constants from their rails. -/
theorem goal_eq_any {c c' : TritVec w} {_x _v : BitVec w}
    (h : maskOf c = maskOf c' ∧ valOf c = valOf c') : c = c' :=
  (Rail.Ev.eq_iff_rails (rail_self c) (rail_self c')).2 h

/-- A constant equation, as rails (used for hypotheses). -/
theorem eq_rails {c c' : TritVec w} (h : c = c') : maskOf c = maskOf c' ∧ valOf c = valOf c' :=
  h ▸ ⟨rfl, rfl⟩

/-- The rails of `TritVec.ofBV a`. -/
theorem maskOf_ofBV (a : BitVec w) : maskOf (TritVec.ofBV a) = 0#w :=
  (rail_unique (rail_self _) (Rail.ofBV a)).1
theorem valOf_ofBV (a : BitVec w) : valOf (TritVec.ofBV a) = a :=
  (rail_unique (rail_self _) (Rail.ofBV a)).2

/-- The rails of `TritVec.undef w`. -/
theorem maskOf_undef (w : Nat) : maskOf (TritVec.undef w) = BitVec.allOnes w :=
  (rail_unique (rail_self _) (Rail.undef w)).1
theorem valOf_undef (w : Nat) : valOf (TritVec.undef w) = 0#w :=
  (rail_unique (rail_self _) (Rail.undef w)).2

theorem bit0_ne_x_mask {c : TritVec 1} (h : c.bit0 ≠ Trit.x) : maskOf c = 0#1 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  rw [maskOf_getElem c 0 hi]
  simpa [TritVec.bit0, Vector.get] using h

theorem bit0_ne_x_of_mask {c : TritVec 1} (h : maskOf c = 0#1) : c.bit0 ≠ Trit.x := by
  intro hx
  have := maskOf_getElem c 0 (by omega)
  rw [h] at this
  have hb : c.bits[0] = Trit.x := by simpa [TritVec.bit0, Vector.get] using hx
  simp [hb] at this

theorem bit0_eq_zero_rails {c : TritVec 1} (h : c.bit0 = Trit.zero) :
    maskOf c = 0#1 ∧ valOf c = 0#1 := by
  refine ⟨bit0_ne_x_mask (by simp [h]), ?_⟩
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  rw [valOf_getElem c 0 hi]
  have : c.bits[0] = Trit.zero := by simpa [TritVec.bit0, Vector.get] using h
  simp [this]

theorem bit0_ne_zero_rails {c : TritVec 1} (h : c.bit0 ≠ Trit.zero) :
    maskOf c ||| valOf c = 1#1 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  rw [BitVec.getElem_or, maskOf_getElem c 0 hi, valOf_getElem c 0 hi]
  cases ht : c.bits[0] <;> simp_all [TritVec.bit0, Vector.get]

end Grounding.Rtl.Rail.Ev
