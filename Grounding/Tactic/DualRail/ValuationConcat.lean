-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL: evaluating `Value.concatList`.

`eval_concatList` computes a literal concatenation from the bits of its parts, and
`eval_concatList_cons` peels the most significant part off as `TritVec.appendW`.
-/

import Grounding.Rtl.Valuation

namespace Grounding.Rtl

/-! ### Evaluating `concatList` -/

/-- The bits of the parts, LSB first (the last part is least significant). -/
def partsBits (V : Valuation) : List (Σ w, Value w) → List Trit
  | [] => []
  | p :: ps => partsBits @V ps ++ (V.eval p.2).bits.toList

/-- The constant of `concatList`: the parts' bits, LSB first. -/
def concatConst (V : Valuation) (w : Nat) (ps : List (Σ w, Value w)) : TritVec w :=
  TritVec.ofArrayD w (partsBits @V ps).toArray

theorem partsBits_eq (V : Valuation) (ps : List (Σ w, Value w)) :
    partsBits @V ps = ps.reverse.flatMap (fun p => (V.eval p.2).bits.toList) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [partsBits, ih]

/-- The parts' concatenation, as a list. -/
theorem foldr_parts_toList {n : Nat} (f : Fin n → Array Trit) : ∀ (l : List (Fin n)),
    (l.foldr (fun k acc => acc ++ f k) #[]).toList = (l.reverse.flatMap (fun k => (f k).toList))
  | [] => rfl
  | k :: l => by simp [foldr_parts_toList f l]

theorem finRange_map_get {α : Type} (ps : Array α) :
    (List.finRange ps.size).map (fun k => ps[k.val]) = ps.toList := by
  apply List.ext_getElem <;> simp

theorem flatMap_finRange_rev {α β : Type} (ps : Array α) (f : α → List β) :
    (List.finRange ps.size).reverse.flatMap (fun k => f ps[k.val]) = ps.toList.reverse.flatMap f := by
  have : (List.finRange ps.size).reverse.flatMap (fun k => f ps[k.val]) =
      ((List.finRange ps.size).map (fun k => ps[k.val])).reverse.flatMap f := by
    rw [List.map_reverse.symm, List.flatMap_map]
  rw [this, finRange_map_get]

/-- Evaluating a width-cast value gives the same bits. -/
theorem cast_eval_toList (V : Valuation) {w w' : Nat} (h : w = w') (v : Value w) :
    (V.eval (h ▸ v)).bits.toList = (V.eval v).bits.toList := by
  subst h; rfl

theorem concatListPart_toList (V : Valuation) (ps : List (Σ w, Value w))
    (i : Fin (ps.map (·.1)).toArray.size) :
    (V.eval (concatListPart ps i)).bits.toList =
      (V.eval (ps[i.1]'(concatList_lt ps i)).2).bits.toList := by
  unfold concatListPart
  exact cast_eval_toList @V _ _

theorem Valuation.eval_concatList (V : Valuation) (w : Nat) (ps : List (Σ w, Value w))
    (h : (ps.map (·.1)).toArray.foldl Nat.add 0 = w) :
    V.eval (Value.concatList w ps h) = concatConst @V w ps := by
  simp only [Value.concatList, Valuation.eval, concatConst]
  congr 1
  apply Array.toList_inj.mp
  rw [foldr_parts_toList]
  simp only [Vector.toList_toArray, concatListPart_toList, partsBits_eq]
  have hs : (ps.map (·.1)).toArray.size = ps.length := by simp
  rw [show (List.finRange (ps.map (·.1)).toArray.size) =
      (List.finRange ps.length).map (Fin.cast hs.symm) from by
        apply List.ext_getElem <;> simp]
  rw [List.map_reverse.symm, List.flatMap_map]
  have := flatMap_finRange_rev ps.toArray (fun p => (V.eval p.2).bits.toList)
  simp only [List.getElem_toArray] at this
  exact this

theorem foldl_add_cons (n : Nat) (l : List Nat) :
    (n :: l).toArray.foldl Nat.add 0 = n + l.toArray.foldl Nat.add 0 := by
  simp only [List.foldl_toArray]
  rw [List.foldl_cons]
  generalize l = l
  suffices ∀ a b, List.foldl Nat.add (a + b) l = a + List.foldl Nat.add b l by
    simpa using this n 0
  induction l with
  | nil => intros; rfl
  | cons x l ih => intro a b; simp only [List.foldl_cons]; rw [← ih]; congr 1; show a + b + x = a + (b + x); omega

theorem partsBits_length (V : Valuation) (ps : List (Σ w, Value w)) :
    (partsBits @V ps).length = (ps.map (·.1)).toArray.foldl Nat.add 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [partsBits, List.length_append, ih, List.map_cons, foldl_add_cons]; simp; omega

theorem concatList_tail {n w : Nat} {v : Value n} {ps : List (Σ w, Value w)}
    (h : ((⟨n, v⟩ :: ps : List (Σ w, Value w)).map (·.1)).toArray.foldl Nat.add 0 = w) :
    (ps.map (·.1)).toArray.foldl Nat.add 0 = w - n := by
  rw [List.map_cons, foldl_add_cons] at h
  simp only at h
  omega

/-- Peel the first (most significant) part of a concatenation. -/
@[simp] theorem Valuation.eval_concatList_cons (V : Valuation) (w n : Nat) (v : Value n)
    (ps : List (Σ w, Value w))
    (h : ((⟨n, v⟩ :: ps : List (Σ w, Value w)).map (·.1)).toArray.foldl Nat.add 0 = w) :
    V.eval (Value.concatList w (⟨n, v⟩ :: ps) h) =
      (V.eval v).appendW (V.eval (Value.concatList (w - n) ps (concatList_tail h))) w := by
  rw [Valuation.eval_concatList, Valuation.eval_concatList, concatConst, concatConst, TritVec.appendW,
    TritVec.ofArrayD_toArray (by rw [List.size_toArray, partsBits_length]; exact concatList_tail h)]
  simp only [partsBits, ← List.append_toArray]
  rfl

end Grounding.Rtl
