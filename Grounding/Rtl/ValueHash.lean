-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL value hashing and Boolean equality.
-/

import Grounding.Rtl.Netlist

namespace Grounding.Rtl
namespace Value

/-- A comparison function for `x` that is known to accept `x` itself. -/
abbrev ReflCmp {w : Nat} (x : Value w) := {f : Value w → Bool // f x = true}

/-- Run a reflexive comparison, short-circuiting on pointer equality. -/
@[inline] def cmp {w : Nat} {x : Value w} (r : ReflCmp x) (y : Value w) : Bool :=
  withPtrEq x y (fun _ => r.1 y) (fun h => h ▸ r.2)

@[simp] theorem cmp_eq {w : Nat} {x : Value w} (r : ReflCmp x) (y : Value w) :
    cmp r y = r.1 y := rfl

@[simp] theorem cmp_self {w : Nat} {x : Value w} (r : ReflCmp x) : cmp r x = true := r.2

private theorem and_true' {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp [ha, hb]

private theorem dite_true' {p : Prop} [Decidable p] (hp : p) {f : p → Bool} {g : ¬p → Bool}
    (h : f hp = true) : dite p f g = true := by
  rw [dite_eq_left_of_eq_true (eq_true hp)]; exact h

/-- Structural equality with a pointer fast path at every node. -/
def beqStruct {w : Nat} : (a : Value w) → ReflCmp a
  | .const c1 => ⟨fun b => match b with
      | .const c2 => decide (c1 = c2)
      | _ => false, decide_eq_true rfl⟩
  | .signal s1 => ⟨fun b => match b with
      | .signal s2 => decide (s1 = s2)
      | _ => false, decide_eq_true rfl⟩
  | .not a1 => ⟨fun b => match b with
      | .not a2 => cmp (beqStruct a1) a2
      | _ => false, cmp_self _⟩
  | .and a1 b1 => ⟨fun b => match b with
      | .and a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .or a1 b1 => ⟨fun b => match b with
      | .or a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .xor a1 b1 => ⟨fun b => match b with
      | .xor a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .mul a1 b1 => ⟨fun b => match b with
      | .mul a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .udiv a1 b1 => ⟨fun b => match b with
      | .udiv a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .umod a1 b1 => ⟨fun b => match b with
      | .umod a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .sdivTrunc a1 b1 => ⟨fun b => match b with
      | .sdivTrunc a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .sdivFloor a1 b1 => ⟨fun b => match b with
      | .sdivFloor a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .smodTrunc a1 b1 => ⟨fun b => match b with
      | .smodTrunc a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | .smodFloor a1 b1 => ⟨fun b => match b with
      | .smodFloor a2 b2 => cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (cmp_self _) (cmp_self _)⟩
  | @eq w1 a1 b1 => ⟨fun b => match b with
      | @eq w2 a2 b2 =>
          if h : w2 = w1 then cmp (beqStruct a1) (h ▸ a2) && cmp (beqStruct b1) (h ▸ b2)
          else false
      | _ => false, dite_true' rfl (and_true' (cmp_self _) (cmp_self _))⟩
  | @ult w1 a1 b1 => ⟨fun b => match b with
      | @ult w2 a2 b2 =>
          if h : w2 = w1 then cmp (beqStruct a1) (h ▸ a2) && cmp (beqStruct b1) (h ▸ b2)
          else false
      | _ => false, dite_true' rfl (and_true' (cmp_self _) (cmp_self _))⟩
  | @slt w1 a1 b1 => ⟨fun b => match b with
      | @slt w2 a2 b2 =>
          if h : w2 = w1 then cmp (beqStruct a1) (h ▸ a2) && cmp (beqStruct b1) (h ▸ b2)
          else false
      | _ => false, dite_true' rfl (and_true' (cmp_self _) (cmp_self _))⟩
  | @eqx w1 a1 b1 => ⟨fun b => match b with
      | @eqx w2 a2 b2 =>
          if h : w2 = w1 then cmp (beqStruct a1) (h ▸ a2) && cmp (beqStruct b1) (h ▸ b2)
          else false
      | _ => false, dite_true' rfl (and_true' (cmp_self _) (cmp_self _))⟩
  | .mux s1 a1 b1 => ⟨fun b => match b with
      | .mux s2 a2 b2 =>
          cmp (beqStruct s1) s2 && cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2
      | _ => false, and_true' (and_true' (cmp_self _) (cmp_self _)) (cmp_self _)⟩
  | .adc a1 b1 c1 => ⟨fun b => match b with
      | .adc a2 b2 c2 =>
          cmp (beqStruct a1) a2 && cmp (beqStruct b1) b2 && cmp (beqStruct c1) c2
      | _ => false, and_true' (and_true' (cmp_self _) (cmp_self _)) (cmp_self _)⟩
  | .shl stride1 amt1 a1 m1 => ⟨fun b => match b with
      | .shl stride2 amt2 a2 m2 =>
          if h : stride2 = stride1 ∧ amt2 = amt1 then
            cmp (beqStruct a1) a2 && cmp (beqStruct m1) (h.2 ▸ m2)
          else false
      | _ => false, dite_true' ⟨rfl, rfl⟩ (and_true' (cmp_self _) (cmp_self _))⟩
  | .ushr stride1 amt1 a1 m1 => ⟨fun b => match b with
      | .ushr stride2 amt2 a2 m2 =>
          if h : stride2 = stride1 ∧ amt2 = amt1 then
            cmp (beqStruct a1) a2 && cmp (beqStruct m1) (h.2 ▸ m2)
          else false
      | _ => false, dite_true' ⟨rfl, rfl⟩ (and_true' (cmp_self _) (cmp_self _))⟩
  | .sshr stride1 amt1 a1 m1 => ⟨fun b => match b with
      | .sshr stride2 amt2 a2 m2 =>
          if h : stride2 = stride1 ∧ amt2 = amt1 then
            cmp (beqStruct a1) a2 && cmp (beqStruct m1) (h.2 ▸ m2)
          else false
      | _ => false, dite_true' ⟨rfl, rfl⟩ (and_true' (cmp_self _) (cmp_self _))⟩
  | .xshr stride1 amt1 a1 m1 => ⟨fun b => match b with
      | .xshr stride2 amt2 a2 m2 =>
          if h : stride2 = stride1 ∧ amt2 = amt1 then
            cmp (beqStruct a1) a2 && cmp (beqStruct m1) (h.2 ▸ m2)
          else false
      | _ => false, dite_true' ⟨rfl, rfl⟩ (and_true' (cmp_self _) (cmp_self _))⟩
  | .replicate w1 a1 => ⟨fun b => match b with
      | .replicate w2 a2 => decide (w2 = w1) && cmp (beqStruct a1) a2
      | _ => false, and_true' (decide_eq_true rfl) (cmp_self _)⟩
  | .concatNode _ ws1 p1 _ => ⟨fun b => match b with
      | .concatNode _ ws2 p2 _ =>
          if h : ws2 = ws1 then
            (List.finRange ws1.size).all (fun i => cmp (beqStruct (p1 i)) ((h ▸ p2) i))
          else false
      | _ => false, dite_true' rfl (List.all_eq_true.2 fun _ _ => cmp_self _)⟩
  | .partSelect sw1 s1 o1 _ => ⟨fun b => match b with
      | .partSelect sw2 s2 o2 _ =>
          if h : sw2 = sw1 then decide (o1 = o2) && cmp (beqStruct s1) (h ▸ s2)
          else false
      | _ => false, dite_true' rfl (and_true' (decide_eq_true rfl) (cmp_self _))⟩

/-- Equality with a top-level pointer fast path. The cached structural hashes
are compared first, so unequal values (e.g. other entries in a hash-map bucket)
are rejected in O(1) instead of by a walk down both expressions. -/
def beq {w : Nat} (a b : Value w) : Bool :=
  Value.hash w a == Value.hash w b && cmp (beqStruct a) b

set_option maxHeartbeats 1000000 in
theorem beqStruct_sound {w : Nat} (a b : Value w) (h : (beqStruct a).1 b = true) : a = b := by
  induction a with
  | const | signal | not | and | or | xor | mul | udiv | umod | sdivTrunc | sdivFloor
  | smodTrunc | smodFloor | mux | adc | replicate =>
    cases b <;> simp only [beqStruct, cmp_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    all_goals
      try obtain ⟨⟨_, _⟩, _⟩ := h
      try obtain ⟨_, _⟩ := h
      try subst_vars
      try simp only [Value.not.injEq, Value.and.injEq, Value.or.injEq, Value.xor.injEq,
        Value.mul.injEq, Value.udiv.injEq, Value.umod.injEq, Value.sdivTrunc.injEq,
        Value.sdivFloor.injEq, Value.smodTrunc.injEq, Value.smodFloor.injEq, Value.mux.injEq,
        Value.adc.injEq, Value.replicate.injEq]
      repeat' apply And.intro
      all_goals solve_by_elim
  | eq | ult | slt | eqx | shl | ushr | sshr | xshr | partSelect =>
    cases b <;> simp only [beqStruct] at h
    all_goals first
      | contradiction
      | (split at h
         · rename_i hcond
           try obtain ⟨rfl, rfl⟩ := hcond
           subst_vars
           simp only [cmp_eq, Bool.and_eq_true, decide_eq_true_eq] at h
           obtain ⟨_, _⟩ := h
           simp only [Value.eq.injEq, Value.ult.injEq, Value.slt.injEq, Value.eqx.injEq,
             Value.shl.injEq, Value.ushr.injEq, Value.sshr.injEq, Value.xshr.injEq,
             Value.partSelect.injEq,
             heq_eq_eq, true_and]
           repeat' apply And.intro
           all_goals first | assumption | solve_by_elim | done
         · contradiction)
  | concatNode _ ws1 p1 _ ih =>
    cases b <;> simp only [beqStruct] at h
    all_goals first
      | contradiction
      | (split at h
         · subst_vars
           simp only [cmp_eq, List.all_eq_true, List.mem_finRange, true_implies] at h
           obtain rfl : p1 = _ := funext fun i => ih i _ (h i)
           rfl
         · contradiction)

theorem beq_iff {w : Nat} (a b : Value w) : beq a b = true ↔ a = b :=
  ⟨fun h => beqStruct_sound a b (Bool.and_eq_true _ _ ▸ h).2,
   fun h => by subst h; simp only [beq, beq_self_eq_true, Bool.true_and]; exact cmp_self _⟩

end Value

instance : BEq (Value w) where
  beq := Value.beq

instance : LawfulBEq (Value w) where
  eq_of_beq h := (Value.beq_iff _ _).1 h
  rfl := (Value.beq_iff _ _).2 rfl

instance : Hashable (Value w) where
  hash := Value.hash w

/-! ### Width-carrying keys, for the shared read-set memo. -/

instance : BEq (Σ w, Value w) where
  beq a b :=
    if h : a.1 = b.1 then Value.beq (h ▸ a.2) b.2 else false

instance : LawfulBEq (Σ w, Value w) where
  eq_of_beq {a b} h := by
    obtain ⟨wa, va⟩ := a
    obtain ⟨wb, vb⟩ := b
    simp only [BEq.beq] at h
    split at h
    · rename_i hw
      cases hw
      exact congrArg _ ((Value.beq_iff _ _).1 h)
    · contradiction
  rfl {a} := by simp [BEq.beq, (Value.beq_iff _ _).2]

instance : Hashable (Σ w, Value w) where
  hash a := mixHash (hashNat a.1) (Value.hash a.1 a.2)

end Grounding.Rtl
