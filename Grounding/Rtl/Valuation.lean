-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL evaluation semantics.

`Valuation.eval` maps each `Value` node onto the corresponding `TritVec`
operation (defined in `TritVec.lean`) under a valuation of the signals, and
`Valuation.isConsistent` says a valuation satisfies a netlist's assignments and
asynchronous resets.

TODO (not implemented): `udiv`, `umod` and the signed div/mod operations evaluate to
all-X (see `Valuation.eval`); the native frontend (`native/backend_builder.cpp`)
rejects `/`, `%`, `**` and wildcard equality (`==?`, `!=?`) as unsupported.
-/

import Grounding.Rtl.Netlist
import Grounding.Rtl.TritVec
import Batteries.Data.List.Lemmas
import Init.Data.BitVec.Lemmas

namespace Grounding.Rtl

/-! ### Evaluation -/

/-- A valuation assigns a constant to every signal at every width. -/
abbrev Valuation := {width : Nat} → Signal width → TritVec width

/-- Evaluate a `Value` under a valuation. -/
def Valuation.eval (V : Valuation) : {width : Nat} → Value width → TritVec width
  | _, .const c => c
  | _, .signal s => V s
  | _, .not a => TritVec.not_ (V.eval a)
  | _, .and a b => TritVec.and_ (V.eval a) (V.eval b)
  | _, .or a b => TritVec.or_ (V.eval a) (V.eval b)
  | _, .xor a b => TritVec.xor_ (V.eval a) (V.eval b)
  | _, .mux sel a b =>
      TritVec.mux (TritVec.bit0 (V.eval sel)) (V.eval a) (V.eval b)
  | _, .adc a b cin =>
      TritVec.adc (V.eval a) (V.eval b) (TritVec.bit0 (V.eval cin))
  | _, .eq a b => TritVec.eq (V.eval a) (V.eval b)
  | _, .ult a b => TritVec.ult (V.eval a) (V.eval b)
  | _, .slt a b => TritVec.slt (V.eval a) (V.eval b)
  | _, .eqx a b => TritVec.eqx (V.eval a) (V.eval b)
  | _, .shl stride _ a amt => TritVec.shlStride stride (V.eval a) (V.eval amt)
  | _, .ushr stride _ a amt => TritVec.ushrStride stride (V.eval a) (V.eval amt)
  | _, .sshr stride _ a amt => TritVec.sshrStride stride (V.eval a) (V.eval amt)
  | _, .xshr stride _ a amt => TritVec.xshrStride stride (V.eval a) (V.eval amt)
  | _, .replicate _ a => TritVec.replicate _ (V.eval a)
  | _, .mul a b => TritVec.mul (V.eval a) (V.eval b)
  -- TODO: division and modulo are not implemented: `udiv`, `umod`, `sdivTrunc`,
  -- `sdivFloor`, `smodTrunc` and `smodFloor` all evaluate to all-X, so any property
  -- that depends on their result is vacuous or unprovable. They need real `TritVec`
  -- operations (all-X when an operand has an X or the divisor is zero, otherwise the
  -- `BitVec` operation), `_ofBV` lemmas, and `Rail` encodings for `bv_dual_rail`.
  | width, .udiv _ _ => TritVec.undef width
  | width, .umod _ _ => TritVec.undef width
  | width, .sdivTrunc _ _ => TritVec.undef width
  | width, .sdivFloor _ _ => TritVec.undef width
  | width, .smodTrunc _ _ => TritVec.undef width
  | width, .smodFloor _ _ => TritVec.undef width
  | width, .concatNode _ ws parts _ =>
      TritVec.ofArrayD width
        ((List.finRange ws.size).foldr
          (fun i acc => acc ++ (V.eval (parts i)).bits.toArray) #[])
  | _, .partSelect _ src offset h =>
      TritVec.slice (V.eval src) offset _ h

/-- Two valuations that agree on the netlist's signals evaluate every value
whose signals are in the netlist identically. -/
theorem Valuation.eval_congr {V V' : Valuation} {n : Netlist}
    (h : ∀ s : Σ width, Signal width, s ∈ n.signals → V s.2 = V' s.2) :
    {width : Nat} → (v : Value width) → v.InNetlist n → V.eval v = V'.eval v
  | _, .const _, _ => rfl
  | _, .signal s, .signal _ hs => h ⟨_, s⟩ hs
  | _, .not a, .not ha => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha]
  | _, .and a b, .and ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .or a b, .or ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .xor a b, .xor ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .mux sel a b, .mux hs ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h sel hs,
        Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .adc a b cin, .adc ha hb hc => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha,
        Valuation.eval_congr h b hb, Valuation.eval_congr h cin hc]
  | _, .eq a b, .eq ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .ult a b, .ult ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .slt a b, .slt ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .eqx a b, .eqx ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | _, .shl stride _ a amt, .shl ha hm => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h amt hm]
  | _, .ushr stride _ a amt, .ushr ha hm => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h amt hm]
  | _, .sshr stride _ a amt, .sshr ha hm => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h amt hm]
  | _, .xshr stride _ a amt, .xshr ha hm => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h amt hm]
  | _, .replicate _ a, .replicate ha => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha]
  | _, .mul a b, .mul ha hb => by
      simp only [Valuation.eval, Valuation.eval_congr h a ha, Valuation.eval_congr h b hb]
  | width, .udiv _ _, .udiv _ _ => rfl
  | width, .umod _ _, .umod _ _ => rfl
  | width, .sdivTrunc _ _, .sdivTrunc _ _ => rfl
  | width, .sdivFloor _ _, .sdivFloor _ _ => rfl
  | width, .smodTrunc _ _, .smodTrunc _ _ => rfl
  | width, .smodFloor _ _, .smodFloor _ _ => rfl
  | width, .concatNode _ ws parts _, .concatNode hparts => by
      simp only [Valuation.eval]
      congr 1
      generalize List.finRange ws.size = is
      induction is with
      | nil => rfl
      | cons i is ih =>
          simp only [List.foldr_cons, ih]
          rw [Valuation.eval_congr h (parts i) (hparts i)]
  | _, .partSelect _ src offset hh, .partSelect hsrc => by
      simp only [Valuation.eval, Valuation.eval_congr h src hsrc]

namespace AsyncLoad

/-- The trigger is at its active level under `V`. A trigger at `X` is not
considered active.

TODO: an `X` on an async reset should make `q` `X` unless a higher-priority
async load is active. -/
def active (V : Valuation) (al : AsyncLoad width) : Prop :=
  (V.eval al.trigger).bit0 = Trit.ofBool al.polarity

/-- Boolean form of `active`, used to find the first active load. -/
def isActive (V : Valuation) (al : AsyncLoad width) : Bool :=
  (V.eval al.trigger).bit0 == Trit.ofBool al.polarity

theorem isActive_iff (V : Valuation) (al : AsyncLoad width) :
    al.isActive V = true ↔ al.active V := by
  simp [isActive, active, beq_iff_eq]

end AsyncLoad

namespace Register

/-- The value forced by the first active asynchronous load in `V`, if any. -/
def asyncValue (V : Valuation) (r : Register width) : Option (TritVec width) :=
  (r.aloads.find? (fun al => al.isActive V)).map (fun al => V.eval al.value)

end Register

namespace Valuation

/-- `V` satisfies every assignment of `n`. -/
def assignsHold (V : Valuation) (n : Netlist) : Prop :=
  ∀ a ∈ n.assignments, V.eval a.target = V.eval a.source

/-- `V` satisfies every active asynchronous load of `n` (the level-sensitive
reset condition). -/
def resetsHold (V : Valuation) (n : Netlist) : Prop :=
  ∀ (r : Σ width, Register width), r ∈ n.registers →
    ∀ v, r.2.asyncValue V = some v → V.eval r.2.q = v

/-- A valuation is consistent with a netlist when it satisfies every
assignment and every active asynchronous load. Use `isConsistent.assigns` /
`isConsistent.resets` to project the parts. -/
def isConsistent (V : Valuation) (n : Netlist) : Prop :=
  V.assignsHold n ∧ V.resetsHold n

theorem isConsistent.assigns {V : Valuation} {n : Netlist} (h : V.isConsistent n) :
    V.assignsHold n := h.1

theorem isConsistent.resets {V : Valuation} {n : Netlist} (h : V.isConsistent n) :
    V.resetsHold n := h.2

/-- Computable consistency check. -/
def checkConsistent (V : Valuation) (n : Netlist) : Bool :=
  n.assignments.all (fun a => decide (V.eval a.target = V.eval a.source)) &&
  n.registers.all (fun r =>
    match r.2.asyncValue V with
    | some v => decide (V.eval r.2.q = v)
    | none => true)

/-- The computable checker agrees with the specification. -/
theorem checkConsistent_iff (V : Valuation) (n : Netlist) :
    checkConsistent V n = true ↔ isConsistent V n := by
  simp only [checkConsistent, isConsistent, assignsHold, resetsHold, List.all_eq_true,
    Bool.and_eq_true]
  constructor
  · rintro ⟨ha, hr⟩
    refine ⟨fun a ha' => of_decide_eq_true (ha a ha'), ?_⟩
    intro r hr' v hv
    have := hr r hr'
    rw [hv] at this
    exact of_decide_eq_true this
  · rintro ⟨ha, hr⟩
    refine ⟨fun a ha' => decide_eq_true (ha a ha'), ?_⟩
    intro r hr'
    cases h : r.2.asyncValue V with
    | none => rfl
    | some v => exact decide_eq_true (hr r hr' v h)

end Valuation

theorem Valuation.isConsistent_get {V : Valuation} {n : Netlist} (h : V.isConsistent n)
    (i : Nat) (a : Assignment) (hi : n.assignments[i]? = some a) :
    V.eval a.target = V.eval a.source :=
  h.assigns a (List.mem_of_getElem? hi)

/-- A structural fingerprint of a netlist (signal table, ports, assignments,
registers). Used to check that a re-elaborated design is the embedded one. -/
def Netlist.fingerprint (n : Netlist) : UInt64 :=
  let h := n.signals.foldl (fun h (p : Σ w, Signal w) =>
    mixHash h (mixHash (hash p.1) (mixHash (hash p.2.id) (hash p.2.name)))) 7
  let h := n.ports.foldl (fun h (p : Σ w, Port w) =>
    let dir : UInt64 := match p.2 with | .In .. => 1 | .Out .. => 2
    mixHash h (mixHash dir (mixHash (hash p.2.name) (Value.hash p.1 p.2.value)))) h
  let h := n.assignments.foldl (fun h a =>
    mixHash h (mixHash (Value.hash a.width a.target) (Value.hash a.width a.source))) h
  n.registers.foldl (fun h (p : Σ w, Register w) =>
    let r := p.2
    let h := mixHash h (mixHash (Value.hash p.1 r.q)
      (mixHash (Value.hash p.1 r.d) (mixHash (Value.hash 1 r.clk) (hash r.clkPolarity))))
    let h := mixHash h (TritVec.hash r.init)
    r.aloads.foldl (fun h l =>
      mixHash h (mixHash (Value.hash 1 l.trigger) (mixHash (hash l.polarity)
        (Value.hash p.1 l.value)))) h) h

end Grounding.Rtl
