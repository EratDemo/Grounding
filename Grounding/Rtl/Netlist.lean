-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL netlist structure.

Core value/assignment/register/port types.
-/

namespace Grounding.Rtl

/-- 0, 1, or X. -/
inductive Trit where
  | zero
  | one
  | x
  deriving Repr, DecidableEq, Inhabited

/-- A constant of exactly `width` trits. -/
structure TritVec (width : Nat) where
  bits : Vector Trit width
  deriving Repr, DecidableEq

/-- A net reference. `id` is the identity; `name` is debug metadata only. -/
structure Signal (width : Nat) where
  id : Nat
  name : Option String := none
  deriving Repr, DecidableEq

/-- Reducible helpers used inside the computed field. Keeping these as plain
`def`s (rather than `Hashable.hash` projections) lets `getComputedFieldValue`
reduce the field. -/
def hashNat (n : Nat) : UInt64 := UInt64.ofNat n

def hashArray (l : Array Nat) : UInt64 :=
  l.foldl (fun h n => mixHash h (hashNat n)) 0

namespace Trit

def hash : Trit → UInt64
  | zero => 0
  | one => 1
  | x => 2

end Trit

instance : Hashable Trit := ⟨Trit.hash⟩

namespace TritVec

def hash (c : TritVec width) : UInt64 :=
  c.bits.toList.foldl (fun h t => mixHash h (Trit.hash t)) 0

end TritVec

instance : Hashable (TritVec width) := ⟨TritVec.hash⟩

namespace Signal

/-- Hash of the identity (`id`); `name` is debug metadata and not hashed. -/
def hash (s : Signal width) : UInt64 := hashNat s.id

end Signal

instance : Hashable (Signal width) := ⟨Signal.hash⟩

/--
A value expression, indexed by its result width.

Conventions:
* `mux sel a b` is `sel ? a : b`.
* `adc a b cin` produces `width + 1` bits.
* `concatNode widths parts _` is MSB-first: part 0 holds the most significant
  bits.
-/
inductive Value : Nat → Type where
  | const {width : Nat} (c : TritVec width) : Value width
  | signal {width : Nat} (s : Signal width) : Value width

  | not {width : Nat} (a : Value width) : Value width
  | and {width : Nat} (a b : Value width) : Value width
  | or {width : Nat} (a b : Value width) : Value width
  | xor {width : Nat} (a b : Value width) : Value width

  | mux {width : Nat} (sel : Value 1) (a b : Value width) : Value width

  | adc {width : Nat} (a b : Value width) (cin : Value 1) :
      Value (width + 1)

  | eq {width : Nat} (a b : Value width) : Value 1
  | ult {width : Nat} (a b : Value width) : Value 1
  | slt {width : Nat} (a b : Value width) : Value 1
  /-- Case equality (`===`): compares X literally, always 0 or 1. -/
  | eqx {width : Nat} (a b : Value width) : Value 1

  /-- Shift left by `stride * amount`. `stride` is a positive constant scale
  (normally 1, or the slot width of a `Bmux`/`Demux`). -/
  | shl (stride : Nat) (amt : Nat) (a : Value width) (amount : Value amt) :
      Value width
  | ushr (stride : Nat) (amt : Nat) (a : Value width) (amount : Value amt) :
      Value width
  | sshr (stride : Nat) (amt : Nat) (a : Value width) (amount : Value amt) :
      Value width
  | xshr (stride : Nat) (amt : Nat) (a : Value width) (amount : Value amt) :
      Value width

  /-- Repeat a single-bit value `width` times (all result bits equal `a`). -/
  | replicate (width : Nat) (a : Value 1) : Value width

  | mul {width : Nat} (a b : Value width) : Value width
  | udiv {width : Nat} (a b : Value width) : Value width
  | umod {width : Nat} (a b : Value width) : Value width
  | sdivTrunc {width : Nat} (a b : Value width) : Value width
  | sdivFloor {width : Nat} (a b : Value width) : Value width
  | smodTrunc {width : Nat} (a b : Value width) : Value width
  | smodFloor {width : Nat} (a b : Value width) : Value width

  | concatNode (width : Nat) (ws : Array Nat)
      (parts : (i : Fin ws.size) → Value ws[i])
      (h : ws.foldl Nat.add 0 = width) : Value width

  | partSelect (srcWidth : Nat) (src : Value srcWidth)
      (offset : Nat) (h : offset + width ≤ srcWidth) : Value width
with
  /-- Structural hash, computed once at construction and stored in the node.
  The `h` proofs are propositions and do not contribute. The index is an
  explicit argument, as required by `@[computed_field]` on indexed types. -/
  @[computed_field] hash : (width : Nat) → Value width → UInt64
    | width, .const c =>
        mixHash 0 (mixHash (hashNat width) (TritVec.hash c))
    | width, .signal s =>
        mixHash 1 (mixHash (hashNat width) (Signal.hash s))
    | width, .not a =>
        mixHash 2 (mixHash (hashNat width) (hash width a))
    | width, .and a b =>
        mixHash 3 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .or a b =>
        mixHash 4 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .xor a b =>
        mixHash 5 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .mux sel a b =>
        mixHash 6 (mixHash (hashNat width)
          (mixHash (hash 1 sel) (mixHash (hash width a) (hash width b))))
    | _, .adc a b cin =>
        mixHash 7 (mixHash (hash _ a) (mixHash (hash _ b) (hash 1 cin)))
    | _, .eq a b =>
        mixHash 8 (mixHash (hash _ a) (hash _ b))
    | _, .ult a b =>
        mixHash 9 (mixHash (hash _ a) (hash _ b))
    | _, .slt a b =>
        mixHash 10 (mixHash (hash _ a) (hash _ b))
    | _, .eqx a b =>
        mixHash 24 (mixHash (hash _ a) (hash _ b))
    | width, .shl stride _ a amt =>
        mixHash 11 (mixHash (hashNat stride) (mixHash (hashNat width)
          (mixHash (hash width a) (hash _ amt))))
    | width, .ushr stride _ a amt =>
        mixHash 12 (mixHash (hashNat stride) (mixHash (hashNat width)
          (mixHash (hash width a) (hash _ amt))))
    | width, .sshr stride _ a amt =>
        mixHash 13 (mixHash (hashNat stride) (mixHash (hashNat width)
          (mixHash (hash width a) (hash _ amt))))
    | width, .xshr stride _ a amt =>
        mixHash 14 (mixHash (hashNat stride) (mixHash (hashNat width)
          (mixHash (hash width a) (hash _ amt))))
    | width, .replicate _ a =>
        mixHash 25 (mixHash (hashNat width) (hash 1 a))
    | width, .mul a b =>
        mixHash 15 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .udiv a b =>
        mixHash 16 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .umod a b =>
        mixHash 17 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .sdivTrunc a b =>
        mixHash 18 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .sdivFloor a b =>
        mixHash 19 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .smodTrunc a b =>
        mixHash 20 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .smodFloor a b =>
        mixHash 21 (mixHash (hashNat width)
          (mixHash (hash width a) (hash width b)))
    | width, .concatNode _ ws parts _ =>
        mixHash 22 (mixHash (hashNat width) (mixHash (hashArray ws)
          (Fin.foldl ws.size (fun h i => mixHash h (hash ws[i] (parts i))) 0)))
    | width, .partSelect srcWidth src offset _ =>
        mixHash 23 (mixHash (hashNat width)
          (mixHash (hashNat srcWidth)
            (mixHash (hash srcWidth src) (hashNat offset))))

namespace Value

/--
Only signals, concatenations of assignable values, and part-selects of an
assignable value can be assigned to.
-/
inductive CanBeAssignedTo : {width : Nat} → Value width → Prop where
  | signal {width : Nat} (s : Signal width) :
      CanBeAssignedTo (.signal s)
  | concat {width : Nat} (ws : Array Nat)
      (parts : (i : Fin ws.size) → Value ws[i])
      (h : ws.foldl Nat.add 0 = width)
      (hparts : ∀ i, CanBeAssignedTo (parts i)) :
      CanBeAssignedTo (.concatNode width ws parts h)
  | partSelect {width : Nat} (srcWidth : Nat) (src : Value srcWidth)
      (offset : Nat) (h : offset + width ≤ srcWidth)
      (hsrc : CanBeAssignedTo src) :
      CanBeAssignedTo (.partSelect srcWidth src offset h)

end Value

/-! ### Concatenation from a list of parts

Embedded designs build `concatNode`s with `concatList`: the parts are a list
literal (MSB first), so the width equation reduces by `rfl` (no `Array.map`). -/

theorem concatList_lt (ps : List (Σ w, Value w)) (i : Fin (ps.map (·.1)).toArray.size) :
    i.1 < ps.length := by simpa using i.2

theorem concatList_width (ps : List (Σ w, Value w)) (i : Fin (ps.map (·.1)).toArray.size) :
    (ps[i.1]'(concatList_lt ps i)).1 = (ps.map (·.1)).toArray[i] := by simp

/-- Part `i` of `concatList`, cast to the width recorded in the width array. -/
def concatListPart (ps : List (Σ w, Value w)) (i : Fin (ps.map (·.1)).toArray.size) :
    Value (ps.map (·.1)).toArray[i] :=
  concatList_width ps i ▸ (ps[i.1]'(concatList_lt ps i)).2

/-- Concatenate a list of parts (MSB first). -/
def Value.concatList (w : Nat) (ps : List (Σ w, Value w))
    (h : (ps.map (·.1)).toArray.foldl Nat.add 0 = w) : Value w :=
  .concatNode w (ps.map (·.1)).toArray (concatListPart ps) h

/-- Every part is assignable (a right-nested conjunction, built term by term). -/
def AllAssignable : List (Σ w, Value w) → Prop
  | [] => True
  | p :: ps => p.2.CanBeAssignedTo ∧ AllAssignable ps

theorem AllAssignable.get : ∀ {ps : List (Σ w, Value w)}, AllAssignable ps →
    ∀ (i : Nat) (hi : i < ps.length), (ps[i]'hi).2.CanBeAssignedTo
  | _ :: _, h, 0, _ => h.1
  | _ :: _, h, i + 1, hi => AllAssignable.get h.2 i (by simpa using hi)

theorem canBeAssignedTo_cast {w1 w2 : Nat} (h : w1 = w2) {v : Value w1}
    (hv : Value.CanBeAssignedTo v) : Value.CanBeAssignedTo (h ▸ v) := by
  cases h
  exact hv

theorem Value.concatList_assignable (w : Nat) (ps : List (Σ w, Value w))
    (h : (ps.map (·.1)).toArray.foldl Nat.add 0 = w) (hps : AllAssignable ps) :
    (Value.concatList w ps h).CanBeAssignedTo :=
  .concat _ _ h fun i =>
    canBeAssignedTo_cast (concatList_width ps i) (hps.get i.1 (concatList_lt ps i))

/-- Signals read by a value. This is coarse: a `partSelect` reads its whole
source, and a `concat` reads all of its parts. -/
def Value.signals : {width : Nat} → Value width → List (Σ width, Signal width)
  | _, .const _ => []
  | w, .signal s => [⟨w, s⟩]
  | _, .not a => Value.signals a
  | _, .and a b => Value.signals a ++ Value.signals b
  | _, .or a b => Value.signals a ++ Value.signals b
  | _, .xor a b => Value.signals a ++ Value.signals b
  | _, .mux sel a b => Value.signals sel ++ Value.signals a ++ Value.signals b
  | _, .adc a b cin => Value.signals a ++ Value.signals b ++ Value.signals cin
  | _, .eq a b => Value.signals a ++ Value.signals b
  | _, .ult a b => Value.signals a ++ Value.signals b
  | _, .slt a b => Value.signals a ++ Value.signals b
  | _, .eqx a b => Value.signals a ++ Value.signals b
  | _, .shl _ _ a amt => Value.signals a ++ Value.signals amt
  | _, .ushr _ _ a amt => Value.signals a ++ Value.signals amt
  | _, .sshr _ _ a amt => Value.signals a ++ Value.signals amt
  | _, .xshr _ _ a amt => Value.signals a ++ Value.signals amt
  | _, .replicate _ a => Value.signals a
  | _, .mul a b => Value.signals a ++ Value.signals b
  | _, .udiv a b => Value.signals a ++ Value.signals b
  | _, .umod a b => Value.signals a ++ Value.signals b
  | _, .sdivTrunc a b => Value.signals a ++ Value.signals b
  | _, .sdivFloor a b => Value.signals a ++ Value.signals b
  | _, .smodTrunc a b => Value.signals a ++ Value.signals b
  | _, .smodFloor a b => Value.signals a ++ Value.signals b
  | _, .concatNode _ ws parts _ =>
      (List.finRange ws.size).flatMap (fun i => Value.signals (parts i))
  | _, .partSelect _ src _ _ => Value.signals src

/-- Port direction. -/
inductive Direction where
  | In
  | Out
  deriving DecidableEq, Repr

/-- A port references a `Value`. Input ports carry an assignability proof. -/
inductive Port (width : Nat) where
  | In (name : String) (value : Value width)
      (ok : Value.CanBeAssignedTo value) : Port width
  | Out (name : String) (value : Value width) : Port width

def Port.value {width : Nat} : Port width → Value width
  | .In _ value _ => value
  | .Out _ value => value

def Port.name {width : Nat} : Port width → String
  | .In name _ _ => name
  | .Out name _ => name

/-- An assignment of a `Value` to an assignable target. -/
structure Assignment where
  width : Nat
  target : Value width
  target_ok : Value.CanBeAssignedTo target
  source : Value width

/-- An asynchronous load: while `trigger` is at level `polarity`, the register
output is forced to `value` (e.g. an active-low reset `rst_ni` has
`polarity := false` and a constant `value`). -/
structure AsyncLoad (width : Nat) where
  trigger : Value 1
  polarity : Bool
  value : Value width

/-- An edge-triggered register: on each `clk` edge of polarity `clkPolarity`
(`true` = rising) `q` takes the value of `d`, unless an asynchronous load is
active. -/
structure Register (width : Nat) where
  q : Value width
  q_ok : Value.CanBeAssignedTo q
  d : Value width
  clk : Value 1
  clkPolarity : Bool := true
  aloads : List (AsyncLoad width) := []
  init : TritVec width

/-- A netlist is a signal table plus ports, assignments, and registers. -/
structure Netlist where
  signals : List (Σ width, Signal width)
  ports : List (Σ width, Port width)
  assignments : List Assignment
  registers : List (Σ width, Register width)

namespace Value

/-- All signals read by `v` occur in the netlist's signal table. -/
inductive InNetlist (n : Netlist) : {width : Nat} → Value width → Prop where
  | const {width : Nat} (c : TritVec width) : InNetlist n (.const c)
  | signal {width : Nat} (s : Signal width) :
      (⟨width, s⟩ : Σ width, Signal width) ∈ n.signals → InNetlist n (.signal s)
  | not {width : Nat} {a : Value width} :
      InNetlist n a → InNetlist n (.not a)
  | and {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.and a b)
  | or {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.or a b)
  | xor {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.xor a b)
  | mux {width : Nat} {sel : Value 1} {a b : Value width} :
      InNetlist n sel → InNetlist n a → InNetlist n b → InNetlist n (.mux sel a b)
  | adc {width : Nat} {a b : Value width} {cin : Value 1} :
      InNetlist n a → InNetlist n b → InNetlist n cin → InNetlist n (.adc a b cin)
  | eq {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.eq a b)
  | ult {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.ult a b)
  | slt {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.slt a b)
  | eqx {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.eqx a b)
  | shl {width amt : Nat} {stride : Nat} {a : Value width} {amount : Value amt} :
      InNetlist n a → InNetlist n amount → InNetlist n (.shl stride amt a amount)
  | ushr {width amt : Nat} {stride : Nat} {a : Value width} {amount : Value amt} :
      InNetlist n a → InNetlist n amount → InNetlist n (.ushr stride amt a amount)
  | sshr {width amt : Nat} {stride : Nat} {a : Value width} {amount : Value amt} :
      InNetlist n a → InNetlist n amount → InNetlist n (.sshr stride amt a amount)
  | xshr {width amt : Nat} {stride : Nat} {a : Value width} {amount : Value amt} :
      InNetlist n a → InNetlist n amount → InNetlist n (.xshr stride amt a amount)
  | replicate {width : Nat} {a : Value 1} :
      InNetlist n a → InNetlist n (.replicate width a)
  | mul {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.mul a b)
  | udiv {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.udiv a b)
  | umod {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.umod a b)
  | sdivTrunc {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.sdivTrunc a b)
  | sdivFloor {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.sdivFloor a b)
  | smodTrunc {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.smodTrunc a b)
  | smodFloor {width : Nat} {a b : Value width} :
      InNetlist n a → InNetlist n b → InNetlist n (.smodFloor a b)
  | concatNode {width : Nat} {ws : Array Nat}
      {parts : (i : Fin ws.size) → Value ws[i]}
      {h : ws.foldl Nat.add 0 = width} :
      (∀ i, InNetlist n (parts i)) → InNetlist n (.concatNode width ws parts h)
  | partSelect {width srcWidth : Nat} {src : Value srcWidth} {offset : Nat}
      {h : offset + width ≤ srcWidth} :
      InNetlist n src → InNetlist n (.partSelect srcWidth src offset h)

end Value

end Grounding.Rtl
