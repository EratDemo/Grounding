-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL driver invariant.

`SignalRef`, `Drives`, and `Netlist.WellFormed` are kept separate from the core
netlist types so they can validate a netlist without being part of its data.
-/

import Grounding.Rtl.Netlist

namespace Grounding.Rtl

/-- A bit of a signal. -/
structure SignalRef (width : Nat) where
  signal : Signal width
  bit : Fin width
  deriving DecidableEq, Repr

/-- Bit offsets of the parts of a `concatNode`. Parts are MSB-first, so part `i`
starts at the total width of the parts after it (matching `Valuation.eval`). -/
def concatOffsets (ws : Array Nat) : Array Nat :=
  (ws.foldr (fun w (acc : List Nat × Nat) => (acc.2 :: acc.1, acc.2 + w)) ([], 0)).1.toArray

/-- The bit offset of part `i` of a `concatNode` with part widths `ws`. -/
def concatOffset (ws : Array Nat) (i : Nat) : Nat := (concatOffsets ws).getD i 0

/--
`DrivesAt v ok p b` means that using `v` (with assignability proof `ok`) as an
lvalue drives bit `b` of some signal from bit position `p` of `v` (LSB = 0).
`signalWidth` is the width of the signal owning the driven bit; it can differ
from the value width (e.g. a concat).
-/
inductive DrivesAt : {valueWidth : Nat} → (v : Value valueWidth) →
    Value.CanBeAssignedTo v → Nat → {signalWidth : Nat} →
    SignalRef signalWidth → Prop where
  | signal {width : Nat} (s : Signal width) (i : Fin width) :
      DrivesAt (.signal s) (Value.CanBeAssignedTo.signal s) i.val ⟨s, i⟩
  | concat {valueWidth : Nat} (ws : Array Nat)
      (parts : (i : Fin ws.size) → Value ws[i])
      (h : ws.foldl Nat.add 0 = valueWidth)
      (hparts : ∀ i, Value.CanBeAssignedTo (parts i))
      (i : Fin ws.size) {p : Nat} {signalWidth : Nat} {b : SignalRef signalWidth}
      (hb : DrivesAt (parts i) (hparts i) p b) :
      DrivesAt (.concatNode valueWidth ws parts h)
        (Value.CanBeAssignedTo.concat (width := valueWidth) ws parts h hparts)
        (concatOffset ws i + p) b
  | partSelect {valueWidth : Nat} (srcWidth : Nat) (src : Value srcWidth)
      (offset : Nat) (h : offset + valueWidth ≤ srcWidth)
      (hsrc : Value.CanBeAssignedTo src)
      {p : Nat} {signalWidth : Nat} {b : SignalRef signalWidth}
      (hb : DrivesAt src hsrc (offset + p) b) (hp : p < valueWidth) :
      DrivesAt (.partSelect srcWidth src offset h)
        (Value.CanBeAssignedTo.partSelect (width := valueWidth) srcWidth src offset h hsrc) p b

/-- `Drives v ok b`: some bit position of the lvalue `v` drives signal bit `b`. -/
def Drives {valueWidth : Nat} (v : Value valueWidth) (ok : Value.CanBeAssignedTo v)
    {signalWidth : Nat} (b : SignalRef signalWidth) : Prop :=
  ∃ p, DrivesAt v ok p b

/-- A value together with the proof that it can be assigned to. -/
structure Driver where
  width : Nat
  value : Value width
  ok : Value.CanBeAssignedTo value

/-- An input port drives its value; an output port does not. -/
def Port.driver? {width : Nat} : Port width → Option Driver
  | .In _ value ok => some ⟨width, value, ok⟩
  | .Out _ _ => none

/-- The drivers of a netlist: input ports, assignment targets, and register
`q` values. -/
def Netlist.drivers (n : Netlist) : List Driver :=
  n.ports.filterMap (fun p => p.2.driver?) ++
  n.assignments.map (fun a => ⟨a.width, a.target, a.target_ok⟩) ++
  n.registers.map (fun r => ⟨r.1, r.2.q, r.2.q_ok⟩)

/-- Signal bit `b` has exactly one driving (driver index, bit position) pair:
two drivers with the same target, or one target that drives the bit from two
positions (e.g. `{y, y}`), both violate it. -/
def Netlist.UniqueDriver (n : Netlist) {width : Nat} (b : SignalRef width) : Prop :=
  ∃ k p, ∃ hk : k < n.drivers.length,
    DrivesAt n.drivers[k].value n.drivers[k].ok p b ∧
    ∀ k' p', ∀ hk' : k' < n.drivers.length,
      DrivesAt n.drivers[k'].value n.drivers[k'].ok p' b → k' = k ∧ p' = p

/-- All signals referenced anywhere in the netlist: assignment targets and
sources, port values, and register `q`/`d`/`clk`/async-load values. -/
def Netlist.referencedSignals (n : Netlist) : List (Σ w, Signal w) :=
  n.ports.flatMap (fun p => Value.signals p.2.value) ++
  n.assignments.flatMap (fun a => Value.signals a.target ++ Value.signals a.source) ++
  n.registers.flatMap (fun r =>
    Value.signals r.2.q ++ Value.signals r.2.d ++ Value.signals r.2.clk ++
      r.2.aloads.flatMap (fun al =>
        Value.signals al.trigger ++ Value.signals al.value))

/-- Signal identity is coherent: two referenced or declared signals with the
same width and id are the same signal (so a name is never attached to two
different signals with one id). The scheduler identifies signals by
`(width, id)`; this is what makes that sound. -/
def Netlist.IdsCoherent (n : Netlist) : Prop :=
  ∀ s ∈ n.signals ++ n.referencedSignals, ∀ t ∈ n.signals ++ n.referencedSignals,
    s.1 = t.1 → s.2.id = t.2.id → s = t

/--
A well-formed netlist:
* signal ids in the signal table are unique;
* every signal referenced by the netlist is in the signal table;
* signal identity is coherent (`IdsCoherent`);
* every bit of every signal in the table has exactly one driver among the
  input ports, assignment targets, and register `q` values.
-/
structure Netlist.WellFormed (n : Netlist) : Prop where
  ids_unique : (n.signals.map (·.2.id)).Nodup
  referenced : ∀ s ∈ n.referencedSignals, s ∈ n.signals
  coherent : n.IdsCoherent
  unique_driver : ∀ (s : Σ width, Signal width), s ∈ n.signals →
    ∀ i : Fin s.1, n.UniqueDriver ⟨s.2, i⟩

end Grounding.Rtl
