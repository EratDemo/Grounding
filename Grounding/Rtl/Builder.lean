-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL builder.

The C++ side keeps the flat-net → signal-bit mapping. It realizes each
`ir::Value` by calling `part_select` on the relevant signal and `concat` over
the resulting one-bit values, then passes the resulting `BuiltValue` to an
operation builder.
-/

import Grounding.Rtl.Netlist

namespace Grounding.Rtl

/-- A constructed value plus an optional assignability proof. -/
structure BuiltValue where
  width : Nat
  value : Value width
  assignable : Option (PLift (Value.CanBeAssignedTo value))

/-- A concrete asynchronous load supplied to `addRegister`: trigger, active
level, and the value loaded while the trigger is active. -/
structure BuiltAsyncLoad where
  trigger : BuiltValue
  polarity : Bool
  value : BuiltValue

/-- Builder state. Signal identities are assigned here (the id of a signal is
its index in `signals`); the flat net ids live on the C++ side. -/
structure Builder where
  signals : Array (Σ width, Signal width) := #[]
  ports : Array (Σ width, Port width) := #[]
  assignments : Array Assignment := #[]
  registers : Array (Σ width, Register width) := #[]

namespace Builder

def constOf (width : Nat) (t : Trit) : Const width :=
  ⟨Vector.replicate width t⟩

def zeroValue (width : Nat) : Value width :=
  .const (constOf width .zero)

def oneValue : Value 1 :=
  .const (constOf 1 .one)

def addSignal (b : Builder) (width : Nat) (name : Option String) :
    Builder × BuiltValue :=
  let s : Signal width := ⟨b.signals.size, name⟩
  let v : BuiltValue :=
    ⟨width, Value.signal s, some (PLift.up (Value.CanBeAssignedTo.signal s))⟩
  ({ b with signals := b.signals.push ⟨width, s⟩ }, v)

def addAssignment (b : Builder) (target source : BuiltValue) :
    Option Builder :=
  match target.assignable with
  | none => none
  | some ok =>
    if h : target.width = source.width then
      let source' : Value target.width := h.symm ▸ source.value
      let a : Assignment := ⟨target.width, target.value, ok.down, source'⟩
      some { b with assignments := b.assignments.push a }
    else
      none

/-- Add a register. `clkPol`: `true` = rising edge. `aloads` are asynchronous
loads in priority order: the first load whose trigger is active wins. -/
def addRegister (b : Builder) (q d clk : BuiltValue) (clkPol : Bool)
    (aloads : Array BuiltAsyncLoad := #[]) : Option Builder := do
  let some qok := q.assignable | none
  if hd : d.width = q.width then
    if hc : clk.width = 1 then
      let als : List (AsyncLoad q.width) ←
        aloads.toList.mapM fun al => do
          if ht : al.trigger.width = 1 then
            if hv : al.value.width = q.width then
              pure ⟨ht ▸ al.trigger.value, al.polarity,
                    hv ▸ al.value.value⟩
            else none
          else none
      let reg : Register q.width :=
        { q := q.value, q_ok := qok.down, d := hd ▸ d.value,
          clk := hc ▸ clk.value, clkPolarity := clkPol, aloads := als,
          init := constOf q.width .x }
      some { b with registers := b.registers.push ⟨q.width, reg⟩ }
    else none
  else none

def addPort (b : Builder) (name : String) (dir : Direction)
    (value : BuiltValue) : Option Builder :=
  match dir with
  | .In =>
    match value.assignable with
    | none => none
    | some ok =>
      let p : Port value.width := .In name value.value ok.down
      some { b with ports := b.ports.push ⟨value.width, p⟩ }
  | .Out =>
    let p : Port value.width := .Out name value.value
    some { b with ports := b.ports.push ⟨value.width, p⟩ }

end Builder

open Builder

/-- A constant of `width` copies of one trit. `trit` is 0/1/2 (zero/one/x). -/
def constValue (width : Nat) (trit : UInt8) : BuiltValue :=
  let t : Trit :=
    match trit with
    | 0 => .zero
    | 1 => .one
    | _ => .x
  ⟨width, .const (constOf width t), none⟩

/-- A constant from trit codes, LSB first (0/1/2 = zero/one/x per byte). -/
def constBitsValue (codes : ByteArray) : BuiltValue :=
  let trits : Array Trit := codes.data.map fun
    | 0 => Trit.zero
    | 1 => Trit.one
    | _ => Trit.x
  ⟨trits.size, .const ⟨⟨trits, rfl⟩⟩, none⟩

/-- Select `width` bits of a value starting at `offset`. The source may itself
be a concat/part-select. Selecting the whole value returns it unchanged. -/
def partSelect (v : BuiltValue) (offset width : Nat) : Option BuiltValue :=
  if offset = 0 ∧ width = v.width then
    some v
  else if h : offset + width ≤ v.width then
    let value := Value.partSelect v.width v.value offset h
    let assignable := v.assignable.map (fun ok =>
      PLift.up (Value.CanBeAssignedTo.partSelect v.width v.value offset h ok.down))
    some ⟨width, value, assignable⟩
  else
    none

private theorem cbe_cast {w1 w2 : Nat} (h : w1 = w2) {v : Value w1}
    (hv : Value.CanBeAssignedTo v) : Value.CanBeAssignedTo (h ▸ v) := by
  cases h
  exact hv

private theorem concat_lt (parts : Array BuiltValue) (i : Fin (parts.map (·.width)).size) :
    i.val < parts.size := by simpa using i.isLt

private theorem concat_width (parts : Array BuiltValue) (i : Fin (parts.map (·.width)).size) :
    (parts.map (·.width))[i] = (parts[i.val]'(by simpa using i.isLt)).width :=
  Array.getElem_map ..

/-- Part `i` of a concatenation, cast to the width recorded in the width array. -/
private def concatPart (parts : Array BuiltValue) (i : Fin (parts.map (·.width)).size) :
    Value (parts.map (·.width))[i] :=
  (concat_width parts i).symm ▸ (parts[i.val]'(by simpa using i.isLt)).value

/-- Concatenate parts (MSB-first). The width is the sum of the part widths.

Linear in the number of parts: widths and values are read from arrays by
index, and assignability is checked in one pass. -/
def concat (parts : Array BuiltValue) : BuiltValue :=
  let ws := parts.map (·.width)
  let value := Value.concatNode (ws.foldl Nat.add 0) ws (concatPart parts) rfl
  let assignable : Option (PLift (Value.CanBeAssignedTo value)) :=
    if hall : ∀ i : Fin parts.size, parts[i].assignable.isSome then
      some (PLift.up (Value.CanBeAssignedTo.concat ws (concatPart parts) rfl (fun i =>
        cbe_cast (concat_width parts i).symm
          ((parts[i.val]'(concat_lt parts i)).assignable.get
            (hall ⟨i.val, concat_lt parts i⟩)).down)))
    else none
  ⟨_, value, assignable⟩

def mkResult (value : Value n) : BuiltValue := ⟨n, value, none⟩

/-!
### Operations

The C++ backend resolves all SystemVerilog width and signedness rules before
calling these: operands of bitwise and arithmetic operations already have the
result width, comparison operands share one width, and one-bit results are
zero-extended on the C++ side. The constructors below therefore only accept
operands of the exact widths they need and return `none` otherwise.
-/

/-- Unary operations. All but the reductions keep the operand width; the
reductions and `logicNot` produce one bit. -/
inductive Unop where
  | pos | not | minus
  | logicNot | reduceAnd | reduceOr | reduceXor
  deriving DecidableEq, Repr

/-- Binary operations on operands of one width. `and` … `mul` keep the width;
the comparisons produce one bit (`u*` unsigned, `s*` signed). -/
inductive Biop where
  | and | or | xor | xnor
  | add | sub | mul
  | eq | ne | eqx | nex
  | ult | ule | ugt | uge
  | slt | sle | sgt | sge
  deriving DecidableEq, Repr

/-- Shift kinds. `a` keeps its width; the amount is an unsigned value of any
width. -/
inductive Shiftop where
  | shl | ushr | sshr
  deriving DecidableEq, Repr

/-- Reduce-xor by a chain of one-bit `xor`s over the bits of `a`. -/
private def reduceXorValue {w : Nat} (a : Value w) : Value 1 :=
  (List.range w).foldl (fun acc i =>
    if h : i + 1 ≤ w then Value.xor acc (Value.partSelect w a i h) else acc)
    (zeroValue 1)

private def lowAdc {w : Nat} (a b : Value w) (cin : Value 1) : Value w :=
  Value.partSelect (w + 1) (Value.adc a b cin) 0 (by omega)

def mkUnop (op : Unop) (a : BuiltValue) : BuiltValue :=
  match op with
  | .pos => a
  | .not => mkResult (Value.not a.value)
  | .minus =>
    mkResult (lowAdc (Value.not a.value) (zeroValue a.width) oneValue)
  | .logicNot => mkResult (Value.eq a.value (zeroValue a.width))
  | .reduceAnd => mkResult (Value.eq a.value (.const (constOf a.width .one)))
  | .reduceOr => mkResult (Value.not (Value.eq a.value (zeroValue a.width)))
  | .reduceXor => mkResult (reduceXorValue a.value)

def mkBiop (op : Biop) (a b : BuiltValue) : Option BuiltValue :=
  if h : b.width = a.width then
    let x := a.value
    let y : Value a.width := h ▸ b.value
    some <| match op with
      | .and => mkResult (Value.and x y)
      | .or => mkResult (Value.or x y)
      | .xor => mkResult (Value.xor x y)
      | .xnor => mkResult (Value.not (Value.xor x y))
      | .add => mkResult (lowAdc x y (zeroValue 1))
      | .sub => mkResult (lowAdc x (Value.not y) oneValue)
      | .mul => mkResult (Value.mul x y)
      | .eq => mkResult (Value.eq x y)
      | .ne => mkResult (Value.not (Value.eq x y))
      | .eqx => mkResult (Value.eqx x y)
      | .nex => mkResult (Value.not (Value.eqx x y))
      | .ult => mkResult (Value.ult x y)
      | .ule => mkResult (Value.not (Value.ult y x))
      | .ugt => mkResult (Value.ult y x)
      | .uge => mkResult (Value.not (Value.ult x y))
      | .slt => mkResult (Value.slt x y)
      | .sle => mkResult (Value.not (Value.slt y x))
      | .sgt => mkResult (Value.slt y x)
      | .sge => mkResult (Value.not (Value.slt x y))
  else
    none

def mkShift (op : Shiftop) (stride : Nat) (a s : BuiltValue) : BuiltValue :=
  match op with
  | .shl => mkResult (Value.shl stride s.width a.value s.value)
  | .ushr => mkResult (Value.ushr stride s.width a.value s.value)
  | .sshr => mkResult (Value.sshr stride s.width a.value s.value)

/-- `xshr`: logical right shift filling with X (for `Shiftx`). -/
def mkShiftx (stride : Nat) (a s : BuiltValue) : BuiltValue :=
  mkResult (Value.xshr stride s.width a.value s.value)

/-- Repeat a one-bit value `width` times. -/
def mkReplicate (width : Nat) (a : BuiltValue) : Option BuiltValue :=
  if h : a.width = 1 then some (mkResult (Value.replicate width (h ▸ a.value))) else none

/-- `sel ? a : b`. -/
def mkMux (sel a b : BuiltValue) : Option BuiltValue :=
  if hs : sel.width = 1 then
    if h : b.width = a.width then
      some (mkResult (Value.mux (hs ▸ sel.value) a.value (h ▸ b.value)))
    else
      none
  else
    none

/-! ### Exports -/

@[export grounding_builder_new]
def builderNew (_ : Unit) : Builder := {}

@[export grounding_builder_add_signal]
def builderAddSignal (b : Builder) (width : Nat) (name : String) :
    Builder × BuiltValue :=
  b.addSignal width (if name.isEmpty then none else some name)

@[export grounding_builder_const]
def builderConst (width : Nat) (trit : UInt8) : BuiltValue :=
  constValue width trit

@[export grounding_builder_const_bits]
def builderConstBits (codes : ByteArray) : BuiltValue :=
  constBitsValue codes

@[export grounding_builder_part_select]
def builderPartSelect (v : BuiltValue) (offset width : Nat) : Option BuiltValue :=
  partSelect v offset width

@[export grounding_builder_concat]
def builderConcat (parts : Array BuiltValue) : BuiltValue :=
  concat parts

@[export grounding_builder_add_port]
def builderAddPort (b : Builder) (name : String) (dir : Direction)
    (value : BuiltValue) : Option Builder :=
  b.addPort name dir value

@[export grounding_builder_add_assignment]
def builderAddAssignment (b : Builder) (target source : BuiltValue) :
    Option Builder :=
  b.addAssignment target source

@[export grounding_builder_add_register]
def builderAddRegister (b : Builder) (q d clk : BuiltValue) (clkPol : UInt8) :
    Option Builder :=
  b.addRegister q d clk (clkPol != 0)

@[export grounding_builder_add_aload_register]
def builderAddAloadRegister (b : Builder) (q d clk : BuiltValue) (clkPol : UInt8)
    (trig : BuiltValue) (trigPol : UInt8) (value : BuiltValue) : Option Builder :=
  b.addRegister q d clk (clkPol != 0)
    #[⟨trig, trigPol != 0, value⟩]

/-- Two asynchronous loads in priority order (the first active one wins). -/
@[export grounding_builder_add_aload2_register]
def builderAddAload2Register (b : Builder) (q d clk : BuiltValue) (clkPol : UInt8)
    (trig1 : BuiltValue) (trig1Pol : UInt8) (value1 : BuiltValue)
    (trig2 : BuiltValue) (trig2Pol : UInt8) (value2 : BuiltValue) :
    Option Builder :=
  b.addRegister q d clk (clkPol != 0)
    #[⟨trig1, trig1Pol != 0, value1⟩, ⟨trig2, trig2Pol != 0, value2⟩]

/-! These construct expression values without touching the builder. The C++
side binds the result to the flat nets it allocated for the operation, so an
intermediate operation does not become a `Signal` or an `Assignment`.
Operation codes are the constructor indices of `Unop`/`Biop`/`Shiftop`. -/

@[export grounding_builder_make_unop]
def builderMakeUnop (op : Unop) (a : BuiltValue) : BuiltValue :=
  mkUnop op a

@[export grounding_builder_make_biop]
def builderMakeBiop (op : Biop) (a b : BuiltValue) : Option BuiltValue :=
  mkBiop op a b

@[export grounding_builder_make_shift]
def builderMakeShift (op : Shiftop) (stride : Nat) (a s : BuiltValue) : BuiltValue :=
  mkShift op stride a s

@[export grounding_builder_make_shiftx]
def builderMakeShiftx (stride : Nat) (a s : BuiltValue) : BuiltValue :=
  mkShiftx stride a s

@[export grounding_builder_make_replicate]
def builderMakeReplicate (width : Nat) (a : BuiltValue) : Option BuiltValue :=
  mkReplicate width a

@[export grounding_builder_make_mux]
def builderMakeMux (sel a b : BuiltValue) : Option BuiltValue :=
  mkMux sel a b

@[export grounding_builder_finish]
def builderFinish (b : Builder) : Netlist :=
  { signals := b.signals.toList
    ports := b.ports.toList
    assignments := b.assignments.toList
    registers := b.registers.toList }

end Grounding.Rtl
