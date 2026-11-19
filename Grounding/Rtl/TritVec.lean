-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL three-valued constants.
-/

import Grounding.Rtl.Netlist
import Batteries.Data.List.Lemmas
import Init.Data.BitVec.Lemmas

namespace Grounding.Rtl

/-! ### Three-valued bit operations -/

namespace Trit

def not : Trit → Trit
  | zero => one
  | one => zero
  | x => x

def and : Trit → Trit → Trit
  | zero, _ => zero
  | _, zero => zero
  | one, one => one
  | _, _ => x

def or : Trit → Trit → Trit
  | one, _ => one
  | _, one => one
  | zero, zero => zero
  | _, _ => x

def xor : Trit → Trit → Trit
  | x, _ => x
  | _, x => x
  | zero, zero => zero
  | one, one => zero
  | zero, one => one
  | one, zero => one

def mux (sel a b : Trit) : Trit :=
  if sel == one then a
  else if sel == zero then b
  else if a == b then a
  else x

/-- The defined trit for a Boolean. -/
def ofBool (b : Bool) : Trit := if b then one else zero

end Trit

/-! ### One adder stage -/

namespace Trit

/-- The sum digit of one adc stage. -/
def sumT (a b c : Trit) : Trit :=
  if a == Trit.x || b == Trit.x || c == Trit.x then Trit.x
  else if a == Trit.zero && b == Trit.zero then c
  else if a == Trit.one && b == Trit.one then c
  else Trit.not c

/-- The carry out of one adc stage. -/
def carT (a b c : Trit) : Trit :=
  if a == Trit.x || b == Trit.x || c == Trit.x then Trit.x
  else if a == Trit.zero && b == Trit.zero then Trit.zero
  else if a == Trit.one && b == Trit.one then Trit.one
  else c

end Trit

/-! ### Constant operations -/

namespace TritVec

def zero (width : Nat) : TritVec width := ⟨Vector.replicate width Trit.zero⟩
def ones (width : Nat) : TritVec width := ⟨Vector.replicate width Trit.one⟩
def undef (width : Nat) : TritVec width := ⟨Vector.replicate width Trit.x⟩
def fromTrit (t : Trit) : TritVec 1 := ⟨Vector.replicate 1 t⟩

def bit0 (c : TritVec 1) : Trit := c.bits.get ⟨0, by omega⟩

/-- Repeat a single-bit constant `n` times. -/
def replicate (n : Nat) (c : TritVec 1) : TritVec n := ⟨Vector.replicate n (bit0 c)⟩

def msb? (c : TritVec width) : Option Trit := c.bits.toList.getLast?
def hasUndef (c : TritVec width) : Bool := c.bits.toList.any (fun t => t == Trit.x)

def ofList (l : List Trit) : TritVec l.length :=
  ⟨Vector.mk l.toArray (by simp)⟩

def not_ (a : TritVec width) : TritVec width :=
  ⟨Vector.map Trit.not a.bits⟩

def and_ (a b : TritVec width) : TritVec width :=
  ⟨Vector.ofFn (fun i => Trit.and (a.bits.get i) (b.bits.get i))⟩

def or_ (a b : TritVec width) : TritVec width :=
  ⟨Vector.ofFn (fun i => Trit.or (a.bits.get i) (b.bits.get i))⟩

def xor_ (a b : TritVec width) : TritVec width :=
  ⟨Vector.ofFn (fun i => Trit.xor (a.bits.get i) (b.bits.get i))⟩

def mux (sel : Trit) (a b : TritVec width) : TritVec width :=
  ⟨Vector.ofFn (fun i => Trit.mux sel (a.bits.get i) (b.bits.get i))⟩

def slice (a : TritVec srcWidth) (offset width : Nat)
    (h : offset + width ≤ srcWidth) : TritVec width :=
  ⟨Vector.ofFn (fun i => a.bits.get ⟨offset + i.val, by omega⟩)⟩

def concat (a : TritVec width₁) (b : TritVec width₂) : TritVec (width₁ + width₂) :=
  ⟨Vector.ofFn (fun i =>
    if h : i.val < width₁ then a.bits.get ⟨i.val, h⟩
    else b.bits.get ⟨i.val - width₁, by omega⟩)⟩

/-! #### Addition -/

def adcBits : List Trit → List Trit → Trit → List Trit × Trit
  | [], [], carry => ([], carry)
  | a :: as, b :: bs, carry =>
      let r := adcBits as bs (Trit.carT a b carry)
      (Trit.sumT a b carry :: r.1, r.2)
  | _, _, carry => ([], carry)

theorem adcBits_length : ∀ (as bs : List Trit) (carry : Trit),
    as.length = bs.length → (adcBits as bs carry).1.length = as.length
  | [], [], _, _ => rfl
  | a :: as, b :: bs, carry, h => by
      simp [adcBits, adcBits_length as bs _ (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

def adc (a b : TritVec width) (cin : Trit) : TritVec (width + 1) :=
  let r := adcBits a.bits.toList b.bits.toList cin
  let l := r.1 ++ [r.2]
  have hl : l.length = width + 1 := by
    simp [l, r, adcBits_length a.bits.toList b.bits.toList cin (by simp)]
  hl ▸ ofList l

/-! #### Comparisons -/

def eqBits : List Trit → List Trit → Trit
  | [], [] => Trit.one
  | a :: as, b :: bs =>
      let r := eqBits as bs
      if r == Trit.zero then Trit.zero
      else if a == Trit.x || b == Trit.x then Trit.x
      else if a == b then r
      else Trit.zero
  | _, _ => Trit.x

def eq (a b : TritVec width) : TritVec 1 :=
  fromTrit (eqBits a.bits.toList b.bits.toList)

/-- Case equality: X compares literally, the result is never X. -/
def eqx (a b : TritVec width) : TritVec 1 :=
  fromTrit (if a = b then Trit.one else Trit.zero)

/-- Unsigned `a < b` on equal-length LSB-first bit lists without X. Scanning
from the LSB, each differing bit overrides the verdict so far, so the most
significant differing bit decides. -/
def ultBits (as bs : List Trit) : Trit :=
  (as.zip bs).foldl (fun r (a, b) =>
    if a == b then r else if a == Trit.zero then Trit.one else Trit.zero) Trit.zero

def ult (a b : TritVec width) : TritVec 1 :=
  if a.hasUndef || b.hasUndef then fromTrit Trit.x
  else fromTrit (ultBits a.bits.toList b.bits.toList)

def slt (a b : TritVec width) : TritVec 1 :=
  if a.hasUndef || b.hasUndef then fromTrit Trit.x
  else
    match a.msb?, b.msb? with
    | some sa, some sb =>
        if sa == sb then fromTrit (ultBits a.bits.toList b.bits.toList)
        else if sa == Trit.one then fromTrit Trit.one
        else fromTrit Trit.zero
    | _, _ => fromTrit Trit.zero

/-! #### Shifts -/

def shiftAmountAux : List Trit → Nat → Option Nat
  | [], _ => some 0
  | t :: ts, idx =>
      match shiftAmountAux ts (idx + 1) with
      | none => none
      | some high =>
          if t == Trit.one then
            if idx >= 32 then none else some (high * 2 + 1)
          else some (high * 2)

/-- The value of a shift amount, or `none` if it is at least `2^32` (such a
shift moves every bit out). The amount must not contain X. -/
def shiftAmount? (c : TritVec width) : Option Nat := shiftAmountAux c.bits.toList 0

def sign (a : TritVec width) : Trit :=
  if h : width = 0 then Trit.x
  else a.bits.get ⟨width - 1, by omega⟩

/-- Shift `a` by `stride * amt` (left or right), filling vacated bits with
`fill`. An amount containing X gives all-X. `stride` is assumed positive
(native `Bmux`/`Demux` use the slot width; ordinary shifts use 1). -/
def shiftBy (left : Bool) (fill : Trit) (stride : Nat)
    (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  if amt.hasUndef then undef width
  else
    match shiftAmount? amt with
    | none => ⟨Vector.replicate width fill⟩
    | some s =>
      let d := s * stride
      if d ≥ 2 ^ 32 then ⟨Vector.replicate width fill⟩
      else ⟨Vector.ofFn (fun i =>
        if left then
          if hi : d ≤ i.val then a.bits.get ⟨i.val - d, by omega⟩ else fill
        else
          if hi : i.val + d < width then a.bits.get ⟨i.val + d, hi⟩ else fill)⟩

def shl (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy true Trit.zero 1 a amt

def ushr (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy false Trit.zero 1 a amt

def sshr (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy false (sign a) 1 a amt

def xshr (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy false Trit.x 1 a amt

def shlStride (stride : Nat) (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy true Trit.zero stride a amt

def ushrStride (stride : Nat) (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy false Trit.zero stride a amt

def sshrStride (stride : Nat) (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy false (sign a) stride a amt

def xshrStride (stride : Nat) (a : TritVec width) (amt : TritVec amountWidth) : TritVec width :=
  shiftBy false Trit.x stride a amt

/-! #### Two-valued projection -/

/-- Project a `TritVec` to a two-valued `BitVec`, tying every `Trit.x` down to
`false`. `TritVec.bits` and `BitVec.ofBoolListLE` are both LSB-first. -/
def tieDownX (c : TritVec width) : BitVec width :=
  BitVec.cast (by simp : (c.bits.toList.map (fun t => t == Trit.one)).length = width)
    (BitVec.ofBoolListLE (c.bits.toList.map (fun t => t == Trit.one)))

@[simp] theorem tieDownX_getLsbD (c : TritVec width) (i : Nat) :
    (tieDownX c).getLsbD i = (c.bits.toList.getD i Trit.zero == Trit.one) := by
  simp only [tieDownX, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  cases h : c.bits[i]? <;> simp [h]

/-- A two-valued constant from a `BitVec` (LSB-first). -/
def ofBV (v : BitVec width) : TritVec width :=
  ⟨Vector.ofFn (fun i => Trit.ofBool (v.getLsbD i.val))⟩

attribute [coe] ofBV

/-- A `BitVec` is a fully-defined `TritVec`, so `sv_eval% V "x" = 7#8` elaborates. -/
instance : Coe (BitVec width) (TritVec width) := ⟨ofBV⟩

/-! #### Multiplication -/

/-- Any X in an operand makes the whole product X; otherwise this is `BitVec`
multiplication modulo `2^width`. -/
def mul (a b : TritVec width) : TritVec width :=
  if a.hasUndef || b.hasUndef then undef width
  else ofBV (tieDownX a * tieDownX b)

/-! #### Concatenation -/

/-- Read `width` trits from an LSB-first array, padding with `X`. Used for
`concatNode`, whose parts are gathered in one linear pass; the array always has
exactly `width` entries for a well-typed node. -/
def ofArrayD (width : Nat) (a : Array Trit) : TritVec width :=
  ⟨Vector.ofFn (fun i => a.getD i.val Trit.x)⟩

theorem ofArrayD_toArray {a : Array Trit} (h : a.size = w) : (TritVec.ofArrayD w a).bits.toArray = a := by
  apply Array.ext
  · simp [h]
  · intro i h1 h2
    simp only [TritVec.ofArrayD, Vector.toArray_ofFn, Array.getElem_ofFn]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]

/-- `a` above `b` (MSB first), read back at width `w`. -/
def appendW (a : TritVec n) (b : TritVec m) (w : Nat) : TritVec w :=
  ofArrayD w (b.bits.toArray ++ a.bits.toArray)

end TritVec

end Grounding.Rtl
