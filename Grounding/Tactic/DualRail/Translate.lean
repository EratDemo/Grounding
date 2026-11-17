-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
`Value` to rail translation.

`Ctx` holds the per-signal atoms and `tr` walks a `Value` bottom-up, producing a
mask, a value and a `Rail.Ev` proof for each node. Memoised by pointer so that
shared `Value` nodes (and barrel-shifter stages) are translated once.
-/

import Grounding.Tactic.DualRail.Ev

namespace Grounding.Tactic.BvDualRail

open Lean Meta Elab Tactic
open Grounding.Rtl

/-- The elements of a list literal. -/
partial def listItems (e : Expr) : Array Expr := Id.run do
  let mut e := e
  let mut out := #[]
  while e.isAppOfArity ``List.cons 3 do
    out := out.push e.appFn!.appArg!
    e := e.appArg!
  return out

def natLit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => e.rawNatLit?

/-- A signal literal `Signal.mk w id name`: its id. -/
def signalId? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``Signal.mk 3 then natLit? e.appFn!.appArg! else none

/-- `w ≤ 2^32` for a literal width, by `Nat.ble`. -/
def le2pow32 (w : Expr) : MetaM (Option Expr) := do
  let some n := natLit? w | return none
  if n ≤ 2 ^ 32 then
    return some (mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit n) (mkNatLit (2 ^ 32))
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))
  return none

/-- `a ≤ b` for literal `a`, `b`, by `Nat.ble`. -/
def leLit (a b : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit a) (mkNatLit b)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Translation context: signal id ↦ (mask term, value term, proof `Rail (V s) m v`). -/
structure Ctx where
  V : Expr
  sigs : Std.HashMap Nat (Expr × Expr × Expr)

abbrev TM := ReaderT Ctx (StateRefT (Std.HashMap USize (Option (Expr × Expr × Expr))) MetaM)

def bv (w : Expr) : Expr := mkApp (mkConst ``BitVec) w

/-- Rail of an embedded constant: mask and value literals, proof by `decide`. -/
def constRail? (w c : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some wn := natLit? w | return none
  let vec := c.appArg!
  unless vec.isAppOfArity ``Vector.mk 4 do return none
  let arr := vec.appFn!.appArg!
  -- `List.toArray` is an `abbrev`, so reducible unfolding may have turned the
  -- array into `Array.mk`. Accept both spellings.
  let list ←
    if arr.isAppOfArity ``List.toArray 2 then pure arr.appArg!
    else if arr.isAppOfArity ``Array.mk 2 then pure arr.appArg!
    else return none
  let bits := listItems list
  let mut mx := 0
  let mut vv := 0
  for i in [0:bits.size] do
    let b := bits[i]!
    if b.isConstOf ``Trit.one then vv := vv + 2 ^ i
    else if b.isConstOf ``Trit.x then mx := mx + 2 ^ i
  let x := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit wn) (mkNatLit mx)
  let v := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit wn) (mkNatLit vv)
  -- Rail c x v  ⇐  maskOf c = x ∧ valOf c = v  (closed, by decide)
  let eqs ← mkAppM ``And #[← mkEq (mkApp2 (mkConst ``Rail.Ev.maskOf) w c) x,
    ← mkEq (mkApp2 (mkConst ``Rail.Ev.valOf) w c) v]
  let pfEqs ← mkDecideProof eqs
  let pf ← mkAppM ``Rail.Ev.rail_of_self_eq #[pfEqs]
  return some (x, v, pf)

/-- Translate an embedded `Value`; `(mask, value, proof : IsR V e mask value)`. -/
partial def tr (e : Expr) : TM (Option (Expr × Expr × Expr)) := do
  let p := unsafe ptrAddrUnsafe e
  if let some r := (← get)[p]? then return r
  let r ← go e
  modify (·.insert p r)
  return r
where
  /-- Apply a binary rail lemma `L {V w a b xa va xb vb} ha hb`; the result rails
  are read off the lemma's statement. -/
  bin (lem : Name) (w a b : Expr) : TM (Option (Expr × Expr × Expr)) := do
    let some (xa, va, ha) ← tr a | return none
    let some (xb, vb, hb) ← tr b | return none
    let pf := mkAppN (mkConst lem) #[(← read).V, w, a, b, xa, va, xb, vb, ha, hb]
    result pf
  /-- The rails of a proof `pf : IsR V e x v`, from the lemma's type. -/
  result (pf : Expr) : TM (Option (Expr × Expr × Expr)) := do
    let ty ← instantiateForall (← inferType pf) #[]
    let ty ← whnfR ty
    -- IsR V e x v  is  Rail (V.eval e) x v
    let args := ty.getAppArgs
    return some (args[args.size - 2]!, args[args.size - 1]!, pf)
  go (e : Expr) : TM (Option (Expr × Expr × Expr)) := do
    let V := (← read).V
    let args := e.getAppArgs
    let some c := e.getAppFn.constName? | return none
    match c, args.size with
    | ``Value.signal, 2 =>
      let some id := signalId? args[1]! | return none
      let some (x, v, h) := (← read).sigs[id]? | return none
      return some (x, v, mkAppN (mkConst ``Rail.Ev.signal) #[V, args[0]!, args[1]!, x, v, h])
    | ``Value.const, 2 =>
      let some (x, v, h) ← constRail? args[0]! args[1]! | return none
      return some (x, v, mkAppN (mkConst ``Rail.Ev.const) #[V, args[0]!, args[1]!, x, v, h])
    | ``Value.not, 2 =>
      let some (x, v, h) ← tr args[1]! | return none
      result (mkAppN (mkConst ``Rail.Ev.not) #[V, args[0]!, args[1]!, x, v, h])
    | ``Value.and, 3 => bin ``Rail.Ev.and args[0]! args[1]! args[2]!
    | ``Value.or, 3 => bin ``Rail.Ev.or args[0]! args[1]! args[2]!
    | ``Value.xor, 3 => bin ``Rail.Ev.xor args[0]! args[1]! args[2]!
    | ``Value.mul, 3 => bin ``Rail.Ev.mul args[0]! args[1]! args[2]!
    | ``Value.eq, 3 => bin ``Rail.Ev.eq args[0]! args[1]! args[2]!
    | ``Value.eqx, 3 => bin ``Rail.Ev.eqx args[0]! args[1]! args[2]!
    | ``Value.ult, 3 => bin ``Rail.Ev.ult args[0]! args[1]! args[2]!
    | ``Value.slt, 3 => bin ``Rail.Ev.slt args[0]! args[1]! args[2]!
    | ``Value.mux, 4 =>
      let some (xs, vs, hs) ← tr args[1]! | return none
      let some (xa, va, ha) ← tr args[2]! | return none
      let some (xb, vb, hb) ← tr args[3]! | return none
      result (mkAppN (mkConst ``Rail.Ev.mux)
        #[V, args[0]!, args[1]!, args[2]!, args[3]!, xs, vs, xa, va, xb, vb, hs, ha, hb])
    | ``Value.adc, 4 =>
      let some (xa, va, ha) ← tr args[1]! | return none
      let some (xb, vb, hb) ← tr args[2]! | return none
      let some (xc, vc, hc) ← tr args[3]! | return none
      result (mkAppN (mkConst ``Rail.Ev.adc)
        #[V, args[0]!, args[1]!, args[2]!, args[3]!, xa, va, xb, vb, xc, vc, ha, hb, hc])
    | ``Value.replicate, 2 =>
      let some (x, v, h) ← tr args[1]! | return none
      result (mkAppN (mkConst ``Rail.Ev.replicate) #[V, args[0]!, args[1]!, x, v, h])
    | ``Value.shl, 5 | ``Value.ushr, 5 | ``Value.sshr, 5 | ``Value.xshr, 5 =>
      let some stride := natLit? args[1]! | return none
      if stride = 0 then return none
      let some hw ← le2pow32 args[0]! | return none
      if stride ≠ 1 then return ← strided c stride hw args
      let some (xa, va, ha) ← tr args[3]! | return none
      let some (xm, vm, hm) ← tr args[4]! | return none
      let lem := match c with
        | ``Value.shl => ``Rail.Ev.shl
        | ``Value.ushr => ``Rail.Ev.ushr
        | ``Value.sshr => ``Rail.Ev.sshr
        | _ => ``Rail.Ev.xshr
      result (mkAppN (mkConst lem)
        #[V, args[0]!, args[2]!, args[3]!, args[4]!, xa, va, xm, vm, hw, ha, hm])
    | ``Value.partSelect, 5 =>
      let some (x, v, h) ← tr args[2]! | return none
      result (mkAppN (mkConst ``Rail.Ev.partSelect)
        #[V, args[0]!, args[1]!, args[3]!, args[2]!, args[4]!, x, v, h])
    | ``Value.concatList, 3 => concat args[0]! args[1]! args[2]!
    -- TODO: `udiv`, `umod` and the signed div/mod nodes have no rail lemma (they
    -- evaluate to all-X in `Valuation.eval`), so an assignment whose source contains
    -- one is silently skipped and gives `bv_decide` no fact about its target.
    | _, _ => return none
  /-- Strided shift `Value.<op> w stride k a m`: a barrel shifter, one mux per
  amount bit `j` selecting a shift by the literal `stride * 2 ^ j`. The stages are
  built here (`X`, `Y`); the lemma's `barrel … = X` premises hold by `rfl`. -/
  strided (c : Name) (stride : Nat) (hw : Expr) (args : Array Expr) :
      TM (Option (Expr × Expr × Expr)) := do
    let V := (← read).V
    let w := args[0]!
    let k := args[2]!
    let some kn := natLit? k | return none
    let some (xa, va, ha) ← tr args[3]! | return none
    let some (xm, vm, hm) ← tr args[4]! | return none
    let lem := match c with
      | ``Value.shl => ``Rail.Ev.shlStride
      | ``Value.ushr => ``Rail.Ev.ushrStride
      | ``Value.sshr => ``Rail.Ev.sshrStride
      | _ => ``Rail.Ev.xshrStride
    let pre := mkAppN (mkConst lem) #[V, w, k, args[3]!, args[4]!, xa, va, xm, vm,
      args[1]!, hw, leLit 1 stride, ha, hm]
    -- remaining: ∀ {X Y}, barrel shX vm stride k xa = X → barrel shY vm stride k va = Y → _
    let ty ← instantiateForall (← inferType pre) #[]
    let .forallE _ _ (.forallE _ _ body _) _ := ty | return none
    let .forallE _ dX (.forallE _ dY _ _) _ := body | return none
    let some (_, lX, _) := dX.eq? | return none
    let some (_, lY, _) := dY.eq? | return none
    -- barrel {w} {k} sh vm stride j x
    let shX := lX.getAppArgs[lX.getAppNumArgs - 5]!
    let shY := lY.getAppArgs[lY.getAppNumArgs - 5]!
    let bvT := bv w
    -- each stage occurs twice in the next one: a DAG, not a tree
    let stages (sh x0 : Expr) : Expr := Id.run do
      let mut x := x0
      for j in [0:kn] do
        let bit := mkApp3 (mkConst ``BitVec.getLsbD) k vm (mkNatLit j)
        let shifted := (mkApp2 sh (mkNatLit (stride * 2 ^ j)) x).headBeta
        x := mkApp4 (mkConst ``cond [1]) bvT bit shifted x
      return x
    let X := stages shX xa
    let Y := stages shY va
    let hX := mkApp2 (mkConst ``Eq.refl [1]) bvT X
    let hY := mkApp2 (mkConst ``Eq.refl [1]) bvT Y
    result (mkAppN pre #[X, Y, hX, hY])
  concat (w ps h : Expr) : TM (Option (Expr × Expr × Expr)) := do
    let V := (← read).V
    if ps.isAppOfArity ``List.nil 1 then
      let z := mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit 0)
      return some (z, z, mkAppN (mkConst ``Rail.Ev.concat_nil) #[V, w, h])
    unless ps.isAppOfArity ``List.cons 3 do return none
    let hd := ps.appFn!.appArg!
    let tl := ps.appArg!
    let n := hd.appFn!.appArg!
    let v := hd.appArg!
    let some (xa, va, hv) ← tr v | return none
    let some nn ← (evalNat n).run | return none
    let some wn ← (evalNat w).run | return none
    let hn := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit nn) (mkNatLit wn)
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    let wn' := mkAppN (mkConst ``HSub.hSub [0, 0, 0]) #[mkConst ``Nat, mkConst ``Nat, mkConst ``Nat,
      mkApp2 (mkConst ``instHSub [0]) (mkConst ``Nat) (mkConst ``instSubNat), w, n]
    let tailE := mkApp3 (mkConst ``Value.concatList) wn' tl
      (mkApp5 (mkConst ``concatList_tail) n w v tl h)
    let some (xb, vb, hr) ← concatE tailE | return none
    result (mkAppN (mkConst ``Rail.Ev.concat_cons) #[V, n, w, v, tl, h, xa, va, xb, vb, hn, hv, hr])
  concatE (e : Expr) : TM (Option (Expr × Expr × Expr)) := do
    unless e.isAppOfArity ``Value.concatList 3 do return none
    let args := e.getAppArgs
    concat args[0]! args[1]! args[2]!

end Grounding.Tactic.BvDualRail
