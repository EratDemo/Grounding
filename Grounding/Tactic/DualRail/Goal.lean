-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Goal handling for `bv_dual_rail`: rewriting a `TritVec` equation (or an
implication or conjunction of them) to mask/value equations, and the matching
proof terms.
-/

import Grounding.Tactic.DualRail.Normalize
import Grounding.Tactic.DualRail.Ev

namespace Grounding.Tactic.BvDualRail

open Lean Meta Elab Tactic
open Grounding.Rtl

def transformGoal (vals : Array ValInfo) (target : Expr) : MetaM Expr := do
  if let .forallE n t b bi := target then
    if !b.hasLooseBVars then
      return .forallE n t (← transformGoal vals b) bi
  let some (_, l, r) := target.eq? | return target
  let l ← normVals l (vals.map (·.V))
  let r ← normVals r (vals.map (·.V))
  for info in vals do
    if ← isValApp info.V l then
      let w := l.appFn!.appArg!
      let mkM (e : Expr) := mkApp2 (mkConst ``Rail.Ev.maskOf) w e
      let mkV (e : Expr) := mkApp2 (mkConst ``Rail.Ev.valOf) w e
      if r.isAppOfArity ``TritVec.ofBV 2 then
        return ← mkAppM ``And #[
          ← mkEq (mkM l) (mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit 0)),
          ← mkEq (mkV l) r.appArg!]
      if r.isApp && r.appFn!.isApp then
        let mut matched := false
        for j in vals do
          if ← isDefEq r.appFn!.appFn! j.V then matched := true
        if matched then
          return ← mkAppM ``And #[← mkEq (mkM l) (mkM r), ← mkEq (mkV l) (mkV r)]
      -- `V s = V.eval e` (a compound right-hand side, possibly under the other
      -- valuation)
      if r.isAppOfArity ``Valuation.eval 3 then
        let mut matched := false
        for j in vals do
          if ← isDefEq r.getAppArgs[0]! j.V then matched := true
        if matched then
          return ← mkAppM ``And #[← mkEq (mkM l) (mkM r), ← mkEq (mkV l) (mkV r)]
  return target

def proveGoal (vals : Array ValInfo) (target pf : Expr) : MetaM Expr := do
  if let .forallE n t b _ := target then
    if !b.hasLooseBVars then
      return ← withLocalDeclD n t fun h => do
        mkLambdaFVars #[h] (← proveGoal vals b (mkApp pf h))
  let some (_, l, r) := target.eq? | return pf
  let l ← normVals l (vals.map (·.V))
  let r ← normVals r (vals.map (·.V))
  for info in vals do
    if ← isValApp info.V l then
      let w := l.appFn!.appArg!
      let s := l.appArg!
      if r.isAppOfArity ``TritVec.ofBV 2 then
        return mkAppN (mkConst ``Rail.Ev.goal_eq_ofBV) #[info.V, w, s, r.appArg!, pf]
      if r.isApp && r.appFn!.isApp then
        let mut matched := false
        for j in vals do
          if ← isDefEq r.appFn!.appFn! j.V then matched := true
        if matched then
          let mkM := mkApp2 (mkConst ``Rail.Ev.maskOf) w l
          let mkV := mkApp2 (mkConst ``Rail.Ev.valOf) w l
          return mkAppN (mkConst ``Rail.Ev.goal_eq_any) #[w, l, r, mkM, mkV, pf]
      if r.isAppOfArity ``Valuation.eval 3 then
        let mut matched := false
        for j in vals do
          if ← isDefEq r.getAppArgs[0]! j.V then matched := true
        if matched then
          let mkM := mkApp2 (mkConst ``Rail.Ev.maskOf) w l
          let mkV := mkApp2 (mkConst ``Rail.Ev.valOf) w l
          return mkAppN (mkConst ``Rail.Ev.goal_eq_any) #[w, l, r, mkM, mkV, pf]
  return pf

/-- A side of a `TritVec` equation the encoding can name: a valuation
application `V s`, a `V.eval e` of one of `vals`, or a literal `TritVec.ofBV a` /
`TritVec.undef w`. For a literal, also the proof of its rails. -/
def nameableSide (vals : Array ValInfo) (w c : Expr) : MetaM (Option (Option Expr)) := do
  if c.isAppOfArity ``TritVec.ofBV 2 then
    let a := c.appArg!
    return some (some (← mkAppM ``And.intro #[mkApp2 (mkConst ``Rail.Ev.maskOf_ofBV) w a,
      mkApp2 (mkConst ``Rail.Ev.valOf_ofBV) w a]))
  if c.isAppOfArity ``TritVec.undef 1 then
    return some (some (← mkAppM ``And.intro #[mkApp (mkConst ``Rail.Ev.maskOf_undef) w,
      mkApp (mkConst ``Rail.Ev.valOf_undef) w]))
  for j in vals do
    if ← isValApp j.V c then return some none
    if c.isAppOfArity ``Valuation.eval 3 then
      if ← isDefEq c.getAppArgs[0]! j.V then return some none
  return none

/-- A `TritVec` equation `l = r` (sides nameable, not both literal) as rails:
`maskOf l = maskOf r ∧ valOf l = valOf r`, plus the rail facts of literal sides. -/
def eqAsRails (vals : Array ValInfo) (ty : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let some (T, l, r) := ty.eq? | return none
  unless T.isAppOfArity ``TritVec 1 do return none
  let w := T.appArg!
  let some pl ← nameableSide vals w l | return none
  let some pr ← nameableSide vals w r | return none
  if pl.isSome && pr.isSome then return none
  let stmt ← mkAppM ``And #[← mkEq (mkApp2 (mkConst ``Rail.Ev.maskOf) w l)
      (mkApp2 (mkConst ``Rail.Ev.maskOf) w r),
    ← mkEq (mkApp2 (mkConst ``Rail.Ev.valOf) w l) (mkApp2 (mkConst ``Rail.Ev.valOf) w r)]
  return some (stmt, #[pl, pr].filterMap id)

/-- A goal conclusion that is a conjunction tree of `TritVec` equations, as rails:
`(stmt, literal rail facts, closer : proof of stmt ↦ proof of the conclusion)`. -/
partial def goalRails (vals : Array ValInfo) (c : Expr) :
    MetaM (Option (Expr × Array Expr × (Expr → Expr))) := do
  if c.isAppOfArity ``And 2 then
    let some (s1, l1, k1) ← goalRails vals c.appFn!.appArg! | return none
    let some (s2, l2, k2) ← goalRails vals c.appArg! | return none
    let stmt := mkApp2 (mkConst ``And) s1 s2
    return some (stmt, l1 ++ l2, fun h =>
      mkApp4 (mkConst ``And.intro) c.appFn!.appArg! c.appArg!
        (k1 (mkApp3 (mkConst ``And.left) s1 s2 h)) (k2 (mkApp3 (mkConst ``And.right) s1 s2 h)))
  -- `p → q` (non-dependent): encode `q`, keep the premise
  if let .forallE n p q bi := c then
    if !q.hasLooseBVars then
      let some (sq, lq, kq) ← goalRails vals q | return none
      return some (.forallE n p sq bi, lq, fun h => .lam n p (kq (mkApp h (.bvar 0))) bi)
  let some (stmt, lits) ← eqAsRails vals c | return none
  let some (T, l, r) := c.eq? | return none
  let w := T.appArg!
  let mk := mkApp2 (mkConst ``Rail.Ev.maskOf) w l
  let vk := mkApp2 (mkConst ``Rail.Ev.valOf) w l
  return some (stmt, lits, fun h => mkAppN (mkConst ``Rail.Ev.goal_eq_any) #[w, l, r, mk, vk, h])

/-- `h₁ → … → c` (non-dependent arrows) as `([h₁, …], c)`. -/
partial def splitArrows (e : Expr) : MetaM (Array Expr × Expr) := do
  match e with
  | .forallE _ t b _ =>
    if b.hasLooseBVars then return (#[], e)
    let (ps, c) ← splitArrows b
    return (#[t] ++ ps, c)
  | _ => return (#[], e)

def rebuildArrows (ps : Array Expr) (c : Expr) : MetaM Expr :=
  ps.foldrM (fun p acc => mkArrow p acc) c

/-- From `pf : h₁ → … → stmt` build a proof of `h₁ → … → c` with `close : stmt → c`. -/
partial def closeArrows (target : Expr) (close : Expr → MetaM Expr) (pf : Expr) : MetaM Expr := do
  match target with
  | .forallE n t b _ =>
    if b.hasLooseBVars then close pf else
    withLocalDeclD n t fun h => do mkLambdaFVars #[h] (← closeArrows b close (mkApp pf h))
  | _ => close pf

end Grounding.Tactic.BvDualRail
