-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Term normalisation and traversal helpers for `bv_dual_rail`.
-/

import Grounding.Tactic.DualRail.Ev

namespace Grounding.Tactic.BvDualRail

open Lean Meta Elab Tactic
open Grounding.Rtl

/-- Eta-reduce `fun x => f x` repeatedly (`Expr.eta` peels one layer). -/
partial def etaFix (e : Expr) : Expr :=
  let e' := e.eta
  if e' == e then e else etaFix e'

/-- Normalize a valuation function: beta- and eta-reduce it so that the many
eta-expanded forms of one valuation (`fun {width} => V width`, …) compare
syntactically equal to `V`. The unfolded `Transition` type stores such forms. -/
def normFun (e : Expr) : MetaM Expr := do
  let e ← liftM (Core.betaReduce e : CoreM Expr)
  return etaFix e

/-- Normalize all `V.eval` applications in a term (bottom-up): a signal becomes
the bare valuation application `V s`, so that it matches the signal atoms.
Other values stay `V.eval`, but with the valuation function normalized. -/
partial def normVals (e : Expr) (_Vs : Array Expr := #[]) : MetaM Expr := do
  -- memoized by pointer: an uncached rebuild would turn the shared DAG into a tree
  let (r, _) ← (go e).run {}
  return r
where
  go (e : Expr) : StateRefT (Std.HashMap USize (Expr × Expr)) MetaM Expr := do
    let p := unsafe ptrAddrUnsafe e
    if let some (k, r) := (← get)[p]? then
      if unsafe ptrEq k e then return r
    let r ← visit e
    -- the key expression is stored too: it stays alive, so its address is not reused
    modify (·.insert p (e, r))
    return r
  visit (e : Expr) : StateRefT (Std.HashMap USize (Expr × Expr)) MetaM Expr := do
    if !e.isApp && !e.isLambda && !e.isForall && !e.isLet && !e.isMData then return e
    if e.isAppOfArity ``Valuation.eval 3 then
      let V0 := e.getAppArgs[0]!
      let w := e.getAppArgs[1]!
      let v ← go e.getAppArgs[2]!
      -- Unfold reducible aliases (e.g. an `abbrev` for a signal) so the shape
      -- check below sees the underlying `Value.signal` / `Value.const`.
      let v ← withTransparency .reducible (whnf v)
      -- Beta/zeta-reduce the application itself: the valuation may occur
      -- eta-expanded (`fun {width} => V`) or as a let-bound auxiliary, and the
      -- result must be syntactically the atoms' form `V s`.
      let app ←
        if v.isAppOfArity ``Value.signal 2 then
          pure (mkApp2 V0 v.getAppArgs[0]! v.getAppArgs[1]!)
        else
          pure (mkApp3 (mkConst ``Valuation.eval) V0 w v)
      let app ← liftM (Core.betaReduce app : CoreM Expr)
      return app
    match e with
    | .app f a => return mkApp (← go f) (← go a)
    | .lam n t b bi => return .lam n t (← go b) bi
    | .forallE n t b bi => return .forallE n t (← go b) bi
    | .letE n t v b nd => return .letE n t (← go v) (← go b) nd
    | .mdata d b => return .mdata d (← go b)
    | _ => return e

structure ValInfo where
  decl : Name
  net : Expr
  V : Expr
  hc : Expr
  deriving Inhabited

/-- Replace auxiliary `_uniq` valuation functions (introduced by unfolding) by
the canonical valuation of the matching atom. `isDefEq` on the whole application
catches the eta-expanded / let-bound forms that `normVals` cannot canonicalize. -/
partial def canonUniq (vals : Array ValInfo) (e : Expr) : MetaM Expr := do
  if e.isApp && e.appFn!.isApp then
    let Ve := e.appFn!.appFn!
    if Ve.isFVar && Ve.fvarId!.name.toString.startsWith "_uniq" then
      let w := e.appFn!.appArg!
      let s := e.appArg!
      for info in vals do
        if ← isDefEq e (mkApp2 info.V w s) then
          return mkApp2 info.V w s
  match e with
  | .app f a => return mkApp (← canonUniq vals f) (← canonUniq vals a)
  | .lam n t b bi => return .lam n t (← canonUniq vals b) bi
  | .forallE n t b bi => return .forallE n t (← canonUniq vals b) bi
  | .letE n t v b nd => return .letE n t (← canonUniq vals v) (← canonUniq vals b) nd
  | .mdata d b => return .mdata d (← canonUniq vals b)
  | _ => return e

/-- Is `l` an application `V w s` of the valuation `V`? (A plain `(← isDefEq …)`
inside `&&` would be hoisted and run before the shape guards.) -/
def isValApp (V l : Expr) : MetaM Bool := do
  unless l.isApp && l.appFn!.isApp do return false
  isDefEq l.appFn!.appFn! V

/-- Index of the valuation of `vals` that `Ve` is (the last match, if several). -/
def valIndex? (vals : Array ValInfo) (Ve : Expr) : MetaM (Option Nat) := do
  let mut idx? : Option Nat := none
  for j in [0:vals.size] do
    if ← isDefEq (vals[j]!).V Ve then idx? := some j
  return idx?

/-- Collect all `V.eval e` subterms in an expression. -/
partial def collectEvals (vals : Array ValInfo) (e : Expr)
    (seen : Std.HashSet USize) (acc : Array (Expr × Expr)) :
    Std.HashSet USize × Array (Expr × Expr) :=
  let p := unsafe ptrAddrUnsafe e
  if seen.contains p then
    (seen, acc)
  else
    let seen := seen.insert p
    let acc :=
      if e.isAppOfArity ``Valuation.eval 3 then
        acc.push (e.getAppArgs[0]!, e.getAppArgs[2]!)
      else acc
    e.getAppArgs.foldl (fun (st, a) x => collectEvals vals x st a) (seen, acc)

/-- Collect `(valIdx, width, V.eval e)` for every `maskOf (V.eval e)` /
`valOf (V.eval e)` subterm of `e` where `V` is one of `vals` and `e` is *not* a
signal (signals already have atoms). These compound terms must become atoms too:
otherwise `bv_decide` sees the occurrence in a fact and the occurrence in the
goal as unrelated opaque applications, and reports a spurious counterexample. -/
partial def collectCompoundEvals (vals : Array ValInfo) (e : Expr)
    (seen : Std.HashSet USize) (acc : Array (Nat × Expr × Expr)) :
    MetaM (Std.HashSet USize × Array (Nat × Expr × Expr)) := do
  let p := unsafe ptrAddrUnsafe e
  if seen.contains p then return (seen, acc)
  let seen := seen.insert p
  let mut acc := acc
  if e.isAppOfArity ``Rail.Ev.maskOf 2 || e.isAppOfArity ``Rail.Ev.valOf 2 then
    let arg := e.getAppArgs[1]!
    if arg.isAppOfArity ``Valuation.eval 3 then
      let Ve := arg.getAppArgs[0]!
      let w := arg.getAppArgs[1]!
      let value := arg.getAppArgs[2]!
      unless value.isAppOfArity ``Value.signal 2 do
        if let some j ← valIndex? vals Ve then
          unless acc.any (fun (_, _, x) => x == arg) do
            acc := acc.push (j, w, arg)
  let mut st := seen
  for x in e.getAppArgs do
    (st, acc) ← collectCompoundEvals vals x st acc
  return (st, acc)

end Grounding.Tactic.BvDualRail
