-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Generic `bv_dual_rail`: encode every `V.isConsistent n` valuation found in the
context and every `Transition`/`TransitionRail` hypothesis between them as
mask/value `BitVec` equations, so that `bv_decide` can finish the goal.
-/
import Grounding.Tactic.DualRail.Translate
import Grounding.Tactic.DualRail.Normalize
import Grounding.Tactic.DualRail.Facts
import Grounding.Tactic.DualRail.Goal

namespace Grounding.Tactic.BvDualRail

open Lean Meta Elab Tactic
open Grounding.Rtl

/-- Does `e` contain one of the atom keys as a subterm? -/
def mentionsKey (keys : Std.HashSet Expr) (e : Expr) : Bool :=
  (e.find? keys.contains).isSome  -- `find?` caches visited pointers

syntax (name := bvDualRail) "bv_dual_rail" (ppSpace colGt ident)? : tactic

@[tactic bvDualRail] def evalBvDualRail : Tactic := fun _stx => withMainContext do
  -- a goal `c.bit0 ≠ Trit.x` is the mask equation `maskOf c = 0#1`
  let t0 ← instantiateMVars (← getMainGoal >>= (·.getType))
  if t0.isAppOfArity ``Ne 3 && t0.getAppArgs[1]!.isAppOfArity ``TritVec.bit0 1 then
    evalTactic (← `(tactic| refine Grounding.Rtl.Rail.Ev.bit0_ne_x_of_mask ?_))
  withMainContext do
  let vals ← findVals
  let mut atoms : Array (Nat × Nat × Expr × Expr) := #[]
  let mut facts : Array (Expr × Expr) := #[]
  let mut allSigs : Array (Std.HashMap Nat (Expr × Expr × Expr)) := #[]
  for i in [0:vals.size] do
    let info := vals[i]!
    let (sigs, ats) ← mkAtoms i info
    allSigs := allSigs.push sigs
    atoms := atoms ++ ats
    facts := facts ++ (← assignmentFacts info sigs)
    facts := facts ++ (← inputFacts info)
  for info in vals do
    facts := facts ++ (← resetFacts vals allSigs info)
  facts := facts ++ (← transitionFacts vals allSigs)
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  let target := target.replace fun e => if e.isMData then some e.consumeMData else none
  -- canonicalize `V.eval (.signal …)` in the goal itself, so the goal's atoms
  -- match the abstraction keys (as for the facts)
  let target ← normVals target (vals.map (·.V))
  let target'₀ ← transformGoal vals target
  -- compound `V.eval e` terms need atoms too (see `collectCompoundEvals`)
  let bitFacts ← bit0Facts vals
  let mut compound : Array (Nat × Expr × Expr) := #[]
  let mut cseen : Std.HashSet USize := {}
  for (_, ty) in facts ++ bitFacts do
    (cseen, compound) ← collectCompoundEvals vals ty cseen compound
  (cseen, compound) ← collectCompoundEvals vals target cseen compound
  (cseen, compound) ← collectCompoundEvals vals target'₀ cseen compound
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    (cseen, compound) ← collectCompoundEvals vals (← instantiateMVars d.type) cseen compound
  let mut compoundId := 1000000
  for (valIdx, w, vs) in compound do
    atoms := atoms.push (valIdx, compoundId, w, vs)
    compoundId := compoundId + 1
  -- hypotheses that mention the atoms, e.g. `maskOf (V s) = 1#1`
  let keys : Std.HashSet Expr := Id.run do
    let mut s := {}
    for (_, _, w, vs) in atoms do
      s := s.insert (mkApp2 (mkConst ``Rail.Ev.maskOf) w vs)
      s := s.insert (mkApp2 (mkConst ``Rail.Ev.valOf) w vs)
    return s
  let mut userHyps : Array (Expr × Expr) := #[]
  let mut eqSides : Array Expr := #[]
  let mut keyHypTys : Array Expr := bitFacts.map (·.2)
  for bf in bitFacts do userHyps := userHyps.push bf
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← normVals (← instantiateMVars d.type) (vals.map (·.V))
    if ty.hasMVar then continue
    -- `l = r` on constants (inputs `V s = ofBV a` are already facts)
    if let some (stmt, lits) ← eqAsRails vals ty then
      let some (_, l, r) := ty.eq? | unreachable!
      let isInput := (← vals.anyM fun j => isValApp j.V l) && r.isAppOfArity ``TritVec.ofBV 2
      unless isInput do
        let pf ← mkAppM ``Rail.Ev.eq_rails #[← mkExpectedTypeHint d.toExpr ty]
        userHyps := userHyps.push (pf, stmt)
        for lp in lits do userHyps := userHyps.push (lp, ← inferType lp)
        eqSides := eqSides.push ty
      continue
    if mentionsKey keys ty then
      userHyps := userHyps.push (d.toExpr, ty)
      keyHypTys := keyHypTys.push ty
  -- the goal (possibly `h₁ → … → l = r`)
  let mut goalLits : Array Expr := #[]
  let (goalPrems, goalConcl) ← splitArrows target
  let goalR ← goalRails vals goalConcl
  if let some (_, lits, _) := goalR then
    goalLits := lits
    eqSides := eqSides.push goalConcl
  for (f, ty) in ← bridgeFacts vals allSigs (eqSides ++ goalPrems ++ keyHypTys ++ #[target]) do
    userHyps := userHyps.push (f, ty)
  for lp in goalLits do userHyps := userHyps.push (lp, ← inferType lp)
  let target' ← match goalR with
    | some (stmt, _, _) => rebuildArrows goalPrems stmt
    | none => pure target'₀
  let n := atoms.size
  let nf := facts.size
  let nu := userHyps.size
  let decls : Array (Name × BinderInfo × (Array Expr → TacticM Expr)) :=
    atoms.foldl (fun acc (valIdx, id, w, _) =>
      (acc.push (Name.mkSimple s!"m{valIdx}_{id}", .default, fun _ => pure (mkApp (mkConst ``BitVec) w))).push
        (Name.mkSimple s!"v{valIdx}_{id}", .default, fun _ => pure (mkApp (mkConst ``BitVec) w))) #[]
  let newGoal ← withLocalDecls decls fun xs => do
    let atomIdx : Std.HashMap Expr Expr := Id.run do
      let mut mp := {}
      for h : j in [0:n] do
        let (valIdx, _, w, vs) := atoms[j]
        mp := mp.insert (mkApp2 (mkConst ``Rail.Ev.maskOf) w vs) xs[2*j]!
        mp := mp.insert (mkApp2 (mkConst ``Rail.Ev.valOf) w vs) xs[2*j+1]!
      return mp
    let abst (e : Expr) : Expr := e.replace fun t => atomIdx[t]?
    let mut hyps : Array Expr := #[]
    for h : j in [0:n] do
      let (_, _, w, _) := atoms[j]
      hyps := hyps.push (← mkEq
        (mkAppN (mkConst ``HAnd.hAnd [0,0,0]) #[mkApp (mkConst ``BitVec) w, mkApp (mkConst ``BitVec) w,
          mkApp (mkConst ``BitVec) w,
          mkApp2 (mkConst ``instHAndOfAndOp [0]) (mkApp (mkConst ``BitVec) w)
            (mkApp (mkConst ``BitVec.instAndOp) w),
          xs[2*j+1]!, xs[2*j]!])
        (mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit 0)))
    for (_, ty) in facts do hyps := hyps.push (abst ty)
    for (_, ty) in userHyps do hyps := hyps.push (abst ty)
    let body ← hyps.foldrM (fun h acc => mkArrow h acc) (abst target')
    mkForallFVars xs body
  let m ← mkFreshExprSyntheticOpaqueMVar newGoal (← g.getTag)
  let mut pf := m
  for (_, _, w, vs) in atoms do
    pf := mkApp2 pf (mkApp2 (mkConst ``Rail.Ev.maskOf) w vs) (mkApp2 (mkConst ``Rail.Ev.valOf) w vs)
  for (_, _, w, vs) in atoms do
    pf := mkApp pf (mkProj ``And 1 (mkApp2 (mkConst ``Rail.Ev.rail_self) w vs))
  for (f, _) in facts do pf := mkApp pf f
  for (f, _) in userHyps do pf := mkApp pf f
  if let some (_, _, close) := goalR then
    g.assign (ShareCommon.shareCommon' (← closeArrows target (fun h => pure (close h)) pf))
  else
    g.assign (ShareCommon.shareCommon' (← proveGoal vals target pf))
  let (_, g') ← m.mvarId!.introNP (2 * n + n + nf + nu)
  replaceMainGoal [g']
  evalTactic (← `(tactic| try simp only [Grounding.Rtl.TritVec.ofBV_inj,
    Grounding.Rtl.Rail.Ev.maskOf_ofBV, Grounding.Rtl.Rail.Ev.valOf_ofBV]))

end Grounding.Tactic.BvDualRail
