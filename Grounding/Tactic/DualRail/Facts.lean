-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Rail facts for `bv_dual_rail`: one per source of information in the context
(assignments, inputs, transitions, resets, `bit0` hypotheses, and bridges from
`maskOf (V.eval e)`/`valOf (V.eval e)` to the translation of `e`).
-/

import Grounding.Tactic.DualRail.Translate
import Grounding.Tactic.DualRail.Normalize
import Grounding.Tactic.DualRail.Transition

namespace Grounding.Tactic.BvDualRail

open Lean Meta Elab Tactic
open Grounding.Rtl

def findVals : MetaM (Array ValInfo) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Valuation.isConsistent 2 do continue
    let some decl := ty.appArg!.constName? | continue
    let some ci := (← getEnv).find? decl | continue
    let some net := ci.value? | continue
    unless net.isAppOfArity ``Netlist.mk 4 do continue
    out := out.push { decl, net, V := ← normFun ty.appFn!.appArg!, hc := d.toExpr }
  if out.isEmpty then
    throwError "bv_dual_rail: no `_ : V.isConsistent n` hypothesis in context"
  return out

def mkAtoms (valIdx : Nat) (info : ValInfo) :
    MetaM (Std.HashMap Nat (Expr × Expr × Expr) × Array (Nat × Nat × Expr × Expr)) := do
  let mut sigs : Std.HashMap Nat (Expr × Expr × Expr) := {}
  let mut atoms : Array (Nat × Nat × Expr × Expr) := #[]
  for item in listItems info.net.getAppArgs[0]! do
    let w := item.appFn!.appArg!
    let s := item.appArg!
    let some id := signalId? s | continue
    let vs := mkApp2 (← normFun info.V) w s
    let mk := mkApp2 (mkConst ``Rail.Ev.maskOf) w vs
    let vk := mkApp2 (mkConst ``Rail.Ev.valOf) w vs
    let proof := mkAppN (mkConst ``Rail.Ev.rail_self) #[w, vs]
    sigs := sigs.insert id (mk, vk, proof)
    atoms := atoms.push (valIdx, id, w, vs)
  return (sigs, atoms)

/-- Membership proof for the `i`-th element of the literal list `rs`. -/
partial def mkMemProofAt (i : Nat) (rs : Expr) : MetaM (Option Expr) := do
  if rs.isAppOfArity ``List.cons 3 then
    let lv := rs.getAppFn.constLevels!
    let ty := rs.appFn!.appFn!.appArg!
    let a := rs.appFn!.appArg!
    let l := rs.appArg!
    if i = 0 then return some (mkApp3 (mkConst ``List.Mem.head lv) ty a l)
    else
      let some p ← mkMemProofAt (i - 1) l | return none
      return some (← mkAppM ``List.Mem.tail #[a, p])
  else return none

/-- Assignment equations of one valuation, as rail facts. -/
def assignmentFacts (info : ValInfo) (sigs : Std.HashMap Nat (Expr × Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  let hAssign ← mkAppM ``Valuation.isConsistent.assigns #[info.hc]
  let some unfAssign ← unfoldDefinition?
    (mkApp2 (mkConst ``Valuation.assignsHold) info.V (mkConst info.decl))
    | throwError "bv_dual_rail: cannot unfold assignsHold"
  let unfAssign ← whnfCore unfAssign
  let P ← forallTelescope unfAssign fun xs b => mkLambdaFVars #[xs[0]!] b
  let asgs := listItems info.net.getAppArgs[2]!
  let mut rests : Array Expr := #[hAssign]
  let mut tails : Array Expr := #[info.net.getAppArgs[2]!]
  let mut facts : Array (Expr × Expr) := #[]
  let mut state : Std.HashMap USize (Option (Expr × Expr × Expr)) := {}
  for i in [0:asgs.size] do
    while rests.size ≤ i do
      let k := rests.size - 1
      let t := tails[k]!
      let sp := mkAppN (mkConst ``Grounding.Rtl.Assignment.cons_split)
        #[P, t.appFn!.appArg!, t.appArg!, rests[k]!]
      rests := rests.push (mkProj ``And 1 sp)
      tails := tails.push t.appArg!
    let t := tails[i]!
    let eqi := mkProj ``And 0
      (mkAppN (mkConst ``Grounding.Rtl.Assignment.cons_split)
        #[P, t.appFn!.appArg!, t.appArg!, rests[i]!])
    let asg := asgs[i]!
    let tgt := asg.getAppArgs[1]!
    let src := asg.getAppArgs[3]!
    let ctx : Ctx := { V := info.V, sigs }
    let (rt, st1) ← ((tr tgt).run ctx).run state
    state := st1
    let (rs, st2) ← ((tr src).run ctx).run state
    state := st2
    let some (_, _, ht) := rt | continue
    let some (_, _, hs) := rs | continue
    let ht' ← mkAppM ``Rail.of_eq #[eqi, ht]
    let pf ← mkAppM ``Rail.Ev.rail_unique #[ht', hs]
    facts := facts.push (pf, ← normVals (← inferType pf))
  return facts

/-- Input facts `V s = ofBV a` for one valuation. -/
def inputFacts (info : ValInfo) : MetaM (Array (Expr × Expr)) := do
  let mut facts : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    let l ← normVals l
    let r ← normVals r
    unless ← isValApp info.V l do continue
    unless r.isAppOfArity ``TritVec.ofBV 2 do continue
    let w := l.appFn!.appArg!
    let s := l.appArg!
    let pf := mkAppN (mkConst ``Rail.Ev.input_ofBV) #[info.V, w, s, r.appArg!, d.toExpr]
    facts := facts.push (pf, ← normVals (← inferType pf))
  return facts

/-- Unfold the rail-level definitions in a transition type, leaving
`maskOf`/`valOf` and `Valuation.eval` applications intact. -/
partial def normalizeRail (e : Expr) : MetaM Expr := do
  let (r, _) ← (go e).run {}
  return r
where
  -- memoized by pointer, as in `normVals`
  go (e : Expr) : StateRefT (Std.HashMap USize (Expr × Expr)) MetaM Expr := do
    let p := unsafe ptrAddrUnsafe e
    if let some (k, r) := (← get)[p]? then
      if unsafe ptrEq k e then return r
    let r ← visit e
    modify (·.insert p (e, r))
    return r
  visit (e : Expr) : StateRefT (Std.HashMap USize (Expr × Expr)) MetaM Expr := do
    let e ← withTransparency .reducible (whnf e)
    let some c := e.getAppFn.constName? | return e
    if c == ``RegistersRail || c == ``Netlist.TransitionRail || c == ``Register.railHolds ||
       c == ``Register.nextRails || c == ``Register.aloadMask || c == ``Register.aloadVal ||
       c == ``Register.fallbackMask || c == ``Register.fallbackVal ||
       c == ``Register.activeRail || c == ``Register.clockXRail || c == ``Register.clockEdgeRail then
      let some e' ← unfoldDefinition? e | return e
      go e'
    else
      let args ← e.getAppArgs.mapM go
      return mkAppN e.getAppFn args

/-- The `tr` memo tables, one per valuation (a memo is keyed by the value only, so it
is only valid for the valuation it was built for). -/
abbrev TrMemo := Array (Std.HashMap USize (Option (Expr × Expr × Expr)))

def TrMemo.empty (vals : Array ValInfo) : TrMemo := Array.replicate vals.size {}

/-- The fact `maskOf (V.eval value) = x ∧ valOf (V.eval value) = v` from the
translation of `value`, bridging the opaque atoms to it. `none` if `Ve` is not one
of `vals` or `value` cannot be translated. -/
def evalFact (vals : Array ValInfo) (allSigs : Array (Std.HashMap Nat (Expr × Expr × Expr)))
    (Ve value : Expr) : StateT TrMemo MetaM (Option (Expr × Expr)) := do
  let some idx ← valIndex? vals Ve | return none
  let w := (← inferType value).appArg!
  let (r, st) ← ((tr value).run ({ V := Ve, sigs := allSigs[idx]! } : Ctx)).run (← get)[idx]!
  modify (·.set! idx st)
  let some (_, _, ht) := r | return none
  let evalExpr := mkApp3 (mkConst ``Valuation.eval) Ve w value
  let self := mkAppN (mkConst ``Rail.Ev.rail_self) #[w, evalExpr]
  let pf ← mkAppM ``Rail.Ev.rail_unique #[self, ht]
  return some (pf, ← normVals (← inferType pf) (vals.map (·.V)))

/-- `evalFact` for every `V.eval e` subterm of the type `ty`. -/
def evalFacts (vals : Array ValInfo) (allSigs : Array (Std.HashMap Nat (Expr × Expr × Expr)))
    (ty : Expr) : StateT TrMemo MetaM (Array (Expr × Expr)) := do
  let (_, evals) := collectEvals vals ty {} #[]
  let mut facts := #[]
  for (Ve, value) in evals do
    if let some f ← evalFact vals allSigs Ve value then facts := facts.push f
  return facts

/-- Transition hypotheses, converted to the rail-level form.

For each transition we add the unfolded `TransitionRail` fact and rail facts
for every `V.eval e` subterm inside it. -/
def transitionFacts (vals : Array ValInfo)
    (allSigs : Array (Std.HashMap Nat (Expr × Expr × Expr))) :
    MetaM (Array (Expr × Expr)) := do
  let mut facts : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some c := ty.getAppFn.constName? | continue
    unless c == ``Netlist.Transition || c == ``Netlist.TransitionRail do continue
    let args := ty.getAppArgs
    if args.size < 3 then continue
    let n := args[0]!
    let V := args[1]!
    let V' := args[2]!
    let some iV ← valIndex? vals V | continue
    let some iV' ← valIndex? vals V' | continue
    -- Build everything from the atoms' canonical valuations: the hypothesis's
    -- `V`/`V'` may be eta-expanded, and elaborating on those forms introduces
    -- let-bound auxiliaries that `normalizeRail` cannot see through.
    let Vc := (vals[iV]!).V
    let Vc' := (vals[iV']!).V
    let hRail ← if c == ``Netlist.Transition then
      let iff := mkAppN (mkConst ``Netlist.Transition.iff_rail) #[n, Vc, Vc']
      mkAppM ``Iff.mp #[iff, d.toExpr]
    else
      pure d.toExpr
    let tyRail := mkAppN (mkConst ``Netlist.TransitionRail) #[n, Vc, Vc']
    let ty ← canonUniq vals (← normVals (← normalizeRail tyRail) (vals.map (·.V)))
    let (fs, _) ← (evalFacts vals allSigs ty).run (TrMemo.empty vals)
    facts := facts ++ fs
    facts := facts.push (hRail, ty)
  return facts

/-- Register reset facts of one valuation (the register half of `isConsistent`),
as rail equations, plus rail facts for the `V.eval e` subterms they mention. -/
def resetFacts (vals : Array ValInfo)
    (allSigs : Array (Std.HashMap Nat (Expr × Expr × Expr))) (info : ValInfo) :
    MetaM (Array (Expr × Expr)) := do
  let hResets ← mkAppM ``Valuation.isConsistent.resets #[info.hc]
  let regs := info.net.getAppArgs[3]!
  let Vs := vals.map (·.V)
  let mut facts : Array (Expr × Expr) := #[]
  let mut memo := TrMemo.empty vals
  let mut i := 0
  for r in listItems regs do
    let some hmem ← mkMemProofAt i regs | continue
    i := i + 1
    let w := r.appFn!.appArg!
    let reg := r.appArg!
    let hreg := mkApp2 hResets r hmem
    let pf := mkAppN (mkConst ``Register.register_reset_rails) #[w, info.V, reg, hreg]
    let ty ← canonUniq vals (← normVals (← normalizeRail (← inferType pf)) Vs)
    let pf ← mkExpectedTypeHint pf ty
    let (fs, memo') ← (evalFacts vals allSigs ty).run memo
    memo := memo'
    facts := facts ++ fs
    facts := facts.push (pf, ty)
  return facts

/-- Rail facts for hypotheses `c.bit0 ≠ Trit.x`, `c.bit0 = Trit.zero`,
`c.bit0 ≠ Trit.zero` where `c` is a `V.eval e` of a known valuation. -/
def bit0Facts (vals : Array ValInfo) : MetaM (Array (Expr × Expr)) := do
  let Vs := vals.map (·.V)
  let mut facts : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let (isEq, a, b) ← do
      if ty.isAppOfArity ``Ne 3 then pure (false, ty.getAppArgs[1]!, ty.getAppArgs[2]!)
      else if ty.isAppOfArity ``Not 1 then
        match ty.appArg!.eq? with
        | some (_, a, b) => pure (false, a, b)
        | none => continue
      else match ty.eq? with
        | some (_, a, b) => pure (true, a, b)
        | none => continue
    unless a.isAppOfArity ``TritVec.bit0 1 do continue
    let c ← normVals a.appArg! Vs
    unless c.isAppOfArity ``Valuation.eval 3 || (← vals.anyM fun j => isValApp j.V c) do continue
    let some cn := b.constName? | continue
    let lem? : Option Name :=
      if isEq && cn == ``Trit.zero then some ``Rail.Ev.bit0_eq_zero_rails
      else if !isEq && cn == ``Trit.x then some ``Rail.Ev.bit0_ne_x_mask
      else if !isEq && cn == ``Trit.zero then some ``Rail.Ev.bit0_ne_zero_rails
      else none
    let some lem := lem? | continue
    let pf ← mkAppM lem #[d.toExpr]
    let pty ← normVals (← inferType pf) Vs
    facts := facts.push (← mkExpectedTypeHint pf pty, pty)
  return facts

/-- Rail facts of every compound `V.eval e` in `e` (bridging the opaque
`maskOf (V.eval e)` / `valOf (V.eval e)` to the translation of `e`). -/
def bridgeFacts (vals : Array ValInfo) (allSigs : Array (Std.HashMap Nat (Expr × Expr × Expr)))
    (es : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut seen := {}
  let mut evals := #[]
  for e in es do
    (seen, evals) := collectEvals vals e seen evals
  let mut facts := #[]
  let mut memo := TrMemo.empty vals
  let mut done : Std.HashSet Expr := {}
  for (Ve, value) in evals do
    let evalExpr := mkApp3 (mkConst ``Valuation.eval) Ve (← inferType value).appArg! value
    if done.contains evalExpr then continue
    done := done.insert evalExpr
    let (f?, memo') ← (evalFact vals allSigs Ve value).run memo
    memo := memo'
    if let some f := f? then facts := facts.push f
  return facts

end Grounding.Tactic.BvDualRail
