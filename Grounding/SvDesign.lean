-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
`sv_design`: embed an elaborated SystemVerilog design as Lean terms.

```
sv_design foo "rtl/top.sv" "--top" "top"
```

runs the frontend while the file is elaborated and adds one definition,
`foo : Netlist`: the whole netlist as a single closed term. Then

```
sv_expr% foo "a + b"
```

elaborates a SystemVerilog expression in the top scope of `foo` to a `Value w`.
The design name is optional: it defaults to the `foo` of a hypothesis
`_ : V.isConsistent foo` in scope, else the unique embedded design. In another
file the native handle is recovered by re-running the frontend with the recorded
arguments, and the result must match the recorded fingerprint.

`sv_eval% V "expr"` (or `sv_eval% V foo "expr"`) is shorthand for
`V.eval (sv_expr% "expr")`.

Nothing native is trusted in proofs: the frontend's output is frozen into
ordinary definitions, and all facts are checked by the kernel.
-/

import Lean.Elab.Command
import Lean.Elab.Term
import Grounding.Sv
import Grounding.Rtl.Valuation
import Grounding.SvDesign.Cache

namespace Grounding.SvDesign

open Lean Meta Elab Command
open Grounding.Rtl
open Lean.Elab.Term (TermElab)

/-! ### Values to expressions -/

structure EmbedState where
  /-- Signal id ↦ its term (a constant, or an inline `Signal.mk` literal). -/
  sigExpr : Std.HashMap Nat Expr := {}
  /-- Already-embedded shared nodes (by structure). -/
  nodes : Std.HashMap (Σ w, Value w) Expr := {}

abbrev EmbedM := StateRefT EmbedState MetaM

def tritExpr : Trit → Expr
  | .zero => mkConst ``Trit.zero
  | .one => mkConst ``Trit.one
  | .x => mkConst ``Trit.x

def valueTy (w : Nat) : Expr := mkApp (mkConst ``Value) (mkNatLit w)

/-- `⟨⟨#[t₀, …], rfl⟩⟩ : TritVec w` -/
def constExpr (c : TritVec w) : MetaM Expr := do
  let arr ← mkArrayLit (mkConst ``Trit) (c.bits.toList.map tritExpr)
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Array.size [0]) (mkConst ``Trit) arr) (mkNatLit w)
  let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit w)
  let pf ← mkExpectedTypeHint pf ty
  let vec := mkApp4 (mkConst ``Vector.mk [0]) (mkConst ``Trit) (mkNatLit w) arr pf
  return mkApp2 (mkConst ``TritVec.mk) (mkNatLit w) vec

/-- A proof of `a ≤ b` for literals, checked by `Nat.ble` in the kernel. -/
def leProof (a b : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit a) (mkNatLit b)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- `rfl : lhs = rhs` where both sides reduce to the literal `n`. -/
def natRfl (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit n)

def sigmaValue : Expr :=
  mkLambda `w .default (mkConst ``Nat) (mkApp (mkConst ``Value) (.bvar 0))

/-- One node, given the embedding `f` of its children. -/
def nodeExpr (f : {w : Nat} → Value w → EmbedM Expr) : {w : Nat} → Value w → EmbedM Expr
  | w, .signal s => do
    match (← get).sigExpr[s.id]? with
    | some e => return mkApp2 (mkConst ``Value.signal) (mkNatLit w) e
    | none => throwError "sv_design: unknown signal #{s.id}"
  | w, .const c => return mkApp2 (mkConst ``Value.const) (mkNatLit w) (← constExpr c)
  | w, .not a => return mkApp2 (mkConst ``Value.not) (mkNatLit w) (← f a)
  | w, .and a b => return mkApp3 (mkConst ``Value.and) (mkNatLit w) (← f a) (← f b)
  | w, .or a b => return mkApp3 (mkConst ``Value.or) (mkNatLit w) (← f a) (← f b)
  | w, .xor a b => return mkApp3 (mkConst ``Value.xor) (mkNatLit w) (← f a) (← f b)
  | w, .mux s a b => return mkApp4 (mkConst ``Value.mux) (mkNatLit w) (← f s) (← f a) (← f b)
  | _, @Value.adc k a b c => return mkApp4 (mkConst ``Value.adc) (mkNatLit k) (← f a) (← f b) (← f c)
  | _, @Value.eq k a b => return mkApp3 (mkConst ``Value.eq) (mkNatLit k) (← f a) (← f b)
  | _, @Value.ult k a b => return mkApp3 (mkConst ``Value.ult) (mkNatLit k) (← f a) (← f b)
  | _, @Value.slt k a b => return mkApp3 (mkConst ``Value.slt) (mkNatLit k) (← f a) (← f b)
  | _, @Value.eqx k a b => return mkApp3 (mkConst ``Value.eqx) (mkNatLit k) (← f a) (← f b)
  | w, .shl stride k a m =>
    return mkApp5 (mkConst ``Value.shl) (mkNatLit w) (mkNatLit stride) (mkNatLit k) (← f a) (← f m)
  | w, .ushr stride k a m =>
    return mkApp5 (mkConst ``Value.ushr) (mkNatLit w) (mkNatLit stride) (mkNatLit k) (← f a) (← f m)
  | w, .sshr stride k a m =>
    return mkApp5 (mkConst ``Value.sshr) (mkNatLit w) (mkNatLit stride) (mkNatLit k) (← f a) (← f m)
  | w, .xshr stride k a m =>
    return mkApp5 (mkConst ``Value.xshr) (mkNatLit w) (mkNatLit stride) (mkNatLit k) (← f a) (← f m)
  | w, .replicate _ a =>
    return mkApp2 (mkConst ``Value.replicate) (mkNatLit w) (← f a)
  | w, .mul a b => return mkApp3 (mkConst ``Value.mul) (mkNatLit w) (← f a) (← f b)
  | w, .udiv a b => return mkApp3 (mkConst ``Value.udiv) (mkNatLit w) (← f a) (← f b)
  | w, .umod a b => return mkApp3 (mkConst ``Value.umod) (mkNatLit w) (← f a) (← f b)
  | w, .sdivTrunc a b => return mkApp3 (mkConst ``Value.sdivTrunc) (mkNatLit w) (← f a) (← f b)
  | w, .sdivFloor a b => return mkApp3 (mkConst ``Value.sdivFloor) (mkNatLit w) (← f a) (← f b)
  | w, .smodTrunc a b => return mkApp3 (mkConst ``Value.smodTrunc) (mkNatLit w) (← f a) (← f b)
  | w, .smodFloor a b => return mkApp3 (mkConst ``Value.smodFloor) (mkNatLit w) (← f a) (← f b)
  | w, .partSelect sw src o _ =>
    return mkApp5 (mkConst ``Value.partSelect) (mkNatLit w) (mkNatLit sw) (← f src) (mkNatLit o)
      (leProof (o + w) sw)
  | w, .concatNode _ ws parts _ => do
    let ps ← (List.finRange ws.size).mapM fun i => do
      return mkApp4 (mkConst ``Sigma.mk [0, 0]) (mkConst ``Nat) sigmaValue
        (mkNatLit ws[i]) (← f (parts i))
    let sigTy := mkApp2 (mkConst ``Sigma [0, 0]) (mkConst ``Nat) sigmaValue
    let lit ← mkListLit sigTy ps
    -- the width proof is `rfl` at the type `concatList` expects, so lemmas match syntactically
    let fst := mkLambda `x .default sigTy
      (mkApp3 (mkConst ``Sigma.fst [0, 0]) (mkConst ``Nat) sigmaValue (.bvar 0))
    let ws := mkApp2 (mkConst ``List.toArray [0]) (mkConst ``Nat)
      (mkApp4 (mkConst ``List.map [0, 0]) sigTy (mkConst ``Nat) fst lit)
    let sum := mkApp7 (mkConst ``Array.foldl [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
      (mkConst ``Nat.add) (mkNatLit 0) ws (mkNatLit 0)
      (mkApp2 (mkConst ``Array.size [0]) (mkConst ``Nat) ws)
    let pf ← mkExpectedTypeHint (natRfl w)
      (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) sum (mkNatLit w))
    return mkApp3 (mkConst ``Value.concatList) (mkNatLit w) lit pf

/-- Embed a value; structurally equal sub-terms are embedded once and shared. -/
partial def valueExpr {w : Nat} (v : Value w) : EmbedM Expr := do
  if let some e := (← get).nodes[(⟨w, v⟩ : Σ w, Value w)]? then return e
  let e ← nodeExpr valueExpr v
  modify fun s => { s with nodes := s.nodes.insert ⟨w, v⟩ e }
  return e

/-- An assignability proof for an embedded target. -/
partial def assignableProof {w : Nat} (v : Value w) (e : Expr) : MetaM Expr := do
  match v, e.getAppFn.constName?, e.getAppArgs with
  | .signal _, _, args => return mkApp2 (mkConst ``Value.CanBeAssignedTo.signal) (mkNatLit w) args[1]!
  | .partSelect sw src o _, _, args =>
    return mkApp6 (mkConst ``Value.CanBeAssignedTo.partSelect) (mkNatLit w) (mkNatLit sw) args[2]!
      (mkNatLit o) args[4]! (← assignableProof src args[2]!)
  | .concatNode _ ws parts _, _, args =>
    -- args: w, list literal, rfl
    let mut pf := Lean.mkConst ``True.intro
    let items := (← getListLitItems args[1]!)
    for i in (List.range ws.size).reverse do
      let some j := (if h : i < ws.size then some (⟨i, h⟩ : Fin ws.size) else none) | unreachable!
      let item := items[i]!
      let partPf ← assignableProof (parts j) item.appArg!
      pf ← mkAppM ``And.intro #[partPf, pf]
    return mkApp4 (mkConst ``Value.concatList_assignable) (mkNatLit w) args[1]! args[2]! pf
  | _, _, _ => throwError "sv_design: target is not assignable"
where
  getListLitItems (e : Expr) : MetaM (Array Expr) := do
    let mut e := e
    let mut out := #[]
    while e.isAppOfArity ``List.cons 3 do
      out := out.push e.appFn!.appArg!
      e := e.appArg!
    return out

/-! ### Declarations -/

def addDef (name : Name) (type value : Expr) (reducible := false) : MetaM Unit := do
  addDecl (.defnDecl (mkDefinitionValEx name [] type value (.regular (getMaxHeight (← getEnv) value + 1))
    .safe [name]))
  compileDecls #[name]
  if reducible then setReducibleAttribute name

/-- The inline term of a signal. -/
def signalExpr (w : Nat) (s : Signal w) : MetaM Expr := do
  let nameE ← match s.name with
    | some str => pure (mkApp2 (mkConst ``Option.some [0]) (mkConst ``String) (mkStrLit str))
    | none => pure (mkApp (mkConst ``Option.none [0]) (mkConst ``String))
  return mkApp3 (mkConst ``Signal.mk) (mkNatLit w) (mkNatLit s.id) nameE

/-- `Σ w, F w` for a type family `F : Nat → Type`. -/
def sigmaTy (F : Name) : Expr :=
  mkApp2 (mkConst ``Sigma [0, 0]) (mkConst ``Nat)
    (mkLambda `w .default (mkConst ``Nat) (mkApp (mkConst F) (.bvar 0)))

def sigmaMk (F : Name) (w : Nat) (x : Expr) : Expr :=
  mkApp4 (mkConst ``Sigma.mk [0, 0]) (mkConst ``Nat)
    (mkLambda `w .default (mkConst ``Nat) (mkApp (mkConst F) (.bvar 0))) (mkNatLit w) x

/-- The whole netlist as one closed term, with signals as inline `Signal.mk` literals
and shared sub-expressions as one `Expr`. -/
def netlistExpr (n : Netlist) : MetaM Expr := do
  let mut sigExpr : Std.HashMap Nat Expr := {}
  let mut sigList := #[]
  for ⟨w, s⟩ in n.signals do
    let e ← signalExpr w s
    sigExpr := sigExpr.insert s.id e
    sigList := sigList.push (sigmaMk ``Signal w e)
  let ((ports, asgs, regs), _) ← (show EmbedM _ from do
    let ports ← n.ports.mapM fun ⟨w, p⟩ => do
      let pe ← match p with
        | .In name v _ => do
          let ve ← valueExpr v
          pure (mkApp4 (mkConst ``Port.In) (mkNatLit w) (mkStrLit name) ve (← assignableProof v ve))
        | .Out name v => do
          pure (mkApp3 (mkConst ``Port.Out) (mkNatLit w) (mkStrLit name) (← valueExpr v))
      pure (sigmaMk ``Port w pe)
    let asgs ← n.assignments.mapM fun a => do
      let te ← valueExpr a.target
      let se ← valueExpr a.source
      pure (mkApp4 (mkConst ``Assignment.mk) (mkNatLit a.width) te (← assignableProof a.target te) se)
    let regs ← n.registers.mapM fun ⟨w, r⟩ => do
      let W := mkNatLit w
      let qe ← valueExpr r.q
      let als ← r.aloads.mapM fun l => do
        pure (mkApp4 (mkConst ``AsyncLoad.mk) W (← valueExpr l.trigger) (toExpr l.polarity)
          (← valueExpr l.value))
      let re := mkApp8 (mkConst ``Register.mk) W qe (← assignableProof r.q qe) (← valueExpr r.d)
        (← valueExpr r.clk) (toExpr r.clkPolarity) (← mkListLit (mkApp (mkConst ``AsyncLoad) W) als)
        (← constExpr r.init)
      pure (sigmaMk ``Register w re)
    return (ports, asgs, regs)).run { sigExpr }
  return mkApp4 (mkConst ``Netlist.mk) (← mkListLit (sigmaTy ``Signal) sigList.toList)
    (← mkListLit (sigmaTy ``Port) ports) (← mkListLit (mkConst ``Assignment) asgs)
    (← mkListLit (sigmaTy ``Register) regs)

/-- Embed `n` as the single definition `decl`. -/
def embed (decl : Name) (n : Netlist) : MetaM Unit := do
  addDef decl (mkConst ``Netlist) (← netlistExpr n)

/-! ### The handle -/

def elaborateArgs (args : Array String) : IO Elaborated := do
  match ← readSvArgs args with
  | .ok e => return e
  | .error msg => throw (IO.userError s!"sv_design: elaboration failed: {msg}")

/-- The live handle for an embedded design, re-elaborating (and checking the
fingerprint) if this process has not elaborated it yet. -/
def getHandle (decl : Name) : CoreM Elaborated := do
  if let some e := (← handleCache.get).find? decl then return e
  let some info := findDesign? (← getEnv) decl
    | throwError "sv_expr%: `{decl}` is not an sv_design"
  let e ← elaborateArgs info.args
  unless e.netlist.fingerprint == info.fingerprint do
    throwError "sv_expr%: re-elaborating `{decl}` gave a different netlist \
      (sources changed since it was embedded?)"
  handleCache.modify (·.insert decl e)
  return e

/-! ### Commands and terms -/

/-- `sv_design foo "arg" …`: elaborate with slang arguments and embed. -/
syntax (name := svDesign) "sv_design " ident (ppSpace str)+ : command

@[command_elab svDesign] def elabSvDesign : CommandElab := fun stx => do
  let decl := (← getCurrNamespace) ++ stx[1].getId
  let args := stx[2].getArgs.map (·.isStrLit?.getD "")
  let e ← liftCoreM <| elaborateArgs args
  liftTermElabM <| embed decl e.netlist
  modifyEnv (designExt.addEntry · { decl, args, fingerprint := e.netlist.fingerprint })
  handleCache.modify (·.insert decl e)
  logInfo m!"sv_design {decl}: {e.netlist.signals.length} signals, \
    {e.netlist.assignments.length} assignments, {e.netlist.registers.length} registers"

/-- `sv_expr% foo "expr"` (or `sv_expr% "expr"`): the `Value` of a SystemVerilog
expression in the top scope of an embedded design. -/
syntax (name := svExpr) "sv_expr% " (ident)? str : term

/-- The embedded design an `sv_expr%` refers to: `name?` if given, else the one named
by a hypothesis `_ : V.isConsistent foo`, else the unique embedded design. -/
def resolveDesign (name? : Option Syntax) : TermElabM Name := do
  if let some n := name? then
    return ← realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let mut ctx : Array Name := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Valuation.isConsistent 2 do continue
    let some decl := ty.appArg!.constName? | continue
    if (findDesign? env decl).isSome then ctx := ctx.push decl
  match ctx.toList with
  | [decl] => return decl
  | _ => match (designExt.getState env).keys with
    | [decl] => return decl
    | all@(_ :: _) =>
      throwError "sv_expr%: no unique design: hypothesis `_ : V.isConsistent foo` in scope \
        for {ctx.toList}, embedded designs in the environment {all}; name one: \
        `sv_expr% foo \"…\"`"
    | [] =>
      throwError "sv_expr%: no embedded design in scope: no hypothesis `_ : V.isConsistent \
        foo` and no `sv_design` in the environment; name one explicitly"

/-- The embedded `Value` term of SystemVerilog expression `src` in the top scope
of the embedded design `decl` (signal literals shared with the netlist's). -/
def resolveValue (tac : String) (decl : Name) (src : String) : TermElabM Expr := do
  let h ← getHandle decl
  let v ← match ← h.eval src with
    | .ok v => pure v
    | .error msg => throwError "{tac}: {msg}"
  let mut sigExpr : Std.HashMap Nat Expr := {}
  for ⟨w, s⟩ in h.netlist.signals do
    sigExpr := sigExpr.insert s.id (← signalExpr w s)
  let (e, _) ← (valueExpr v.value).run { sigExpr }
  return e

@[term_elab svExpr] def elabSvExpr : TermElab := fun stx _ => do
  let decl ← resolveDesign stx[1].getOptional?
  unless (findDesign? (← getEnv) decl).isSome do
    throwError "sv_expr%: `{decl}` is not an sv_design"
  resolveValue "sv_expr%" decl (stx[2].isStrLit?.getD "")

/-- `sv_eval% V "expr"` (or `sv_eval% V foo "expr"`): shorthand for
`V.eval (sv_expr% "expr")`. -/
syntax (name := svEval) "sv_eval% " term:max (ident)? str : term

macro_rules
  | `(sv_eval% $v $[$n]? $s) =>
    `(Grounding.Rtl.Valuation.eval $v (sv_expr% $[$n]? $s))

end Grounding.SvDesign
