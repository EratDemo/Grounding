-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
/-
Grounding RTL value printing.

`Repr` for `Value` prints a SystemVerilog-like expression. Values are shared
DAGs (a sub-expression can be referenced many times), so printing the tree
naively is exponential. Instead, every non-leaf node that is referenced more
than once is printed once as a labelled binding and referred to by its label:

```
let %0 := (a ^ b)
let %1 := (%0 & %0)
(%1 | %0)
```

Leaves (signals and constants) are always printed inline. Node identity is
structural, via the `BEq`/`Hashable` instances on `Σ w, Value w` (cached hash,
pointer fast path), so both passes are linear in the size of the DAG.
-/

import Grounding.Rtl.ValueHash
import Std.Data.HashMap

namespace Grounding.Rtl

namespace Value

/-- Children of a node, as width-carrying values (in printing order). -/
def children : {w : Nat} → Value w → List (Σ w, Value w)
  | _, .const _ | _, .signal _ => []
  | _, .not a => [⟨_, a⟩]
  | _, .and a b | _, .or a b | _, .xor a b | _, .mul a b
  | _, .udiv a b | _, .umod a b | _, .sdivTrunc a b | _, .sdivFloor a b
  | _, .smodTrunc a b | _, .smodFloor a b
  | _, .eq a b | _, .ult a b | _, .slt a b | _, .eqx a b => [⟨_, a⟩, ⟨_, b⟩]
  | _, .mux s a b => [⟨_, s⟩, ⟨_, a⟩, ⟨_, b⟩]
  | _, .adc a b c => [⟨_, a⟩, ⟨_, b⟩, ⟨_, c⟩]
  | _, .shl _ _ a m | _, .ushr _ _ a m | _, .sshr _ _ a m | _, .xshr _ _ a m => [⟨_, a⟩, ⟨_, m⟩]
  | _, .replicate _ a => [⟨_, a⟩]
  | _, .concatNode _ ws parts _ => (List.finRange ws.size).map (fun i => ⟨_, parts i⟩)
  | _, .partSelect _ src _ _ => [⟨_, src⟩]

/-- Leaves are printed inline and never labelled. -/
def isLeaf : {w : Nat} → Value w → Bool
  | _, .const _ | _, .signal _ => true
  | _, _ => false

end Value

namespace Repr

abbrev Key := Σ w, Value w

/-- Reference counts of every node reachable from the roots (each node's
children are counted once per distinct parent occurrence, and visited once). -/
partial def countRefs (roots : List Key) : Std.HashMap Key Nat :=
  go roots {}
where
  go : List Key → Std.HashMap Key Nat → Std.HashMap Key Nat
    | [], m => m
    | k :: rest, m =>
      match m[k]? with
      | some n => go rest (m.insert k (n + 1))
      | none => go (k.2.children ++ rest) (m.insert k 1)

def tritChar : Trit → Char
  | .zero => '0'
  | .one => '1'
  | .x => 'x'

/-- A constant as a SystemVerilog literal, e.g. `4'b10x1` (MSB first). -/
def constStr {w : Nat} (c : TritVec w) : String :=
  s!"{w}'b" ++ String.ofList (c.bits.toList.reverse.map tritChar)

def signalStr {w : Nat} (s : Signal w) : String :=
  s.name.getD s!"#{s.id}"

/-- The text of one node, given the printed text of its children. -/
def nodeText {w : Nat} (v : Value w) (args : List String) : String :=
  let arg (i : Nat) : String := args.getD i "?"
  let bin (op : String) : String := s!"({arg 0} {op} {arg 1})"
  let call (f : String) : String := s!"{f}({", ".intercalate args})"
  match v with
  | .const c => constStr c
  | .signal s => signalStr s
  | .not _ => s!"~{arg 0}"
  | .and _ _ => bin "&"
  | .or _ _ => bin "|"
  | .xor _ _ => bin "^"
  | .mul _ _ => bin "*"
  | .eq _ _ => bin "=="
  | .eqx _ _ => bin "==="
  | .ult _ _ => bin "<"
  | .slt _ _ => s!"$signed({arg 0}) < $signed({arg 1})"
  | .udiv _ _ => bin "/"
  | .umod _ _ => bin "%"
  | .sdivTrunc _ _ => call "sdiv_trunc"
  | .sdivFloor _ _ => call "sdiv_floor"
  | .smodTrunc _ _ => call "smod_trunc"
  | .smodFloor _ _ => call "smod_floor"
  | .mux _ _ _ => s!"({arg 0} ? {arg 1} : {arg 2})"
  | .adc _ _ _ => call "adc"
  | .shl stride _ _ _ =>
      if stride = 1 then bin "<<" else call s!"shl_stride({stride})"
  | .ushr stride _ _ _ =>
      if stride = 1 then bin ">>" else call s!"ushr_stride({stride})"
  | .sshr stride _ _ _ =>
      if stride = 1 then bin ">>>" else call s!"sshr_stride({stride})"
  | .xshr stride _ _ _ =>
      if stride = 1 then call "xshr" else call s!"xshr_stride({stride})"
  | .replicate _ _ => call "replicate"
  | .concatNode _ _ _ _ => "{" ++ ", ".intercalate args ++ "}"
  | @Value.partSelect w _ _ offset _ =>
    if w = 1 then s!"{arg 0}[{offset}]" else s!"{arg 0}[{offset + w - 1}:{offset}]"

/-- Printer state: labels assigned so far and the emitted bindings. -/
structure State where
  labels : Std.HashMap Key Nat := {}
  bindings : Array String := #[]

/-- Print `k`, emitting bindings for shared children first (post-order), and
return the text that refers to it. `shared k` says whether `k` gets a label. -/
partial def print (shared : Key → Bool) (k : Key) : StateM State String := do
  if let some n := (← get).labels[k]? then
    return s!"%{n}"
  let args ← k.2.children.mapM (print shared)
  let text : String := nodeText k.2 args
  if shared k then
    let st ← get
    let n := st.labels.size
    set { st with labels := st.labels.insert k n,
                  bindings := st.bindings.push s!"let %{n} := {text}" }
    return s!"%{n}"
  return text

/-- Render roots with shared sub-expressions labelled. Returns the bindings and
the text of each root. -/
def render (roots : List Key) : Array String × List String :=
  let refs := countRefs roots
  let shared (k : Key) : Bool := !k.2.isLeaf && refs.getD k 0 > 1
  let (texts, st) := (roots.mapM (print shared)).run {}
  (st.bindings, texts)

/-- One value as a multi-line `Format`: bindings, then the expression. -/
def format (k : Key) : Std.Format :=
  let (bindings, texts) := render [k]
  let body := texts.headD ""
  if bindings.isEmpty then body
  else Std.Format.joinSep ((bindings.toList ++ [body]).map Std.Format.text) Std.Format.line

end Repr

instance : Repr (Value w) where
  reprPrec v _ := Repr.format ⟨w, v⟩

end Grounding.Rtl
