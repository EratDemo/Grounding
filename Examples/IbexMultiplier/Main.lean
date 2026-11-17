-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Grounding
import Examples.IbexMultiplier.Arith
import Grounding.Tactic.DualRail

open Grounding.Rtl

sv_design IbexMultidivSlow
  "third_party/ibex/rtl/ibex_cheriot_pkg.sv"
  "-F" "third_party/ibex/rtl/ibex_core.f"
  "+incdir+third_party/ibex/vendor/lowrisc_ip/ip/prim/rtl"
  "+incdir+third_party/ibex/vendor/lowrisc_ip/dv/sv/dv_utils"
  "--top" "ibex_multdiv_slow"

namespace IbexMultidivSlow

set_option maxRecDepth 20000

/-- The ALU path relation holds. -/
def AluPath (V : Valuation) : Prop :=
  V.eval (sv_expr% "(alu_adder_ext_i == ({1'b0, alu_operand_a_o} + {1'b0, alu_operand_b_o})) && (alu_adder_i == alu_adder_ext_i[32:1]) && (equal_to_zero_i == (alu_adder_i == 0))") = TritVec.ofBV 1#1

/-- The external `imd_val` constraint between consecutive states. -/
private def ValidHistoryExt (V V' : Valuation) : Prop :=
  let edge := (V.eval (sv_expr% "clk_i")).bit0 == Trit.zero &&
              (V'.eval (sv_expr% "clk_i")).bit0 == Trit.one
  let q0 := sv_expr% "imd_val_q_i[0]"
  let q1 := sv_expr% "imd_val_q_i[1]"
  (V'.eval q0 =
    bif edge then V.eval (sv_expr% "((mult_sel_i | div_sel_i) & imd_val_we_o[0]) ? imd_val_d_o[0] : imd_val_q_i[0]")
    else V.eval q0) ∧
  (V'.eval q1 =
    bif edge then V.eval (sv_expr% "((mult_sel_i | div_sel_i) & imd_val_we_o[1]) ? imd_val_d_o[1] : imd_val_q_i[1]")
    else V'.eval q1)

/-- The clock and the control/operand inputs are X-free. -/
def CtrlInputsDefined (V : Valuation) : Prop :=
  (V.eval (sv_expr% "^{data_ind_timing_i, div_sel_i, clk_i, mult_sel_i, operator_i, op_b_i, signed_mode_i, mult_en_i, div_en_i, multdiv_ready_id_i, equal_to_zero_i, alu_adder_i}")).bit0 ≠ Trit.x

/-- A valid history starts with an active (low) reset, has no X
on `data_ind_timing_i`, `div_sel_i`, `clk_i`, or the inputs feeding
`md_state_d` in any state, follows both the netlist transition
relation and the external path between every pair of neighbouring states,
and every valuation is consistent with the netlist. -/
def ValidHistory (Vs : List Valuation) : Prop :=
  (match Vs with
    | [] => False
    | V₀ :: _ => (V₀.eval (sv_expr% "rst_ni")).bit0 = Trit.zero) ∧
  (∀ V ∈ Vs.tail, V.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1) ∧
  (∀ V ∈ Vs, CtrlInputsDefined V) ∧
  (∀ V ∈ Vs, V.isConsistent IbexMultidivSlow) ∧
  (∀ p ∈ Vs.zip Vs.tail,
    IbexMultidivSlow.Transition p.1 p.2 ∧ ValidHistoryExt p.1 p.2)

/-- The multiplier's inputs are those of the MUL problem: the operator, the
multiplier enable/select, no divider enable, and the operands with their signed
mode (the ID stage keeps them stable while the instruction is in flight). -/
def MulHeld (hi : Bool) (sm : BitVec 2) (a b : BitVec 32) (V : Valuation) : Prop :=
  V.eval (sv_expr% "operator_i") = TritVec.ofBV (if hi then 1#2 else 0#2) ∧
  V.eval (sv_expr% "mult_en_i") = TritVec.ofBV 1#1 ∧
  V.eval (sv_expr% "mult_sel_i") = TritVec.ofBV 1#1 ∧
  V.eval (sv_expr% "div_en_i") = TritVec.ofBV 0#1 ∧
  V.eval (sv_expr% "signed_mode_i") = TritVec.ofBV sm ∧
  V.eval (sv_expr% "op_a_i") = TritVec.ofBV a ∧
  V.eval (sv_expr% "op_b_i") = TritVec.ofBV b

/-- **Multiplier contract.** In a valid history, if a state `V₀` is idle, then
the first state `V` (from `V₀` on) where `valid_o` is high outputs the product,
provided the MUL problem is offered (`MulHeld`) and the ALU relation holds
(`AluPath`) in the states up to and including `V`. -/
def MulContract : Prop :=
  ∀ (hi : Bool) (sm : BitVec 2) (a b : BitVec 32) (Vs : List Valuation),
    ValidHistory Vs →
    ∀ (pre : List Valuation) (V₀ : Valuation) (post : List Valuation),
      Vs = pre ++ List.cons (α := Valuation) V₀ post →
      V₀.eval (sv_expr% "md_state_q") = TritVec.ofBV 0#3 →
      ∀ V, (List.cons (α := Valuation) V₀ post).find?
          (fun V => decide (V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)) = some V →
        (∀ W ∈ (List.cons (α := Valuation) V₀ post).takeWhile
            (fun (W : Valuation) => !decide (W.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)),
          MulHeld hi sm a b W ∧ AluPath W) →
        (MulHeld hi sm a b V ∧ AluPath V) →
        V.eval (sv_expr% "multdiv_result_o") = TritVec.ofBV (mulSpec hi sm[0] sm[1] a b)

/-! `extendVal`/`mulSpec` are defined in `Examples.IbexMultiplier.Arith`. -/

/-- Sanity checks for the arithmetic layer. -/
example : mulSpec false false false 3#32 5#32 = 15#32 := by decide
example : mulSpec true true true (-1#32) (-1#32) = 0#32 := by decide
example : mulSpec true false false 0x80000000#32 0x80000000#32 = 0x40000000#32 := by decide
example : mulSpec true true false (-1#32) 2#32 = 0xFFFFFFFF#32 := by decide

/-! ### Hardware facts (one `bv_dual_rail` + `bv_decide` call each) -/

/-- The three registers whose values feed `md_state_d` are X-free. -/
def RegistersDefined (V : Valuation) : Prop :=
  (V.eval (sv_expr% "^{md_state_q, multdiv_count_q, op_b_shift_q}")).bit0 ≠ Trit.x

set_option maxHeartbeats 8000000 in
theorem registers_defined_reset {V : Valuation}
    (hc : V.isConsistent IbexMultidivSlow)
    (hrst : (V.eval (sv_expr% "rst_ni")).bit0 = Trit.zero) :
    RegistersDefined V := by
  unfold RegistersDefined
  bv_dual_rail
  bv_decide

set_option maxHeartbeats 32000000 in
/-- One step of a valid history preserves `RegistersDefined`; the SAT solver
derives the X-freeness of every input from the masks. -/
theorem step_defined {V V' : Valuation}
    (hc : V.isConsistent IbexMultidivSlow) (hc' : V'.isConsistent IbexMultidivSlow)
    (ht : IbexMultidivSlow.Transition V V')
    (hd : RegistersDefined V)
    (hx : CtrlInputsDefined V)
    (hx' : CtrlInputsDefined V')
    (hrst' : V'.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1) :
    RegistersDefined V' := by
  unfold RegistersDefined CtrlInputsDefined at *
  bv_dual_rail
  bv_decide

private theorem defined_tail (V : Valuation) (rest : List Valuation)
    (hd : RegistersDefined V)
    (hx : ∀ W ∈ (List.cons (α := Valuation) V rest), CtrlInputsDefined W)
    (hc : ∀ W ∈ (List.cons (α := Valuation) V rest), W.isConsistent IbexMultidivSlow)
    (hr : ∀ W ∈ rest, W.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1)
    (hz : ∀ p ∈ ((List.cons (α := Valuation) V rest)).zip rest,
      IbexMultidivSlow.Transition p.1 p.2 ∧ ValidHistoryExt p.1 p.2) :
    ∀ W ∈ (List.cons (α := Valuation) V rest), RegistersDefined W := by
  induction rest generalizing V with
  | nil => simpa using hd
  | cons W rest ih =>
    have hz1 := hz (V, W) (by simp)
    have hW : RegistersDefined W :=
      step_defined (hc V (by simp)) (hc W (by simp)) hz1.1 hd
        (hx V (by simp)) (hx W (by simp)) (hr W (by simp))
    have := ih W hW
      (fun X hX => hx X (by simp_all))
      (fun X hX => hc X (by simp_all)) (fun X hX => hr X (by simp_all))
      (fun p hp => hz p (by simp_all [List.zip_cons_cons]))
    intro X hX
    cases hX with
    | head => exact hd
    | tail _ h => exact this X h

/-- In a valid history every state has its FSM/counter/operand registers X-free. -/
theorem ValidHistory.registers_defined {Vs : List Valuation} (h : ValidHistory Vs) :
    ∀ V ∈ Vs, RegistersDefined V := by
  obtain ⟨h0, hr, hx, hc, hz⟩ := h
  cases Vs with
  | nil => exact absurd h0 id
  | cons V₀ rest =>
    exact defined_tail V₀ rest
      (registers_defined_reset (hc V₀ (by simp)) h0) hx hc hr hz


/-! ### FSM step facts for the multiplier

Encoding of `md_fsm_e`: IDLE=0, ABS_A=1, ABS_B=2, COMP=3, LAST=4,
CHANGE_SIGN=5, FINISH=6. Operators: MULL=0, MULH=1. Each lemma is one rising
clock edge with reset inactive -/

/-- One rising clock edge with reset inactive afterwards: both valuations are
consistent, the netlist and the external path relate them. -/
structure EdgeStep (V V' : Valuation) : Prop where
  hc : V.isConsistent IbexMultidivSlow
  hc' : V'.isConsistent IbexMultidivSlow
  ht : IbexMultidivSlow.Transition V V'
  he : ValidHistoryExt V V'
  hclk : V.eval (sv_expr% "clk_i") = TritVec.ofBV 0#1
  hclk' : V'.eval (sv_expr% "clk_i") = TritVec.ofBV 1#1
  hrst' : V'.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1

/-- The multiplier is selected and enabled with operator `op`; the control
inputs are concrete bits. -/
structure MulCtrl (V : Valuation) (op : BitVec 2) (me de dit ds rdy : BitVec 1) : Prop where
  hme : V.eval (sv_expr% "mult_en_i") = TritVec.ofBV me
  hde : V.eval (sv_expr% "div_en_i") = TritVec.ofBV de
  hen : me ||| de = 1#1
  hms : V.eval (sv_expr% "mult_sel_i") = TritVec.ofBV 1#1
  hop : V.eval (sv_expr% "operator_i") = TritVec.ofBV op
  hdit : V.eval (sv_expr% "data_ind_timing_i") = TritVec.ofBV dit
  hds : V.eval (sv_expr% "div_sel_i") = TritVec.ofBV ds
  hrdy : V.eval (sv_expr% "multdiv_ready_id_i") = TritVec.ofBV rdy

/-- The operands and signed mode offered to the multiplier. -/
structure MulOperands (V : Valuation) (sm : BitVec 2) (a b : BitVec 32) : Prop where
  hsm : V.eval (sv_expr% "signed_mode_i") = TritVec.ofBV sm
  hoa : V.eval (sv_expr% "op_a_i") = TritVec.ofBV a
  hob : V.eval (sv_expr% "op_b_i") = TritVec.ofBV b

/-- The datapath registers of the multiplier. -/
def MulRegs (V : Valuation) (pa pb acc : BitVec 33) : Prop :=
  V.eval (sv_expr% "op_a_shift_q") = TritVec.ofBV pa ∧
  V.eval (sv_expr% "op_b_shift_q") = TritVec.ofBV pb ∧
  V.eval (sv_expr% "accum_window_q") = TritVec.ofBV acc

/-- The FSM state register holds `s`. -/
def InState (V : Valuation) (s : BitVec 3) : Prop :=
  V.eval (sv_expr% "md_state_q") = TritVec.ofBV s

set_option hygiene false in
/-- Destructure an `EdgeStep` and reduce the external path for the rising
edge, leaving it in `V.eval` form. -/
macro "unpack_edge" hE:ident : tactic => `(tactic| (
  obtain ⟨hc, hc', ht, he, hclk, hclk', hrst'⟩ := $hE
  unfold ValidHistoryExt at he
  obtain ⟨hq0, hq1⟩ := he
  simp only [hclk, hclk', TritVec.bit0_ofBV] at hq0 hq1
  have hedge : (Trit.ofBool (0#1)[0] == Trit.zero && Trit.ofBool (1#1)[0] == Trit.one) = true := by
    decide
  simp only [hedge, Bool.cond_true] at hq0 hq1))

set_option maxHeartbeats 32000000 in
/-- IDLE, MULL: load the shifted operands; go to LAST iff `b >> 1 = 0` outside
data-independent timing mode. -/
theorem step_idle_mull {V V' : Valuation} {a b : BitVec 32} {sm : BitVec 2}
    {me de dit ds rdy : BitVec 1}
    (hE : EdgeStep V V') (hS : InState V 0#3)
    (hC : MulCtrl V 0#2 me de dit ds rdy) (hO : MulOperands V sm a b) :
    V'.eval (sv_expr% "md_state_q") = TritVec.ofBV
      (bif (dit == 0#1 && (ext33 (sm[1]) b >>> 1) == 0#33) then 4#3 else 3#3) ∧
    V'.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV 31#5 ∧
    V'.eval (sv_expr% "op_a_shift_q") = TritVec.ofBV (ext33 (sm[0]) a <<< 1) ∧
    V'.eval (sv_expr% "op_b_shift_q") = TritVec.ofBV (ext33 (sm[1]) b >>> 1) ∧
    V'.eval (sv_expr% "accum_window_q") = TritVec.ofBV (bwpp (ext33 (sm[0]) a) (b.getLsbD 0)) := by
  unpack_edge hE
  obtain ⟨hme, hde, hen, hms, hop, hdit, hds, hrdy⟩ := hC
  obtain ⟨hsm, hoa, hob⟩ := hO
  unfold InState at hS
  unfold ext33 bwpp
  bv_dual_rail
  bv_decide

set_option maxHeartbeats 32000000 in
/-- IDLE, MULH: load the operands and the first (shifted) partial product. -/
theorem step_idle_mulh {V V' : Valuation} {a b : BitVec 32} {sm : BitVec 2}
    {me de dit ds rdy : BitVec 1}
    (hE : EdgeStep V V') (hS : InState V 0#3)
    (hC : MulCtrl V 1#2 me de dit ds rdy) (hO : MulOperands V sm a b) :
    V'.eval (sv_expr% "md_state_q") = TritVec.ofBV 3#3 ∧
    V'.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV 31#5 ∧
    V'.eval (sv_expr% "op_a_shift_q") = TritVec.ofBV (ext33 (sm[0]) a) ∧
    V'.eval (sv_expr% "op_b_shift_q") = TritVec.ofBV (ext33 (sm[1]) b >>> 1) ∧
    V'.eval (sv_expr% "accum_window_q") = TritVec.ofBV
      ((bwpp (ext33 (sm[0]) a) (b.getLsbD 0) >>> 1) ||| 0x100000000#33) := by
  unpack_edge hE
  obtain ⟨hme, hde, hen, hms, hop, hdit, hds, hrdy⟩ := hC
  obtain ⟨hsm, hoa, hob⟩ := hO
  unfold InState at hS
  unfold ext33 bwpp
  bv_dual_rail
  bv_decide

set_option maxHeartbeats 32000000 in
/-- COMP, MULL: one shift-add step. -/
theorem step_comp_mull {V V' : Valuation} {pa pb acc : BitVec 33} {c : BitVec 5}
    {me de dit ds rdy : BitVec 1}
    (hE : EdgeStep V V') (hA : AluPath V) (hS : InState V 3#3)
    (hC : MulCtrl V 0#2 me de dit ds rdy) (hR : MulRegs V pa pb acc)
    (hcnt : V.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV c) :
    V'.eval (sv_expr% "md_state_q") = TritVec.ofBV
      (bif ((dit == 0#1 && (pb >>> 1) == 0#33) || c == 1#5) then 4#3 else 3#3) ∧
    V'.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV (c - 1#5) ∧
    V'.eval (sv_expr% "op_a_shift_q") = TritVec.ofBV (pa <<< 1) ∧
    V'.eval (sv_expr% "op_b_shift_q") = TritVec.ofBV (pb >>> 1) ∧
    V'.eval (sv_expr% "accum_window_q") = TritVec.ofBV (acc + bwpp pa (pb.getLsbD 0)) := by
  unpack_edge hE
  unfold AluPath at hA
  obtain ⟨hme, hde, hen, hms, hop, hdit, hds, hrdy⟩ := hC
  obtain ⟨hpa, hpb, hacc⟩ := hR
  unfold InState at hS
  unfold bwpp
  bv_dual_rail
  bv_decide

set_option maxHeartbeats 32000000 in
/-- COMP, MULH: one Baugh-Wooley step; the window keeps the carry. -/
theorem step_comp_mulh {V V' : Valuation} {pa pb acc : BitVec 33} {c : BitVec 5}
    {me de dit ds rdy : BitVec 1}
    (hE : EdgeStep V V') (hA : AluPath V) (hS : InState V 3#3)
    (hC : MulCtrl V 1#2 me de dit ds rdy) (hR : MulRegs V pa pb acc)
    (hcnt : V.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV c) :
    V'.eval (sv_expr% "md_state_q") = TritVec.ofBV (bif c == 1#5 then 4#3 else 3#3) ∧
    V'.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV (c - 1#5) ∧
    V'.eval (sv_expr% "op_a_shift_q") = TritVec.ofBV pa ∧
    V'.eval (sv_expr% "op_b_shift_q") = TritVec.ofBV (pb >>> 1) ∧
    V'.eval (sv_expr% "accum_window_q") = TritVec.ofBV ((add34 acc (bwpp pa (pb.getLsbD 0))).extractLsb' 1 33) := by
  unpack_edge hE
  unfold AluPath at hA
  obtain ⟨hme, hde, hen, hms, hop, hdit, hds, hrdy⟩ := hC
  obtain ⟨hpa, hpb, hacc⟩ := hR
  unfold InState at hS
  unfold bwpp add34
  bv_dual_rail
  bv_decide

set_option maxHeartbeats 32000000 in
/-- No rising edge: when the clock is defined on both sides and does not go
0 → 1 (reset inactive afterwards), the FSM registers and the accumulator hold. -/
theorem step_hold {V V' : Valuation} {k k' : BitVec 1}
    (hc : V.isConsistent IbexMultidivSlow) (hc' : V'.isConsistent IbexMultidivSlow)
    (ht : IbexMultidivSlow.Transition V V') (he : ValidHistoryExt V V')
    (hclk : V.eval (sv_expr% "clk_i") = TritVec.ofBV k)
    (hclk' : V'.eval (sv_expr% "clk_i") = TritVec.ofBV k')
    (hne : (k == 0#1 && k' == 1#1) = false)
    (hrst' : V'.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1) :
    V'.eval (sv_expr% "md_state_q") = V.eval (sv_expr% "md_state_q") ∧
    V'.eval (sv_expr% "multdiv_count_q") = V.eval (sv_expr% "multdiv_count_q") ∧
    V'.eval (sv_expr% "op_a_shift_q") = V.eval (sv_expr% "op_a_shift_q") ∧
    V'.eval (sv_expr% "op_b_shift_q") = V.eval (sv_expr% "op_b_shift_q") ∧
    V'.eval (sv_expr% "accum_window_q") = V.eval (sv_expr% "accum_window_q") := by
  unfold ValidHistoryExt at he
  obtain ⟨hq0, hq1⟩ := he
  simp only [hclk, hclk', TritVec.bit0_ofBV] at hq0 hq1
  have hedge : (Trit.ofBool k[0] == Trit.zero && Trit.ofBool k'[0] == Trit.one) = false := by
    revert hne
    generalize k = x; generalize k' = y
    decide +revert
  simp only [hedge, Bool.cond_false] at hq0 hq1
  bv_dual_rail
  bv_decide

/-- `valid_o` as a function of the FSM state and the operator: high in FINISH,
and in LAST for MULL/MULH. -/
theorem valid_iff {V : Valuation} {s : BitVec 3} {op : BitVec 2}
    (hc : V.isConsistent IbexMultidivSlow) (hS : InState V s)
    (hop : V.eval (sv_expr% "operator_i") = TritVec.ofBV op) :
    V.eval (sv_expr% "valid_o") =
      TritVec.ofBV (bif (s == 6#3 || (s == 4#3 && op.ult 2#2)) then 1#1 else 0#1) := by
  unfold InState at hS
  bv_dual_rail
  bv_decide

set_option maxHeartbeats 8000000 in
/-- In IDLE and COMP the multiplier does not signal valid, whatever the operator. -/
theorem valid_zero {V : Valuation} {s : BitVec 3}
    (hc : V.isConsistent IbexMultidivSlow) (hS : InState V s) (hs : s = 0#3 ∨ s = 3#3) :
    V.eval (sv_expr% "valid_o") = TritVec.ofBV 0#1 := by
  rcases hs with rfl | rfl <;> (unfold InState at hS; bv_dual_rail; bv_decide)

set_option maxHeartbeats 32000000 in
/-- LAST, MULL/MULH: `valid_o` is high and the result is the final sum. -/
theorem last_output {V : Valuation} {hi : Bool} {pa pb acc : BitVec 33}
    (hc : V.isConsistent IbexMultidivSlow) (hA : AluPath V) (hS : InState V 4#3)
    (hde : V.eval (sv_expr% "div_en_i") = TritVec.ofBV 0#1)
    (hop : V.eval (sv_expr% "operator_i") = TritVec.ofBV (bif hi then 1#2 else 0#2))
    (hR : MulRegs V pa pb acc) :
    V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1 ∧
    V.eval (sv_expr% "multdiv_result_o") = TritVec.ofBV (lastResult hi pa pb acc) := by
  obtain ⟨hpa, hpb, hacc⟩ := hR
  unfold AluPath at hA
  unfold InState at hS
  cases hi <;> simp only [Bool.cond_true, Bool.cond_false] at hop <;>
    unfold lastResult bwpp <;> simp only [Bool.cond_true, Bool.cond_false] <;>
    bv_dual_rail <;> bv_decide


/-! ### The contract proof -/

set_option maxHeartbeats 8000000 in
/-- The clock and the control inputs read by the FSM are concrete bits. -/
theorem ctrl_bits {V : Valuation} (hc : V.isConsistent IbexMultidivSlow)
    (hx : CtrlInputsDefined V) :
    (V.eval (sv_expr% "clk_i")).bit0 ≠ Trit.x ∧
    (V.eval (sv_expr% "data_ind_timing_i")).bit0 ≠ Trit.x ∧
    (V.eval (sv_expr% "div_sel_i")).bit0 ≠ Trit.x ∧
    (V.eval (sv_expr% "multdiv_ready_id_i")).bit0 ≠ Trit.x := by
  unfold CtrlInputsDefined at hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (bv_dual_rail; bv_decide)

/-- The multiplier is idle, or in COMP step `j` (with `31 - j` steps to go) with the
datapath registers in the window of the arithmetic invariant. -/
def PhaseRun (hi : Bool) (sm : BitVec 2) (a b : BitVec 32) (V : Valuation) : Prop :=
  InState V 0#3 ∨
  ∃ j pa pb acc, j ≤ 30 ∧ InState V 3#3 ∧
    V.eval (sv_expr% "multdiv_count_q") = TritVec.ofBV (BitVec.ofNat 5 (31 - j)) ∧
    MulRegs V pa pb acc ∧
    ((hi = false ∧ MullWin sm[0] sm[1] a b j pa pb acc) ∨ (hi = true ∧ MulhWin sm[0] sm[1] a b j pa pb acc))

/-- The multiplier is in LAST with the final window. -/
def PhaseLast (hi : Bool) (sm : BitVec 2) (a b : BitVec 32) (V : Valuation) : Prop :=
  ∃ j pa pb acc, j ≤ 31 ∧ InState V 4#3 ∧ MulRegs V pa pb acc ∧
    ((hi = false ∧ MullWin sm[0] sm[1] a b j pa pb acc ∧ (pb = 0#33 ∨ j = 31)) ∨
     (hi = true ∧ MulhWin sm[0] sm[1] a b j pa pb acc ∧ j = 31))

theorem count_eq_one_iff {j : Nat} (hj : j ≤ 30) :
    (BitVec.ofNat 5 (31 - j) == 1#5) = true ↔ j = 30 := by
  have : ∀ j, j < 31 → ((BitVec.ofNat 5 (31 - j) == 1#5) = true ↔ j = 30) := by decide
  exact this j (by omega)

theorem count_sub_one {j : Nat} (hj : j ≤ 30) :
    BitVec.ofNat 5 (31 - j) - 1#5 = BitVec.ofNat 5 (31 - (j + 1)) := by
  have : ∀ j, j < 31 → BitVec.ofNat 5 (31 - j) - 1#5 = BitVec.ofNat 5 (31 - (j + 1)) := by decide
  exact this j (by omega)

set_option maxHeartbeats 8000000 in
/-- One step of the multiplier: from idle or COMP to COMP or LAST. -/
theorem phase_step {hi : Bool} {sm : BitVec 2} {a b : BitVec 32} {V V' : Valuation}
    (hc : V.isConsistent IbexMultidivSlow) (hc' : V'.isConsistent IbexMultidivSlow)
    (hx : CtrlInputsDefined V) (hx' : CtrlInputsDefined V')
    (ht : IbexMultidivSlow.Transition V V') (he : ValidHistoryExt V V')
    (hrst' : V'.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1)
    (hH : MulHeld hi sm a b V) (hA : AluPath V)
    (hP : PhaseRun hi sm a b V) :
    PhaseRun hi sm a b V' ∨ PhaseLast hi sm a b V' := by
  obtain ⟨hclkx, hditx, hdsx, hrdyx⟩ := ctrl_bits hc hx
  obtain ⟨hclkx', -, -, -⟩ := ctrl_bits hc' hx'
  obtain ⟨k, hk⟩ := TritVec.exists_ofBV_of_bit0 hclkx
  obtain ⟨k', hk'⟩ := TritVec.exists_ofBV_of_bit0 hclkx'
  obtain ⟨dit, hdit⟩ := TritVec.exists_ofBV_of_bit0 hditx
  obtain ⟨ds, hds⟩ := TritVec.exists_ofBV_of_bit0 hdsx
  obtain ⟨rdy, hrdy⟩ := TritVec.exists_ofBV_of_bit0 hrdyx
  obtain ⟨hop, hme, hms, hde, hsm, hoa, hob⟩ := hH
  by_cases hedge : (k == 0#1 && k' == 1#1) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
    obtain ⟨rfl, rfl⟩ := hedge
    have hE : EdgeStep V V' := ⟨hc, hc', ht, he, hk, hk', hrst'⟩
    have hO : MulOperands V sm a b := ⟨hsm, hoa, hob⟩
    rcases hP with hS | ⟨j, pa, pb, acc, hj, hS, hcnt, hR, hW⟩
    · cases hi
      · have hop' : V.eval (sv_expr% "operator_i") = TritVec.ofBV 0#2 := by simpa using hop
        have hC : MulCtrl V 0#2 1#1 0#1 dit ds rdy := ⟨hme, hde, by decide, hms, hop', hdit, hds, hrdy⟩
        obtain ⟨h1, h2, h3, h4, h5⟩ := step_idle_mull hE hS hC hO
        by_cases hcond : (dit == 0#1 && (ext33 sm[1] b >>> 1) == 0#33) = true
        · rw [hcond, Bool.cond_true] at h1
          right
          refine ⟨0, _, _, _, by omega, h1, ⟨h3, h4, h5⟩, Or.inl ⟨rfl, MullWin.zero sm[0] sm[1] a b, Or.inl ?_⟩⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.2
        · rw [Bool.eq_false_iff.mpr hcond, Bool.cond_false] at h1
          left; right
          exact ⟨0, _, _, _, by omega, h1, h2, ⟨h3, h4, h5⟩, Or.inl ⟨rfl, MullWin.zero sm[0] sm[1] a b⟩⟩
      · have hop' : V.eval (sv_expr% "operator_i") = TritVec.ofBV 1#2 := by simpa using hop
        have hC : MulCtrl V 1#2 1#1 0#1 dit ds rdy := ⟨hme, hde, by decide, hms, hop', hdit, hds, hrdy⟩
        obtain ⟨h1, h2, h3, h4, h5⟩ := step_idle_mulh hE hS hC hO
        left; right
        exact ⟨0, _, _, _, by omega, h1, h2, ⟨h3, h4, h5⟩, Or.inr ⟨rfl, MulhWin.zero sm[0] sm[1] a b⟩⟩
    · cases hi
      · have hop' : V.eval (sv_expr% "operator_i") = TritVec.ofBV 0#2 := by simpa using hop
        have hC : MulCtrl V 0#2 1#1 0#1 dit ds rdy := ⟨hme, hde, by decide, hms, hop', hdit, hds, hrdy⟩
        have hw : MullWin sm[0] sm[1] a b j pa pb acc := by
          rcases hW with ⟨_, hw⟩ | ⟨h, _⟩
          · exact hw
          · exact absurd h (by simp)
        obtain ⟨h1, h2, h3, h4, h5⟩ := step_comp_mull hE hA hS hC hR hcnt
        have hw' := MullWin.step (by omega) hw
        by_cases hcond : ((dit == 0#1 && (pb >>> 1) == 0#33) || BitVec.ofNat 5 (31 - j) == 1#5) = true
        · rw [hcond, Bool.cond_true] at h1
          right
          refine ⟨j + 1, _, _, _, by omega, h1, ⟨h3, h4, h5⟩, Or.inl ⟨rfl, hw', ?_⟩⟩
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨_, hz⟩ | hc1
          · exact Or.inl hz
          · exact Or.inr (by have := (count_eq_one_iff hj).1 (by simpa using hc1); omega)
        · rw [Bool.eq_false_iff.mpr hcond, Bool.cond_false] at h1
          have hne : j ≠ 30 := by
            intro h30
            apply hcond
            simp only [Bool.or_eq_true]
            exact Or.inr ((count_eq_one_iff hj).2 h30)
          rw [count_sub_one hj] at h2
          left; right
          exact ⟨j + 1, _, _, _, by omega, h1, h2, ⟨h3, h4, h5⟩, Or.inl ⟨rfl, hw'⟩⟩
      · have hop' : V.eval (sv_expr% "operator_i") = TritVec.ofBV 1#2 := by simpa using hop
        have hC : MulCtrl V 1#2 1#1 0#1 dit ds rdy := ⟨hme, hde, by decide, hms, hop', hdit, hds, hrdy⟩
        have hw : MulhWin sm[0] sm[1] a b j pa pb acc := by
          rcases hW with ⟨h, _⟩ | ⟨_, hw⟩
          · exact absurd h (by simp)
          · exact hw
        obtain ⟨h1, h2, h3, h4, h5⟩ := step_comp_mulh hE hA hS hC hR hcnt
        have hw' := MulhWin.step hw
        by_cases hcond : (BitVec.ofNat 5 (31 - j) == 1#5) = true
        · rw [hcond, Bool.cond_true] at h1
          have hj30 := (count_eq_one_iff hj).1 hcond
          right
          exact ⟨j + 1, _, _, _, by omega, h1, ⟨h3, h4, h5⟩, Or.inr ⟨rfl, hw', by omega⟩⟩
        · rw [Bool.eq_false_iff.mpr hcond, Bool.cond_false] at h1
          have hne : j ≠ 30 := fun h30 => hcond ((count_eq_one_iff hj).2 h30)
          rw [count_sub_one hj] at h2
          left; right
          exact ⟨j + 1, _, _, _, by omega, h1, h2, ⟨h3, h4, h5⟩, Or.inr ⟨rfl, hw'⟩⟩
  · have hne : (k == 0#1 && k' == 1#1) = false := Bool.eq_false_iff.mpr hedge
    obtain ⟨h1, h2, h3, h4, h5⟩ := step_hold hc hc' ht he hk hk' hne hrst'
    left
    rcases hP with hS | ⟨j, pa, pb, acc, hj, hS, hcnt, hR, hW⟩
    · left
      unfold InState at hS ⊢
      rw [h1]; exact hS
    · right
      obtain ⟨hpa, hpb, hacc⟩ := hR
      refine ⟨j, pa, pb, acc, hj, ?_, ?_, ⟨?_, ?_, ?_⟩, hW⟩
      · unfold InState at hS ⊢; rw [h1]; exact hS
      · rw [h2]; exact hcnt
      · rw [h3]; exact hpa
      · rw [h4]; exact hpb
      · rw [h5]; exact hacc

/-- A segment of a valid history: the facts the run needs from `ValidHistory`. -/
structure Seg (L : List Valuation) : Prop where
  hc : ∀ V ∈ L, V.isConsistent IbexMultidivSlow
  hx : ∀ V ∈ L, CtrlInputsDefined V
  hr : ∀ V ∈ L.tail, V.eval (sv_expr% "rst_ni") = TritVec.ofBV 1#1
  hz : ∀ p ∈ L.zip L.tail, IbexMultidivSlow.Transition p.1 p.2 ∧ ValidHistoryExt p.1 p.2

theorem Seg.tail {x : Valuation} {M : List Valuation} (h : Seg (List.cons (α := Valuation) x M)) :
    Seg M := by
  refine ⟨fun V hV => h.hc V (List.Mem.tail _ hV), fun V hV => h.hx V (List.Mem.tail _ hV),
    fun V hV => h.hr V ?_, fun p hp => h.hz p ?_⟩
  · cases M with
    | nil => exact nomatch hV
    | cons m M' => exact List.Mem.tail _ hV
  · cases M with
    | nil => exact nomatch hp
    | cons m M' => exact List.Mem.tail _ hp

theorem Seg.suffix {pre L : List Valuation} (h : Seg (pre ++ L)) : Seg L := by
  induction pre with
  | nil => simpa using h
  | cons x pre ih => exact ih (Seg.tail h)

theorem ValidHistory.seg {Vs : List Valuation} (h : ValidHistory Vs) : Seg Vs :=
  ⟨h.2.2.2.1, h.2.2.1, h.2.1, h.2.2.2.2⟩

/-- In LAST with MULL/MULH, `valid_o` is high; in IDLE/COMP it is low. -/
theorem phase_valid {hi : Bool} {sm : BitVec 2} {a b : BitVec 32} {X : Valuation}
    (hc : X.isConsistent IbexMultidivSlow)
    (hop : X.eval (sv_expr% "operator_i") = TritVec.ofBV (if hi then 1#2 else 0#2)) :
    (PhaseRun hi sm a b X → X.eval (sv_expr% "valid_o") = TritVec.ofBV 0#1) ∧
    (PhaseLast hi sm a b X → X.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1) := by
  constructor
  · rintro (hS | ⟨j, pa, pb, acc, hj, hS, _⟩)
    · exact valid_zero hc hS (Or.inl rfl)
    · exact valid_zero hc hS (Or.inr rfl)
  · rintro ⟨j, pa, pb, acc, hj, hS, _⟩
    rw [valid_iff hc hS hop]
    cases hi <;> decide

set_option maxHeartbeats 8000000 in
/-- Run the multiplier from a phase state until `valid_o`. -/
theorem run {hi : Bool} {sm : BitVec 2} {a b : BitVec 32} :
    ∀ (rest : List Valuation) (X : Valuation),
      Seg (List.cons (α := Valuation) X rest) →
      (PhaseRun hi sm a b X ∨ PhaseLast hi sm a b X) →
      ∀ V, (List.cons (α := Valuation) X rest).find?
          (fun V => decide (V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)) = some V →
        (∀ W ∈ (List.cons (α := Valuation) X rest).takeWhile
            (fun (W : Valuation) => !decide (W.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)),
          MulHeld hi sm a b W ∧ AluPath W) →
        (MulHeld hi sm a b V ∧ AluPath V) →
        V.eval (sv_expr% "multdiv_result_o") = TritVec.ofBV (mulSpec hi sm[0] sm[1] a b) := by
  intro rest
  induction rest with
  | nil =>
    intro X hSeg hPh V hfind hheld hfinal
    have hcX := hSeg.hc X (by simp)
    by_cases hv : X.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1
    · rw [List.find?_cons_of_pos (p := fun V : Valuation => decide (V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)) (decide_eq_true hv)] at hfind
      cases hfind
      obtain ⟨⟨hop, _, _, hde, _⟩, hA⟩ := hfinal
      rcases hPh with hR | ⟨j, pa, pb, acc, hj, hS, hRg, hend⟩
      · exfalso
        have := (phase_valid (a := a) (b := b) hcX hop).1 hR
        rw [this] at hv; simp at hv
      · have hop' : X.eval (sv_expr% "operator_i") = TritVec.ofBV (bif hi then 1#2 else 0#2) := by
          rw [hop]; cases hi <;> rfl
        obtain ⟨_, hres⟩ := last_output hcX hA hS hde hop' hRg
        rw [hres, result_correct (by omega) hend]
    · exfalso
      rw [List.find?_cons_of_neg (p := fun V : Valuation => decide (V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)) (by rw [decide_eq_true_eq]; exact hv)] at hfind
      cases hfind
  | cons W rest' ih =>
    intro X hSeg hPh V hfind hheld hfinal
    have hcX := hSeg.hc X (by simp)
    by_cases hv : X.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1
    · rw [List.find?_cons_of_pos (p := fun V : Valuation => decide (V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)) (decide_eq_true hv)] at hfind
      cases hfind
      obtain ⟨⟨hop, _, _, hde, _⟩, hA⟩ := hfinal
      rcases hPh with hR | ⟨j, pa, pb, acc, hj, hS, hRg, hend⟩
      · exfalso
        have := (phase_valid (a := a) (b := b) hcX hop).1 hR
        rw [this] at hv; simp at hv
      · have hop' : X.eval (sv_expr% "operator_i") = TritVec.ofBV (bif hi then 1#2 else 0#2) := by
          rw [hop]; cases hi <;> rfl
        obtain ⟨_, hres⟩ := last_output hcX hA hS hde hop' hRg
        rw [hres, result_correct (by omega) hend]
    · have htw : List.takeWhile (α := Valuation)
            (fun W => !decide (W.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1))
            (List.cons (α := Valuation) X (List.cons (α := Valuation) W rest')) =
          List.cons (α := Valuation) X (List.takeWhile (α := Valuation)
            (fun W => !decide (W.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1))
            (List.cons (α := Valuation) W rest')) :=
        List.takeWhile_cons_of_pos (by rw [Bool.not_eq_true']; exact decide_eq_false hv)
      have hXheld := hheld X (by rw [htw]; exact List.Mem.head _)
      rcases hPh with hR | hL
      · rw [List.find?_cons_of_neg (p := fun V : Valuation => decide (V.eval (sv_expr% "valid_o") = TritVec.ofBV 1#1)) (by rw [decide_eq_true_eq]; exact hv)] at hfind
        have hstep := phase_step hcX (hSeg.hc W (by simp)) (hSeg.hx X (by simp)) (hSeg.hx W (by simp))
          (hSeg.hz (X, W) (by simp)).1 (hSeg.hz (X, W) (by simp)).2
          (hSeg.hr W (by simp)) hXheld.1 hXheld.2 hR
        exact ih W hSeg.tail hstep V hfind (fun T hT => hheld T (by rw [htw]; exact List.Mem.tail _ hT)) hfinal
      · exfalso
        exact hv ((phase_valid (a := a) (b := b) hcX hXheld.1.1).2 hL)

/-- **Multiplier correctness**: `MulContract` holds. -/
theorem mul_contract : MulContract := by
  intro hi sm a b Vs hV pre V₀ post hVs hidle V hfind hheld hfinal
  subst hVs
  exact run post V₀ (Seg.suffix hV.seg) (Or.inl (Or.inl hidle)) V hfind hheld hfinal

end IbexMultidivSlow
