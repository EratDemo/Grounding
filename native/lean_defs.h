// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <lean/lean.h>

// Exported by Grounding.Rtl.Builder. Arguments are owned (the callee consumes
// one reference) and results are owned.
extern "C" {
lean_object *grounding_builder_new(lean_object *unit);
lean_object *grounding_builder_add_signal(
		lean_object *builder, lean_object *width, lean_object *name);
lean_object *grounding_builder_const(lean_object *width, uint8_t trit);
lean_object *grounding_builder_const_bits(lean_object *codes);
lean_object *grounding_builder_part_select(
		lean_object *value, lean_object *offset, lean_object *width);
lean_object *grounding_builder_concat(lean_object *parts);
lean_object *grounding_builder_add_port(
		lean_object *builder, lean_object *name, uint8_t direction, lean_object *value);
lean_object *grounding_builder_add_assignment(
		lean_object *builder, lean_object *target, lean_object *source);
lean_object *grounding_builder_add_register(
		lean_object *builder, lean_object *q, lean_object *d, lean_object *clk, uint8_t clk_pol);
lean_object *grounding_builder_add_aload_register(lean_object *builder, lean_object *q,
		lean_object *d, lean_object *clk, uint8_t clk_pol, lean_object *trig, uint8_t trig_pol,
		lean_object *value);
lean_object *grounding_builder_add_aload2_register(lean_object *builder, lean_object *q,
		lean_object *d, lean_object *clk, uint8_t clk_pol, lean_object *trig1, uint8_t trig1_pol,
		lean_object *value1, lean_object *trig2, uint8_t trig2_pol, lean_object *value2);
lean_object *grounding_builder_make_unop(uint8_t op, lean_object *a);
lean_object *grounding_builder_make_biop(uint8_t op, lean_object *a, lean_object *b);
lean_object *grounding_builder_make_shift(
		uint8_t op, lean_object *stride, lean_object *a, lean_object *s);
lean_object *grounding_builder_make_shiftx(lean_object *stride, lean_object *a, lean_object *s);
lean_object *grounding_builder_make_replicate(lean_object *width, lean_object *bit);
lean_object *grounding_builder_make_mux(lean_object *sel, lean_object *a, lean_object *b);
lean_object *grounding_builder_finish(lean_object *builder);
}

// Constructor indices of `Grounding.Rtl.Unop`.
enum class LeanUnop : uint8_t {
	Pos,
	Not,
	Minus,
	LogicNot,
	ReduceAnd,
	ReduceOr,
	ReduceXor,
};

// Constructor indices of `Grounding.Rtl.Biop`.
enum class LeanBiop : uint8_t {
	And,
	Or,
	Xor,
	Xnor,
	Add,
	Sub,
	Mul,
	Eq,
	Ne,
	Eqx,
	Nex,
	Ult,
	Ule,
	Ugt,
	Uge,
	Slt,
	Sle,
	Sgt,
	Sge,
};

// Constructor indices of `Grounding.Rtl.Shiftop`.
enum class LeanShiftop : uint8_t {
	Shl,
	Ushr,
	Sshr,
};
