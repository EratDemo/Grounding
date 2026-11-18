// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <string>
#include <vector>

#include "ir.h"

namespace grounding {

// Native elaboration state kept alive so expressions can be evaluated in the
// scope of the elaborated top module. Owned by the returned handle.
struct SvState;

struct ReadResult
{
	// Owned Lean `Netlist` object (an opaque pointer).
	void *netlist = nullptr;
	// Heap-allocated state; ownership transfers to the caller.
	SvState *state = nullptr;
};

// Evaluate SystemVerilog expression `text` in the scope of the elaborated top
// module. Returns the expression's flat IR value; no signals or assignments
// are added to the netlist. Throws std::runtime_error on failure.
ir::Value eval_expression(SvState &state, const std::string &text);

// Parse and elaborate a SystemVerilog source string into the Lean RTL netlist,
// keeping the native compilation state for later expression evaluation.
// Throws std::runtime_error on failure.
ReadResult read_sv(const std::string &source, std::vector<std::string> args);

} // namespace grounding
