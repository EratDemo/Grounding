// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <cstdint>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "ir.h"
#include "slang_frontend.h"

// Re-export the trit constants into `ir` for convenience.
namespace ir {
using slang_frontend::S0;
using slang_frontend::S1;
using slang_frontend::Sx;
using slang_frontend::Trit;
} // namespace ir

struct LeanNetlistBuilder;
enum class LeanUnop : uint8_t;
enum class LeanBiop : uint8_t;

namespace slang_frontend {

struct BackendGraphBuilder : public BackendGraphBuilderBase
{
public:
	uint32_t next_name_id = 0;
	std::unique_ptr<LeanNetlistBuilder> inner;

	BackendGraphBuilder();
	~BackendGraphBuilder();

	std::string new_id(const std::string &base = std::string());
	std::unique_ptr<BackendGraphBuilder> start_new_graph(std::string_view graph_name);
	void finalize();
	void *take_netlist();
	void for_each_lean_ref(void *ctx, void (*fn)(void *, void *));
	void *realize_value(const ir::Value &value);

	ir::Value Unop(ast::UnaryOperator op, ir::Value a, bool a_signed, uint64_t y_width) override;
	ir::Value Biop(ast::BinaryOperator op, ir::Value a, ir::Value b, bool a_signed, bool b_signed,
			uint64_t y_width) override;
	ir::Value Demux(ir::Value a, ir::Value s) override;
	ir::Value Bwmux(ir::Value a, ir::Value b, ir::Value s) override;
	ir::Value Bmux(ir::Value a, ir::Value s) override;
	ir::Value Shift(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width) override;
	ir::Value Shiftx(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width) override;
	ir::Value Mux(ir::Value a, ir::Value b, ir::Net s) override;
	ir::Value add_placeholder_signal(
			uint64_t width, std::string_view name_suggestion, bool public_name) override;
	void add_input(std::string_view name, ir::Value signal) override;
	void add_output(std::string_view name, ir::Value signal) override;
	void add_instance(std::string_view cell_type, std::vector<PortConnection> ports) override;
	void instantiate_blackbox(std::string_view cell_type, std::string_view name,
			std::span<PortConnection> port_connections,
			std::span<ParameterValue> param_values) override;
	void connect(ir::Value target, ir::Value source) override;
	void set_initialization(ir::Value signal, TritVector init_value) override;
	ir::Memory *add_memory(
			std::string_view name, uint64_t width, slang::ConstantRange range) override;
	void add_read_port(ir::Memory *memory, ir::Value address, ir::Value data) override;
	ir::WritePort *add_write_port(ir::Memory *memory, std::span<ir::WritePort *> preceding,
			bool clocked, bool clock_polarity, ir::Net clk, const ir::Value &enable,
			const ir::Value &address, const ir::Value &data) override;
	void add_memory_init(
			ir::Memory *memory, uint64_t bit_offset, bool big_endian, TritVector data) override;
	void add_dual_edge_aldff(const std::string &base_name, ir::Net clk, ir::Net aload,
			const ir::Value &d, const ir::Value &q, const ir::Value &ad,
			bool aload_polarity) override;
	void add_dff(std::string_view name, const ir::Net clk, const ir::Value &d, const ir::Value &q,
			bool clk_polarity) override;
	void add_dffe(std::string_view name, const ir::Net clk, const ir::Net en, const ir::Value &d,
			const ir::Value &q, bool clk_polarity, bool en_polarity) override;
	void add_aldff(std::string_view name, const ir::Net clk, const ir::Net aload,
			const ir::Value &d, const ir::Value &q, const ir::Value &ad, bool clk_polarity,
			bool aload_polarity) override;
	void add_aldffe(std::string_view name, const ir::Net clk, const ir::Net en, const ir::Net aload,
			const ir::Value &d, const ir::Value &q, const ir::Value &ad, bool clk_polarity,
			bool en_polarity, bool aload_polarity) override;
	void add_dffsre(std::string_view name, const ir::Net clk, const ir::Net en, const ir::Net set,
			const ir::Net clear, const ir::Value &d, const ir::Value &q, bool clk_polarity,
			bool set_polarity, bool clear_polarity, bool set_over_clear) override;

private:
	// One-bit unary result (logic-not / reductions), zero-extended.
	ir::Value bool1(LeanUnop op, const ir::Value &a, uint64_t y_width);
	ir::Value notBit(const ir::Value &bit, uint64_t y_width);
	// Comparison on operands resized to a common width, zero-extended result.
	ir::Value cmp(LeanBiop op, const ir::Value &a, const ir::Value &b, bool a_signed, bool b_signed,
			uint64_t y_width);
	ir::Value reduceOr(const ir::Value &a);
	ir::Value enabled(ir::Net en, bool en_polarity, const ir::Value &d, const ir::Value &q);
	ir::Value shiftImpl(
			ir::Value a, ir::Value s, bool s_signed, uint64_t result_width, bool fill_x);
};

// No-op attribute guard: the flat netlist does not retain HDL attributes or
// source locations.
class AttributeGuard
{
public:
	AttributeGuard(GraphBuilder &) {}

	template <typename... Args> void set(Args &&...) {}
};

} // namespace slang_frontend
