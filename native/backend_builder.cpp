// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#include "backend_builder.h"
#include "lean_defs.h"

#include <lean/lean.h>

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

// An owned Lean reference, released on scope exit unless `release`d.
class Owned
{
	lean_object *obj_ = nullptr;

public:
	Owned() = default;
	explicit Owned(lean_object *obj) : obj_(obj) {}
	Owned(const Owned &) = delete;
	Owned &operator=(const Owned &) = delete;
	Owned(Owned &&o) noexcept : obj_(std::exchange(o.obj_, nullptr)) {}
	Owned &operator=(Owned &&o) noexcept
	{
		std::swap(obj_, o.obj_);
		return *this;
	}
	~Owned()
	{
		if (obj_ != nullptr) {
			lean_dec(obj_);
		}
	}
	lean_object *get() const { return obj_; }
	lean_object *release() { return std::exchange(obj_, nullptr); }
};

lean_object *mk_nat(uint64_t value)
{
	return lean_uint64_to_nat(value);
}

lean_object *mk_string(std::string_view s)
{
	return lean_mk_string_from_bytes(s.data(), s.size());
}

// Extract the payload of an owned `Option`. Returns nullptr for `none`.
lean_object *take_option(lean_object *option)
{
	if (lean_is_scalar(option)) {
		return nullptr;
	}
	lean_object *value = lean_ctor_get(option, 0);
	lean_inc(value);
	lean_dec(option);
	return value;
}

uint8_t trit_code(const ir::Net &net)
{
	return net.id_ == ir::Net::kZero ? 0 : (net.id_ == ir::Net::kOne ? 1 : 2);
}

}; // namespace

struct LeanNetlistBuilder
{
	LeanNetlistBuilder() : builder(grounding_builder_new(lean_box(0))) {}
	LeanNetlistBuilder(const LeanNetlistBuilder &) = delete;
	LeanNetlistBuilder &operator=(const LeanNetlistBuilder &) = delete;
	LeanNetlistBuilder(LeanNetlistBuilder &&) = delete;
	LeanNetlistBuilder &operator=(LeanNetlistBuilder &&) = delete;
	~LeanNetlistBuilder()
	{
		for (auto &entry : net_refs) {
			lean_dec(entry.second.value);
		}
		if (builder != nullptr) {
			lean_dec(builder);
		}
		if (netlist != nullptr) {
			lean_dec(netlist);
		}
	}

	uint32_t next_id = ir::Net::kFirstWire;
	lean_object *builder = nullptr;
	lean_object *netlist = nullptr;

	struct NetRef
	{
		lean_object *value; // BuiltValue for this net (one owned reference per net)
		uint32_t bit;       // bit index within `value`
	};

	std::unordered_map<uint32_t, NetRef> net_refs;

	// The constant nets [i, j) of `value` as one Lean constant (LSB first). A run
	// of one repeated trit uses the compact `const(width, trit)` form.
	static lean_object *const_run(const ir::Value &value, size_t i, size_t j)
	{
		bool uniform = true;
		for (size_t k = i + 1; k < j && uniform; ++k) {
			uniform = value.nets_[k] == value.nets_[i];
		}
		if (uniform) {
			return grounding_builder_const(mk_nat(j - i), trit_code(value.nets_[i]));
		}
		lean_object *codes = lean_alloc_sarray(1, j - i, j - i);
		uint8_t *data = lean_sarray_cptr(codes);
		for (size_t k = i; k < j; ++k) {
			data[k - i] = trit_code(value.nets_[k]);
		}
		return grounding_builder_const_bits(codes);
	}

	void finalize()
	{
		if (netlist == nullptr && builder != nullptr) {
			netlist = grounding_builder_finish(std::exchange(builder, nullptr));
		}
	}

	lean_object *realize_value(const ir::Value &value)
	{
		std::vector<Owned> parts; // LSB-first runs
		const size_t n = value.nets_.size();
		size_t i = 0;
		while (i < n) {
			const ir::Net net = value.nets_[i];
			size_t j = i + 1;
			if (net.is_const()) {
				// One constant per maximal run of constant nets (any trits).
				while (j < n && value.nets_[j].is_const()) {
					j++;
				}
				parts.emplace_back(const_run(value, i, j));
			} else {
				auto it = net_refs.find(net.id_);
				if (it == net_refs.end()) {
					throw std::runtime_error("grounding: cannot realize net value");
				}
				const NetRef ref = it->second;
				// A run of the same one-bit net is one `replicate`.
				while (j < n && value.nets_[j] == net) {
					j++;
				}
				if (j - i > 1) {
					lean_inc(ref.value);
					lean_object *bit = take_option(
							grounding_builder_part_select(ref.value, mk_nat(ref.bit), mk_nat(1)));
					if (bit == nullptr) {
						throw std::runtime_error("grounding: cannot realize net value");
					}
					lean_object *rep =
							take_option(grounding_builder_make_replicate(mk_nat(j - i), bit));
					if (rep == nullptr) {
						throw std::runtime_error("grounding: cannot realize net value");
					}
					parts.emplace_back(rep);
				} else {
					j = i + 1;
					while (j < n && !value.nets_[j].is_const()) {
						auto jt = net_refs.find(value.nets_[j].id_);
						if (jt == net_refs.end() || jt->second.value != ref.value ||
								jt->second.bit != ref.bit + (j - i)) {
							break;
						}
						j++;
					}
					lean_inc(ref.value);
					lean_object *sel = take_option(grounding_builder_part_select(
							ref.value, mk_nat(ref.bit), mk_nat(j - i)));
					if (sel == nullptr) {
						throw std::runtime_error("grounding: cannot realize net value");
					}
					parts.emplace_back(sel);
				}
			}
			i = j;
		}
		if (parts.size() == 1) {
			return parts.front().release();
		}
		// Lean concatenation is MSB-first.
		lean_object *array = lean_alloc_array(parts.size(), parts.size());
		for (size_t k = 0; k < parts.size(); ++k) {
			lean_array_set_core(array, k, parts[parts.size() - 1 - k].release());
		}
		return grounding_builder_concat(array);
	}

	ir::Value new_nets(uint64_t width)
	{
		if (width > UINT32_MAX - next_id) {
			throw std::runtime_error("grounding: too many nets");
		}
		ir::Value v;
		v.reserve(width);
		for (uint64_t i = 0; i < width; i++) {
			v.append(ir::Net(next_id++));
		}
		return v;
	}

	void bind_net(uint32_t net, lean_object *value, uint32_t bit)
	{
		auto [it, inserted] = net_refs.try_emplace(net, NetRef{value, bit});
		if (!inserted) {
			throw std::runtime_error("grounding: net bound twice");
		}
		lean_inc(value);
	}

	// Bind the nets of `target` to the bits of `value` (a BuiltValue of width
	// target.size()). Consumes the owned reference in `value`.
	void bind(const ir::Value &target, lean_object *value)
	{
		Owned owned(value);
		const auto width = static_cast<uint32_t>(target.nets_.size());
		for (uint32_t bit = 0; bit < width; ++bit) {
			bind_net(target.nets_[bit].id_, owned.get(), bit);
		}
	}

	// Replace the builder by the result of a builder update, or throw.
	void update(lean_object *result, const char *what)
	{
		builder = take_option(result);
		if (builder == nullptr) {
			throw std::runtime_error(what);
		}
	}

	// Builder mutations are invalid once the Lean `Netlist` has been finalized.
	void ensure_live() const
	{
		if (builder == nullptr) {
			throw std::runtime_error("grounding: cannot modify the builder after finalization");
		}
	}

	void add_signal(const ir::Value &signal, std::string_view name)
	{
		ensure_live();
		const auto width = static_cast<uint32_t>(signal.size());
		lean_object *result = grounding_builder_add_signal(
				std::exchange(builder, nullptr), mk_nat(width), mk_string(name));
		lean_object *next_builder = lean_ctor_get(result, 0);
		lean_object *signal_value = lean_ctor_get(result, 1);
		lean_inc(next_builder);
		lean_inc(signal_value);
		lean_dec(result);
		builder = next_builder;
		bind(signal, signal_value);
	}

	void add_port(std::string_view name, bool input, const ir::Value &value)
	{
		ensure_live();
		Owned v(realize_value(value));
		update(grounding_builder_add_port(std::exchange(builder, nullptr), mk_string(name),
					   input ? 0 : 1, v.release()),
				input ? "grounding: cannot add input port (value is not assignable)"
					  : "grounding: cannot add output port");
	}

	void add_assignment(const ir::Value &target, const ir::Value &source)
	{
		ensure_live();
		Owned t(realize_value(target));
		Owned s(realize_value(source));
		update(grounding_builder_add_assignment(
					   std::exchange(builder, nullptr), t.release(), s.release()),
				"grounding: cannot add assignment (target is not assignable or "
				"widths differ)");
	}

	void add_register(const ir::Value &q, const ir::Value &d, const ir::Value &clk, bool clk_rising)
	{
		ensure_live();
		Owned qv(realize_value(q));
		Owned dv(realize_value(d));
		Owned cv(realize_value(clk));
		update(grounding_builder_add_register(std::exchange(builder, nullptr), qv.release(),
					   dv.release(), cv.release(), clk_rising ? 1 : 0),
				"grounding: cannot add register (q is not assignable, the clock "
				"is not one bit, or widths differ)");
	}

	void add_aload_register(const ir::Value &q, const ir::Value &d, const ir::Value &clk,
			bool clk_rising, const ir::Value &trig, bool trig_pol, const ir::Value &value)
	{
		ensure_live();
		Owned qv(realize_value(q));
		Owned dv(realize_value(d));
		Owned cv(realize_value(clk));
		Owned tv(realize_value(trig));
		Owned vv(realize_value(value));
		update(grounding_builder_add_aload_register(std::exchange(builder, nullptr), qv.release(),
					   dv.release(), cv.release(), clk_rising ? 1 : 0, tv.release(),
					   trig_pol ? 1 : 0, vv.release()),
				"grounding: cannot add register (q is not assignable, the clock "
				"or load trigger is not one bit, or widths differ)");
	}

	void add_aload2_register(const ir::Value &q, const ir::Value &d, const ir::Value &clk,
			bool clk_rising, const ir::Value &trig1, bool trig1_pol, const ir::Value &value1,
			const ir::Value &trig2, bool trig2_pol, const ir::Value &value2)
	{
		ensure_live();
		Owned qv(realize_value(q));
		Owned dv(realize_value(d));
		Owned cv(realize_value(clk));
		Owned t1(realize_value(trig1));
		Owned v1(realize_value(value1));
		Owned t2(realize_value(trig2));
		Owned v2(realize_value(value2));
		update(grounding_builder_add_aload2_register(std::exchange(builder, nullptr), qv.release(),
					   dv.release(), cv.release(), clk_rising ? 1 : 0, t1.release(),
					   trig1_pol ? 1 : 0, v1.release(), t2.release(), trig2_pol ? 1 : 0,
					   v2.release()),
				"grounding: cannot add register (q is not assignable, the clock "
				"or a load trigger is not one bit, or widths differ)");
	}

	void unop(LeanUnop op, const ir::Value &target, const ir::Value &a)
	{
		bind(target, grounding_builder_make_unop(static_cast<uint8_t>(op), realize_value(a)));
	}

	void biop(LeanBiop op, const ir::Value &target, const ir::Value &a, const ir::Value &b)
	{
		Owned av(realize_value(a));
		Owned bv(realize_value(b));
		lean_object *res = take_option(
				grounding_builder_make_biop(static_cast<uint8_t>(op), av.release(), bv.release()));
		if (res == nullptr) {
			throw std::runtime_error("grounding: biop operand widths differ");
		}
		bind(target, res);
	}

	void shift(LeanShiftop op, const ir::Value &target, const ir::Value &a, const ir::Value &s,
			uint64_t stride = 1)
	{
		Owned av(realize_value(a));
		Owned sv(realize_value(s));
		bind(target, grounding_builder_make_shift(
							 static_cast<uint8_t>(op), mk_nat(stride), av.release(), sv.release()));
	}

	void shiftx(
			const ir::Value &target, const ir::Value &a, const ir::Value &s, uint64_t stride = 1)
	{
		Owned av(realize_value(a));
		Owned sv(realize_value(s));
		bind(target, grounding_builder_make_shiftx(mk_nat(stride), av.release(), sv.release()));
	}

	void replicate(const ir::Value &target, const ir::Value &bit)
	{
		Owned bv(realize_value(bit));
		lean_object *res =
				take_option(grounding_builder_make_replicate(mk_nat(target.size()), bv.release()));
		if (res == nullptr) {
			throw std::runtime_error("grounding: replicate operand is not one bit");
		}
		bind(target, res);
	}

	void mux(const ir::Value &target, const ir::Value &sel, const ir::Value &a, const ir::Value &b)
	{
		Owned sv(realize_value(sel));
		Owned av(realize_value(a));
		Owned bv(realize_value(b));
		lean_object *res =
				take_option(grounding_builder_make_mux(sv.release(), av.release(), bv.release()));
		if (res == nullptr) {
			throw std::runtime_error(
					"grounding: invalid mux (selector is not one bit or operand widths "
					"differ)");
		}
		bind(target, res);
	}

	void *take_netlist()
	{
		finalize();
		return std::exchange(netlist, nullptr);
	}

	void for_each_lean_ref(void *ctx, void (*fn)(void *, void *)) const
	{
		// `builder` and `netlist` are normally null here (the builder is consumed
		// by `finalize` and the netlist is handed to Lean by `take_netlist`), but
		// mark them too so the hook stays correct if it is called earlier.
		if (builder != nullptr) {
			fn(ctx, builder);
		}
		if (netlist != nullptr) {
			fn(ctx, netlist);
		}
		for (const auto &entry : net_refs) {
			fn(ctx, entry.second.value);
		}
	}
};

namespace slang_frontend {

std::unique_ptr<BackendGraphBuilder> BackendGraphBuilder::start_new_graph(std::string_view)
{
	throw std::runtime_error("hierarchical netlists are not supported yet");
}

BackendGraphBuilder::BackendGraphBuilder() : inner(std::make_unique<LeanNetlistBuilder>())
{}

// `inner` is a `unique_ptr`, so this destroys the `LeanNetlistBuilder` and
// releases every Lean reference it owns.
BackendGraphBuilder::~BackendGraphBuilder() = default;

std::string BackendGraphBuilder::new_id(const std::string &base)
{
	return base + std::to_string(next_name_id++);
}

void BackendGraphBuilder::finalize()
{
	inner->finalize();
}

void *BackendGraphBuilder::take_netlist()
{
	return inner->take_netlist();
}

void BackendGraphBuilder::for_each_lean_ref(void *ctx, void (*fn)(void *, void *))
{
	inner->for_each_lean_ref(ctx, fn);
}

void *BackendGraphBuilder::realize_value(const ir::Value &value)
{
	return inner->realize_value(value);
}

ir::Value BackendGraphBuilder::bool1(LeanUnop op, const ir::Value &a, uint64_t y_width)
{
	ir::Value y = inner->new_nets(1);
	inner->unop(op, y, a);
	return y.extend(y_width);
}

ir::Value BackendGraphBuilder::notBit(const ir::Value &bit, uint64_t y_width)
{
	ir::Value y = inner->new_nets(1);
	inner->unop(LeanUnop::Not, y, bit);
	return y.extend(y_width);
}

ir::Value BackendGraphBuilder::Unop(
		ast::UnaryOperator op, ir::Value a, bool a_signed, uint64_t y_width)
{
	if (y_width == 0) {
		return {};
	}

	using U = ast::UnaryOperator;
	switch (op) {
	case U::Plus:
	case U::BitwiseNot:
	case U::Minus:      {
		ir::Value ea = a.extend(y_width, a_signed);
		ir::Value y = inner->new_nets(y_width);
		inner->unop(op == U::Plus         ? LeanUnop::Pos
					: op == U::BitwiseNot ? LeanUnop::Not
										  : LeanUnop::Minus,
				y, ea);
		return y;
	}
	case U::LogicalNot:  return bool1(LeanUnop::LogicNot, a, y_width);
	case U::BitwiseAnd:  return bool1(LeanUnop::ReduceAnd, a, y_width);
	case U::BitwiseOr:   return bool1(LeanUnop::ReduceOr, a, y_width);
	case U::BitwiseXor:  return bool1(LeanUnop::ReduceXor, a, y_width);
	case U::BitwiseNand: return notBit(bool1(LeanUnop::ReduceAnd, a, 1), y_width);
	case U::BitwiseNor:  return notBit(bool1(LeanUnop::ReduceOr, a, 1), y_width);
	case U::BitwiseXnor: return notBit(bool1(LeanUnop::ReduceXor, a, 1), y_width);
	default:
		throw std::runtime_error(
				"grounding: unsupported unop '" + std::string(slang::ast::toString(op)) + "'");
	}
}

ir::Value BackendGraphBuilder::cmp(LeanBiop op, const ir::Value &a, const ir::Value &b,
		bool a_signed, bool b_signed, uint64_t y_width)
{
	const uint64_t w = std::max(a.size(), b.size());
	ir::Value y = inner->new_nets(1);
	inner->biop(op, y, a.extend(w, a_signed), b.extend(w, b_signed));
	return y.extend(y_width);
}

ir::Value BackendGraphBuilder::reduceOr(const ir::Value &a)
{
	if (a.size() == 1) {
		return a;
	}
	ir::Value y = inner->new_nets(1);
	inner->unop(LeanUnop::ReduceOr, y, a);
	return y;
}

ir::Value BackendGraphBuilder::Biop(ast::BinaryOperator op, ir::Value a, ir::Value b, bool a_signed,
		bool b_signed, uint64_t y_width)
{
	if (y_width == 0) {
		return {};
	}

	using B = ast::BinaryOperator;
	const bool is_signed = a_signed && b_signed;
	auto arith = [&](LeanBiop lop) {
		ir::Value y = inner->new_nets(y_width);
		inner->biop(lop, y, a.extend(y_width, a_signed), b.extend(y_width, b_signed));
		return y;
	};
	auto logic = [&](LeanBiop lop, bool invert_a) {
		ir::Value ra = reduceOr(a);
		if (invert_a) {
			ir::Value na = inner->new_nets(1);
			inner->unop(LeanUnop::Not, na, ra);
			ra = na;
		}
		ir::Value y = inner->new_nets(1);
		inner->biop(lop, y, ra, reduceOr(b));
		return y.extend(y_width);
	};
	switch (op) {
	case B::Add:            return arith(LeanBiop::Add);
	case B::Subtract:       return arith(LeanBiop::Sub);
	case B::Multiply:       return arith(LeanBiop::Mul);
	case B::BinaryAnd:      return arith(LeanBiop::And);
	case B::BinaryOr:       return arith(LeanBiop::Or);
	case B::BinaryXor:      return arith(LeanBiop::Xor);
	case B::BinaryXnor:     return arith(LeanBiop::Xnor);
	case B::Equality:       return cmp(LeanBiop::Eq, a, b, a_signed, b_signed, y_width);
	case B::Inequality:     return cmp(LeanBiop::Ne, a, b, a_signed, b_signed, y_width);
	case B::CaseEquality:   return cmp(LeanBiop::Eqx, a, b, a_signed, b_signed, y_width);
	case B::CaseInequality: return cmp(LeanBiop::Nex, a, b, a_signed, b_signed, y_width);
	case B::LessThan:
		return cmp(is_signed ? LeanBiop::Slt : LeanBiop::Ult, a, b, a_signed, b_signed, y_width);
	case B::LessThanEqual:
		return cmp(is_signed ? LeanBiop::Sle : LeanBiop::Ule, a, b, a_signed, b_signed, y_width);
	case B::GreaterThan:
		return cmp(is_signed ? LeanBiop::Sgt : LeanBiop::Ugt, a, b, a_signed, b_signed, y_width);
	case B::GreaterThanEqual:
		return cmp(is_signed ? LeanBiop::Sge : LeanBiop::Uge, a, b, a_signed, b_signed, y_width);
	case B::LogicalAnd:           return logic(LeanBiop::And, false);
	case B::LogicalOr:            return logic(LeanBiop::Or, false);
	case B::LogicalImplication:   return logic(LeanBiop::Or, true);
	case B::LogicalEquivalence:   return logic(LeanBiop::Xnor, false);
	case B::LogicalShiftLeft:
	case B::ArithmeticShiftLeft:
	case B::LogicalShiftRight:
	case B::ArithmeticShiftRight: {
		const LeanShiftop sop = (op == B::LogicalShiftLeft || op == B::ArithmeticShiftLeft)
										? LeanShiftop::Shl
								: (op == B::ArithmeticShiftRight && a_signed) ? LeanShiftop::Sshr
																			  : LeanShiftop::Ushr;
		ir::Value y = inner->new_nets(y_width);
		inner->shift(sop, y, a.extend(y_width, a_signed), b);
		return y;
	}
	default:
		throw std::runtime_error(
				"grounding: unsupported biop '" + std::string(slang::ast::toString(op)) + "'");
	}
}

ir::Value BackendGraphBuilder::Demux(ir::Value a, ir::Value s)
{
	const uint64_t out_width = a.size() << s.size();
	ir::Value y = inner->new_nets(out_width);
	inner->shift(LeanShiftop::Shl, y, a.extend(out_width), s, a.size());
	return y;
}

// One mux per run of equal select bits (sv-elab convention: s ? b : a).
ir::Value BackendGraphBuilder::Bwmux(ir::Value a, ir::Value b, ir::Value s)
{
	ir::Value result;
	result.reserve(a.size());
	for (uint64_t base = 0; base < a.size();) {
		uint64_t width = 1;
		while (base + width < s.size() && s[base + width] == s[base]) {
			width++;
		}
		result.append(Mux(a.extract(base, width), b.extract(base, width), s[base]));
		base += width;
	}
	return result;
}

// Select the `width`-bit slice of `a` at offset `s * width`.
ir::Value BackendGraphBuilder::Bmux(ir::Value a, ir::Value s)
{
	assert(a.size() % (uint64_t{1} << s.size()) == 0);
	const uint64_t width = a.size() >> s.size();
	// A one-bit selector (e.g. the clock enable of `if (en) q <= d`) is a plain
	// two-way mux, not a strided shift.
	if (s.size() == 1)
		return Mux(a.extract(0, width), a.extract(width, width), s[0]);
	ir::Value y = inner->new_nets(a.size());
	inner->shift(LeanShiftop::Ushr, y, a, s, width);
	return y.extract(0, width);
}

// `Shift`/`Shiftx`: result[j] = a[s + j] for j < result_width, where
// out-of-range bits are 0 (Shift) or X (Shiftx). A signed `s` may be negative,
// which shifts left.
ir::Value BackendGraphBuilder::shiftImpl(
		ir::Value a, ir::Value s, bool s_signed, uint64_t result_width, bool fill_x)
{
	const ir::Trit fill = fill_x ? ir::Sx : ir::S0;
	const uint64_t w = std::max<uint64_t>(a.size(), result_width);
	ir::Value pa = a;
	pa.append(ir::Value(fill, w - a.size()));

	auto right = [&](const ir::Value &amount) {
		ir::Value y = inner->new_nets(w);
		if (fill_x) {
			inner->shiftx(y, pa, amount);
		} else {
			inner->shift(LeanShiftop::Ushr, y, pa, amount);
		}
		return y;
	};

	ir::Value shifted;
	if (!s_signed || s.empty()) {
		shifted = right(s);
	} else {
		// Negative amounts shift left by -s, filling the low bits.
		const ir::Net sign = s[s.size() - 1];
		ir::Value r = right(s);
		ir::Value neg = inner->new_nets(s.size());
		inner->unop(LeanUnop::Minus, neg, s);
		ir::Value l = inner->new_nets(w);
		inner->shift(LeanShiftop::Shl, l, pa, neg);
		if (fill_x) {
			// Bits shifted in at the bottom are X: or in X where a zero-filled
			// left shift of all-ones is 0.
			ir::Value mask = inner->new_nets(w);
			inner->shift(LeanShiftop::Shl, mask, ir::Value(ir::S1, w), neg);
			ir::Value inv = inner->new_nets(w);
			inner->unop(LeanUnop::Not, inv, mask);
			ir::Value xs = inner->new_nets(w);
			inner->biop(LeanBiop::And, xs, inv, ir::Value(ir::Sx, w));
			ir::Value lx = inner->new_nets(w);
			inner->biop(LeanBiop::Or, lx, l, xs);
			l = lx;
		}
		shifted = inner->new_nets(w);
		inner->mux(shifted, ir::Value(sign), l, r);
	}
	return shifted.extract(0, result_width);
}

ir::Value BackendGraphBuilder::Shift(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width)
{
	return shiftImpl(std::move(a), std::move(s), s_signed, result_width, false);
}

ir::Value BackendGraphBuilder::Shiftx(
		ir::Value a, ir::Value s, bool s_signed, uint64_t result_width)
{
	return shiftImpl(std::move(a), std::move(s), s_signed, result_width, true);
}

// sv-elab convention: `Mux(a, b, s)` is `s ? b : a`.
ir::Value BackendGraphBuilder::Mux(ir::Value a, ir::Value b, ir::Net s)
{
	ir::Value y = inner->new_nets(a.size());
	inner->mux(y, ir::Value(s), b, a);
	return y;
}

ir::Value BackendGraphBuilder::add_placeholder_signal(
		uint64_t width, std::string_view name_suggestion, bool public_name)
{
	ir::Value v = inner->new_nets(width);
	inner->add_signal(v, public_name ? name_suggestion : std::string_view{});
	return v;
}

void BackendGraphBuilder::add_input(std::string_view name, ir::Value signal)
{
	inner->add_port(name, true, signal);
}

void BackendGraphBuilder::add_output(std::string_view name, ir::Value signal)
{
	inner->add_port(name, false, signal);
}

void BackendGraphBuilder::add_instance(std::string_view, std::vector<PortConnection>)
{
	throw std::runtime_error("hierarchical (non-dissolved) module instantiation is not supported");
}

void BackendGraphBuilder::instantiate_blackbox(std::string_view cell_type, std::string_view,
		std::span<PortConnection>, std::span<ParameterValue>)
{
	throw std::runtime_error(
			"grounding: blackbox '" + std::string(cell_type) + "' is not supported yet");
}

void BackendGraphBuilder::connect(ir::Value target, ir::Value source)
{
	assert(target.size() == source.size());
	if (target.empty()) {
		return;
	}
	inner->add_assignment(target, source);
}

void BackendGraphBuilder::set_initialization(ir::Value, TritVector init_value)
{
	if (init_value.is_fully_undef()) {
		return;
	}
	throw std::runtime_error("grounding: non-X variable initialization is not supported yet");
}

ir::Memory *BackendGraphBuilder::add_memory(std::string_view, uint64_t, slang::ConstantRange)
{
	throw std::runtime_error("memories are not supported yet");
}

void BackendGraphBuilder::add_read_port(ir::Memory *, ir::Value, ir::Value)
{
	throw std::runtime_error("memories are not supported yet");
}

ir::WritePort *BackendGraphBuilder::add_write_port(ir::Memory *, std::span<ir::WritePort *>, bool,
		bool, ir::Net, const ir::Value &, const ir::Value &, const ir::Value &)
{
	throw std::runtime_error("memories are not supported yet");
}

void BackendGraphBuilder::add_memory_init(ir::Memory *, uint64_t, bool, TritVector)
{
	throw std::runtime_error("memories are not supported yet");
}

void BackendGraphBuilder::add_dual_edge_aldff(const std::string &, ir::Net, ir::Net,
		const ir::Value &, const ir::Value &, const ir::Value &, bool)
{
	throw std::runtime_error("dual-edge flops are not supported");
}

void BackendGraphBuilder::add_dff(std::string_view, const ir::Net clk, const ir::Value &d,
		const ir::Value &q, bool clk_polarity)
{
	inner->add_register(q, d, ir::Value(clk), clk_polarity);
}

// The next value with a clock enable folded in: `en ? d : q` (for the enable's
// active level).
ir::Value BackendGraphBuilder::enabled(
		ir::Net en, bool en_polarity, const ir::Value &d, const ir::Value &q)
{
	ir::Value y = inner->new_nets(d.size());
	if (en_polarity) {
		inner->mux(y, ir::Value(en), d, q);
	} else {
		inner->mux(y, ir::Value(en), q, d);
	}
	return y;
}

void BackendGraphBuilder::add_dffe(std::string_view, const ir::Net clk, const ir::Net en,
		const ir::Value &d, const ir::Value &q, bool clk_polarity, bool en_polarity)
{
	inner->add_register(q, enabled(en, en_polarity, d, q), ir::Value(clk), clk_polarity);
}

void BackendGraphBuilder::add_aldff(std::string_view, const ir::Net clk, const ir::Net aload,
		const ir::Value &d, const ir::Value &q, const ir::Value &ad, bool clk_polarity,
		bool aload_polarity)
{
	inner->add_aload_register(
			q, d, ir::Value(clk), clk_polarity, ir::Value(aload), aload_polarity, ad);
}

void BackendGraphBuilder::add_aldffe(std::string_view, const ir::Net clk, const ir::Net en,
		const ir::Net aload, const ir::Value &d, const ir::Value &q, const ir::Value &ad,
		bool clk_polarity, bool en_polarity, bool aload_polarity)
{
	inner->add_aload_register(q, enabled(en, en_polarity, d, q), ir::Value(clk), clk_polarity,
			ir::Value(aload), aload_polarity, ad);
}

void BackendGraphBuilder::add_dffsre(std::string_view, const ir::Net clk, const ir::Net en,
		const ir::Net set, const ir::Net clear, const ir::Value &d, const ir::Value &q,
		bool clk_polarity, bool set_polarity, bool clear_polarity, bool set_over_clear)
{
	// The register's asynchronous loads are priority-ordered (the first active
	// load wins), so precedence is expressed by the order rather than by gating
	// the lower-priority control.
	ir::Value set_value = ir::Value(ir::S1, d.size());
	ir::Value clear_value = ir::Value(ir::S0, d.size());
	ir::Value next = enabled(en, /*en_polarity=*/true, d, q);
	if (set_over_clear) {
		inner->add_aload2_register(q, next, ir::Value(clk), clk_polarity, ir::Value(set),
				set_polarity, set_value, ir::Value(clear), clear_polarity, clear_value);
	} else {
		inner->add_aload2_register(q, next, ir::Value(clk), clk_polarity, ir::Value(clear),
				clear_polarity, clear_value, ir::Value(set), set_polarity, set_value);
	}
}

void transfer_attrs(NetlistContext &, const ast::Symbol &, AttributeGuard &)
{}

void transfer_attrs(NetlistContext &, const ast::Statement &, AttributeGuard &)
{}

void transfer_attrs(NetlistContext &, const ast::Expression &, AttributeGuard &)
{}

} // namespace slang_frontend
