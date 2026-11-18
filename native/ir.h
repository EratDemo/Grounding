// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <iterator>
#include <vector>

namespace slang_frontend {
// The frontend's constant representation (defined in slang_frontend.h).
// Declared here so that the IR below can convert to and from it.
enum Trit : uint8_t;
class TritVector;
} // namespace slang_frontend

namespace ir {

struct Value;

struct Net
{
	static constexpr uint32_t kZero = 0;
	static constexpr uint32_t kOne = 1;
	static constexpr uint32_t kUndef = 2;
	static constexpr uint32_t kFirstWire = 3;

	uint32_t id_;

	constexpr Net() : id_(kUndef) {}
	explicit constexpr Net(uint32_t id) : id_(id) {}
	Net(slang_frontend::Trit t);

	static constexpr Net zero() { return Net(kZero); }
	static constexpr Net one() { return Net(kOne); }
	static constexpr Net undef() { return Net(kUndef); }

	Net raw() const { return *this; }
	Value repeat(uint64_t width);

	// The frontend's representation of this bit's constant value.
	slang_frontend::Trit as_trit() const;

	bool operator==(Net o) const { return id_ == o.id_; }
	bool operator!=(Net o) const { return id_ != o.id_; }
	bool operator==(slang_frontend::Trit t) const { return id_ == Net(t).id_; }
	bool operator!=(slang_frontend::Trit t) const { return id_ != Net(t).id_; }

	bool is_const() const { return id_ < kFirstWire; }
	bool is_def() const { return id_ == kZero || id_ == kOne; }
};

// Proxy returned by Value::operator[] for read and write access.
class NetProxy
{
	std::vector<Net> &nets_;
	size_t idx_;

public:
	NetProxy(std::vector<Net> &nets, size_t i) : nets_(nets), idx_(i) {}

	operator Net() const { return nets_[idx_]; }

	NetProxy &operator=(Net n)
	{
		nets_[idx_] = n;
		return *this;
	}

	NetProxy &operator=(const NetProxy &o)
	{
		nets_[idx_] = o.nets_[o.idx_];
		return *this;
	}

	bool operator==(Net n) const { return nets_[idx_] == n; }
	bool operator!=(Net n) const { return nets_[idx_] != n; }
	bool operator==(slang_frontend::Trit t) const { return nets_[idx_] == t; }
	bool operator!=(slang_frontend::Trit t) const { return nets_[idx_] != t; }
	slang_frontend::Trit as_trit() const { return nets_[idx_].as_trit(); }
};

// Multi-bit signal, LSB at index 0.
struct Value
{
	std::vector<Net> nets_;

	Value() = default;
	Value(Net bit) : nets_{bit} {}
	Value(slang_frontend::Trit t) : nets_{Net(t)} {}
	Value(slang_frontend::Trit t, uint64_t width) : nets_(width, Net(t)) {}
	Value(const slang_frontend::TritVector &c);

	explicit Value(int val, int width = 32)
	{
		nets_.reserve(width);
		for (int i = 0; i < width; i++) {
			const bool bit = i < 32 ? ((static_cast<uint32_t>(val) >> i) & 1) : (val < 0);
			nets_.push_back(bit ? Net::one() : Net::zero());
		}
	}

	// Concatenation (MSB-first, matching Verilog semantics).
	Value(std::initializer_list<Value> parts)
	{
		for (auto it = parts.end(); it != parts.begin();) {
			--it;
			nets_.insert(nets_.end(), it->nets_.begin(), it->nets_.end());
		}
	}

	uint64_t size() const { return nets_.size(); }
	uint64_t width() const { return nets_.size(); }
	bool empty() const { return nets_.empty(); }

	Net operator[](uint64_t i) const { return nets_[i]; }
	NetProxy operator[](uint64_t i) { return NetProxy(nets_, i); }

	Value extract(uint64_t offset, uint64_t width) const
	{
		Value result;
		result.nets_.assign(nets_.begin() + offset, nets_.begin() + offset + width);
		return result;
	}
	Value extract_end(uint64_t offset) const { return extract(offset, nets_.size() - offset); }
	void append(Net bit) { nets_.push_back(bit); }
	void append(const NetProxy &p) { nets_.push_back(Net(p)); }
	void append(slang_frontend::Trit t) { nets_.push_back(Net(t)); }
	void append(Value other) { nets_.insert(nets_.end(), other.nets_.begin(), other.nets_.end()); }
	void remove(uint64_t index, uint64_t width = 1)
	{
		nets_.erase(nets_.begin() + index, nets_.begin() + index + width);
	}
	Value repeat(uint64_t count) const
	{
		Value result;
		result.nets_.reserve(nets_.size() * count);
		for (uint64_t i = 0; i < count; i++) {
			result.nets_.insert(result.nets_.end(), nets_.begin(), nets_.end());
		}
		return result;
	}
	void extend_u0(uint64_t width, bool is_signed = false)
	{
		if (width < nets_.size()) {
			nets_.erase(nets_.begin() + width, nets_.end());
			return;
		}
		Net fill = (is_signed && !nets_.empty()) ? nets_.back() : Net::zero();
		nets_.resize(width, fill);
	}
	// Return a copy resized to `width` bits, sign-extending when `is_signed`.
	Value extend(uint64_t width, bool is_signed = false) const
	{
		Value result = *this;
		result.extend_u0(width, is_signed);
		return result;
	}
	Net msb() const { return nets_.back(); }
	void reserve(uint64_t n) { nets_.reserve(n); }

	bool is_fully_const() const
	{
		for (auto &n : nets_) {
			if (!n.is_const()) {
				return false;
			}
		}
		return true;
	}
	bool is_fully_def() const
	{
		for (auto &n : nets_) {
			if (!n.is_def()) {
				return false;
			}
		}
		return true;
	}
	bool is_fully_zero() const
	{
		for (auto &n : nets_) {
			if (n != Net::zero()) {
				return false;
			}
		}
		return true;
	}
	bool is_fully_ones() const
	{
		for (auto &n : nets_) {
			if (n != Net::one()) {
				return false;
			}
		}
		return true;
	}

	Net as_net() const
	{
		assert(nets_.size() == 1);
		return nets_[0];
	}

	// The frontend's constant representation of this value (requires every
	// bit to be a constant tie-off).
	slang_frontend::TritVector as_const() const;

	bool as_bool() const
	{
		for (auto &n : nets_) {
			if (n == Net::one()) {
				return true;
			}
		}
		return false;
	}
	int as_int(bool is_signed = false) const;

	struct const_iterator
	{
		using iterator_category = std::input_iterator_tag;
		using value_type = Net;
		using difference_type = std::ptrdiff_t;
		using pointer = const Net *;
		using reference = Net;

		std::vector<Net>::const_iterator it;
		Net operator*() const { return *it; }
		const_iterator &operator++()
		{
			++it;
			return *this;
		}
		const_iterator operator++(int)
		{
			auto tmp = *this;
			++it;
			return tmp;
		}
		bool operator!=(const const_iterator &o) const { return it != o.it; }
		bool operator==(const const_iterator &o) const { return it == o.it; }
	};

	const_iterator begin() const { return {nets_.begin()}; }
	const_iterator end() const { return {nets_.end()}; }

	bool operator==(const Value &o) const { return nets_ == o.nets_; }
	bool operator!=(const Value &o) const { return nets_ != o.nets_; }
};

inline Value Net::repeat(uint64_t width)
{
	return Value(*this).repeat(width);
}

} // namespace ir
