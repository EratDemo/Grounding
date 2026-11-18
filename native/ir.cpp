// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#include "ir.h"
#include "slang_frontend.h"

namespace ir {

Net::Net(slang_frontend::Trit t)
{
	switch (static_cast<uint8_t>(t)) {
	case static_cast<uint8_t>(slang_frontend::S0): id_ = kZero; break;
	case static_cast<uint8_t>(slang_frontend::S1): id_ = kOne; break;
	default:                                       id_ = kUndef; break;
	}
}

slang_frontend::Trit Net::as_trit() const
{
	if (id_ == kZero) {
		return slang_frontend::S0;
	}
	if (id_ == kOne) {
		return slang_frontend::S1;
	}
	return slang_frontend::Sx;
}

Value::Value(const slang_frontend::TritVector &c)
{
	nets_.reserve(c.size());
	for (slang_frontend::Trit t : c) {
		nets_.push_back(Net(t));
	}
}

slang_frontend::TritVector Value::as_const() const
{
	std::vector<slang_frontend::Trit> bits;
	bits.reserve(nets_.size());
	for (const Net &n : nets_) {
		bits.push_back(n.as_trit());
	}
	return slang_frontend::TritVector(bits);
}

int Value::as_int(bool is_signed) const
{
	return as_const().as_int(is_signed);
}

} // namespace ir
