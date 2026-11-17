// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
// 128 iterations of a nonlinear hash chain. Each step uses the previous value
// twice; copying the previous expression tree per use would be exponential
// (order 2^128), while a shared in-memory representation stays linear.
module hash128(input logic [31:0] x, output logic [31:0] acc);
  always_comb begin
    acc = x;
    for (int i = 0; i < 128; i++)
      acc = (acc >> 5) ^ (acc + 1);
  end
endmodule
