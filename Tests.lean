-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Grounding

open Grounding Grounding.Rtl

/-- 128-step nonlinear hash chain; a shared DAG keeps elaboration linear. -/
def hash128Source : String := r#"
module hash128(input logic [31:0] x, output logic [31:0] acc);
  always_comb begin
    acc = x;
    for (int i = 0; i < 128; i++)
      acc = (acc >> 5) ^ (acc + 1);
  end
endmodule
"#

def main : IO UInt32 := do
  match ← readSv hash128Source "hash128" with
  | .error msg =>
    IO.eprintln s!"hash128 elaboration failed: {msg}"
    return 1
  | .ok elaborated =>
    let netlist := elaborated.netlist
    if netlist.ports.length != 2 then
      IO.eprintln s!"expected 2 ports, got {netlist.ports.length}"
      return 1
    IO.println "hash128 ok"
    return 0
