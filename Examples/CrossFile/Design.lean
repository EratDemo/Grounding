-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Grounding

/-!
Embeds a design and uses nothing from it. `Examples.CrossFile.Use` imports this
module and evaluates `sv_expr%` in another file, which exercises recovering the
native handle from the persisted `DesignInfo` (the live handle of this elaboration
does not exist there).
-/

sv_design adder
  "Examples/CrossFile/adder.sv"
