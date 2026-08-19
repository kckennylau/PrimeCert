/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import PrimeCertTest.WieferichBenchDefs

/-! The check with the exponent written as a subtraction, over the positions the other runs walk. -/

open PrimeCert.Wieferich

set_option maxRecDepth 4000000 in
set_option Elab.async false in
bench_check wieferichAtSub 2310 1000000
