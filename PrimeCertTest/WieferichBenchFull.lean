/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import PrimeCertTest.WieferichBenchDefs

/-! The shipped check, over the same positions as the lookup-only run. -/

open PrimeCert.Wieferich

set_option maxRecDepth 4000000 in
set_option Elab.async false in
bench_check wieferichAt 2310 1000000
