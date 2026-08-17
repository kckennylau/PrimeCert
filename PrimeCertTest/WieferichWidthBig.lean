/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! The same check over 10000 terms starting at 10000000003, where `p ^ 2` exceeds `2 ^ 64`. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (wieferichB n).not'.or' (mirimanoffB n).not') 10000000003 10000 6 := by
  quickRfl

end PrimeCert.Bench
