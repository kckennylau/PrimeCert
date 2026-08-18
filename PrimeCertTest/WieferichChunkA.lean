/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! The mod-6 class split into 480 pieces of 1250, this being the first piece. Comparing the
three sampled pieces against one 100000-term fold separates chunking from the wheel. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (wieferichB n).not'.or' (mirimanoffB n).not') 1 208 6 := by
  quickRfl

end PrimeCert.Bench
