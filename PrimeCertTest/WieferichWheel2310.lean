/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! One spoke of a mod-2310 wheel, covering the same 600000 as `WieferichBase` covers with its
mod-6 spoke. The wheel has 480 spokes against mod 6's 2. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (wieferichB n).not'.or' (mirimanoffB n).not') 1 260 2310 := by
  quickRfl

end PrimeCert.Bench
