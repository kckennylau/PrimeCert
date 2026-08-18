/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! The middle piece of the mod-6 class split into 480. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (wieferichB n).not'.or' (mirimanoffB n).not') 299521 208 6 := by
  quickRfl

end PrimeCert.Bench
