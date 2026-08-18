/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! The check testing modulo `p` first, over the same 10000 terms as `WieferichWidth32`. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (wieferichTwoStage n).not'.or' (mirimanoffB n).not') 1 10000 6 := by
  quickRfl

end PrimeCert.Bench
