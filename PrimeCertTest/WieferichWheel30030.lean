/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! One residue class of the mod-30030 wheel, covering the same 600000. The wheel keeps 5760
classes of 30030, so each holds 19 terms. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (wieferichB n).not'.or' (mirimanoffB n).not') 1 19 30030 := by
  quickRfl

end PrimeCert.Bench
