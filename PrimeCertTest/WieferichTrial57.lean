/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! The check skipping any term divisible by 5 or 7. Terms are `1 mod 6`, so 2 and 3 divide
none of them. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun n ↦ (passes n [5, 7]).not'.or'
      ((wieferichB n).not'.or' (mirimanoffB n).not')) 1 100000 6 := by
  quickRfl

end PrimeCert.Bench
