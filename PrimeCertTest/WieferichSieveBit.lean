/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
import PrimeCert.SieveBase
meta import PrimeCert.Meta.QuickRfl

/-! The check skipping any term the cached sieve says is composite. The fold runs over the sieve
index `t`, whose number is `num t = 3 * t + 1 + t % 2`, so even `t` gives the terms `1 mod 6`. -/

namespace PrimeCert.Bench

open PrimeCert.Sieve

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun t ↦ (testBitK sieveBits_1000000 t).not'.or'
      ((wieferichB (numK t)).not'.or' (mirimanoffB (numK t)).not')) 0 100000 2 := by
  quickRfl

end PrimeCert.Bench
