/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
import PrimeCert.SieveBase
meta import PrimeCert.Meta.QuickRfl

/-! One residue class of the mod-30030 wheel, filtered by the cached sieve bit, covering the
whole 1000000 the cache holds. The class `n ≡ 1 mod 30030` has sieve index `t = 10010 * k`. -/

namespace PrimeCert.Bench

open PrimeCert.Sieve

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun t ↦ (testBitK sieveBits_1000000 t).not'.or'
      ((wieferichB (numK t)).not'.or' (mirimanoffB (numK t)).not')) 0 33 10010 := by
  quickRfl

end PrimeCert.Bench
