/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
import PrimeCert.SieveBase
meta import PrimeCert.Meta.QuickRfl

/-! The sieve filter reading each bit by shifting `1` up to the index, rather than shifting the
bitset down. -/

namespace PrimeCert.Bench

open PrimeCert.Sieve

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench :
    forallB (fun t ↦ (Nat.blt 0 (Nat.land sieveBits_1000000 (Nat.shiftLeft 1 t))).not'.or'
      ((wieferichB (numK t)).not'.or' (mirimanoffB (numK t)).not')) 0 100000 2 := by
  quickRfl

end PrimeCert.Bench
