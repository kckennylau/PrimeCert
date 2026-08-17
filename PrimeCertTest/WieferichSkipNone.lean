/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCertTest.WieferichBenchDefs
meta import PrimeCert.Meta.QuickRfl

/-! `n.mod 5` is below 5, so the right branch is taken throughout and every power is computed.
This gives the cost of the added test alone. -/

namespace PrimeCert.Bench

set_option maxRecDepth 4000000
set_option Elab.async false

theorem bench : ∀ n < 600000, n % 6 = 1 →
    ((n.mod 5).beq 7).or' ((wieferichB n).not'.or' (mirimanoffB n).not') :=
  forallB_of_mod _ (start := 1) (len := 100000) (step := 6) (by quickRfl)

end PrimeCert.Bench
