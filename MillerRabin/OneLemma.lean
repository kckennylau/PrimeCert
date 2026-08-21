/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import MillerRabin.Bound
meta import PrimeCert.Meta.QuickRfl

/-! One scan covering every residue class, in place of 478 named theorems and a list. -/

open PrimeCert PrimeCert.Sieve

namespace MillerRabin

/-- At remainder `r`: true when `r` shares a factor with 2310, true at the two classes holding a
known Wieferich prime, and otherwise the scan of that class below 1000000. -/
noncomputable def classAt (r : ℕ) : Bool :=
  ((Nat.gcd r 2310).beq 1).not'.or'
    ((r.beq 1093).or' ((r.beq 1201).or' (forallB wieferichAtK (indexK r) 433 770)))

set_option maxRecDepth 4000000 in
set_option Elab.async false in
theorem all_classes : forallB classAt 0 2310 1 := by quickRfl

end MillerRabin
