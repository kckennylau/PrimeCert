/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import MillerRabin.Main
meta import PrimeCert.Meta.QuickRfl

/-! Splits the cost of `cover` into its two components, over the same 2310 remainders. -/

open PrimeCert

namespace MillerRabin

/-- The divisor test of `coverAt`, holding whatever it reads. -/
noncomputable def gcdOnlyAt (r : ℕ) : Bool :=
  ((Nat.gcd r 2310).beq 1).not'.or' true

/-- The divisor test of `coverAt` followed by its list walk, at the remainders `coverAt` walks,
holding whatever they read. -/
noncomputable def gcdThenMemAt (r : ℕ) : Bool :=
  ((Nat.gcd r 2310).beq 1).not'.or' ((memB r classes_2310).or' true)

set_option maxRecDepth 40000 in
set_option Elab.async false in
theorem cover_gcd_only : forallB gcdOnlyAt 0 2310 1 := by quickRfl

set_option maxRecDepth 40000 in
set_option Elab.async false in
theorem cover_gcd_then_mem : forallB gcdThenMemAt 0 2310 1 := by quickRfl

end MillerRabin
