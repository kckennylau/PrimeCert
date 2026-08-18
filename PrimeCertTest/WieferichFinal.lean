/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import PrimeCertTest.WieferichClasses
public import PrimeCert.WieferichBound
public import PrimeCert.ForallB
meta import PrimeCert.Meta.QuickRfl

/-! # No prime below 1000000 is Wieferich, apart from 1093 and 3511 -/

namespace PrimeCert.Wieferich

open PrimeCert

/-- A residue coprime to 2310 is one the class theorems cover, or one of the two cut out. -/
@[expose] public noncomputable def coverAt (r : ℕ) : Bool :=
  ((Nat.gcd r 2310).beq 1).not'.or'
    ((memB r classes_2310).or' ((r.beq 1093).or' (r.beq 1201)))

set_option maxRecDepth 40000 in
public theorem cover : forallB coverAt 0 2310 1 := by quickRfl

end PrimeCert.Wieferich
