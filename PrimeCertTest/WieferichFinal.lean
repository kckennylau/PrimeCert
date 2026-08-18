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

/-- A remainder coprime to 2310 falls into one of the three cases. -/
public theorem residue_cases {r : ℕ} (hr : r < 2310) (hg : Nat.gcd r 2310 = 1) :
    r ∈ classes_2310 ∨ r = 1093 ∨ r = 1201 := by
  have h := (forallB_iff coverAt 0 2310 1).mp cover r (by omega)
  rw [coverAt] at h
  simp [Nat.mul_one, Nat.add_zero, hg, Bool.not'_eq_not, Bool.or'_eq_or, Nat.beq_eq] at h
  rcases h with h | h | h
  · exact Or.inl (memB_iff.mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end PrimeCert.Wieferich
