/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Polya.Meta

/-! # Pólya's conjecture at its smallest counterexample

The computation at 906150257, with the prime powers checked against the certified sieve, and the
three statements it settles. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_sieve 936411
run_polya 906150257

namespace PrimeCert.Polya

/-- The running total of the Liouville values at 906150257, the smallest argument where it is
positive. -/
theorem polya_witness : L 906150257 = 1 := by
  rw [polyaValue]
  norm_num

/-- Pólya's conjecture has a counterexample. -/
example : ∃ n, 2 ≤ n ∧ 0 < L n :=
  exists_pos_L 906150257 (by norm_num) (by rw [polya_witness]; norm_num)

/-- Pólya's conjecture is false. -/
theorem polya_conjecture_false : ¬ ∀ n, 2 ≤ n → L n ≤ 0 :=
  not_forall_L_nonpos 906150257 (by norm_num) (by rw [polya_witness]; norm_num)

/--
info: 'PrimeCert.Polya.polya_conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms polya_conjecture_false

end PrimeCert.Polya
