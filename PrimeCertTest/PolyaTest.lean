/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.Meta.Polya

/-! # Tests for `run_lam`

The table built here is compared against the parity of `Ω` computed outside Lean, and the equation
the command emits is checked to be about that table.
-/

open PrimeCert.Polya

run_lam 200

/-- The emitted table agrees with the parity of `Ω n` for `1 ≤ n ≤ 200`. -/
example : lamLit = 2685532350315778980126693957439803788173598504951661943732652 := rfl

/-- The emitted equation relates the kernel definition to that table. -/
example : lamK lamPP 200 = lamLit := lamData

/-- Bit `n` is set exactly when `n` has an odd number of prime factors with multiplicity: `12` has
three, `36` has four, `199` is prime. -/
example : (lamLit.shiftRight 12).land 1 = 1 := rfl
example : (lamLit.shiftRight 36).land 1 = 0 := rfl
example : (lamLit.shiftRight 199).land 1 = 1 := rfl
example : (lamLit.shiftRight 1).land 1 = 0 := rfl

/-! A second table is refused. -/

/-- error: run_lam: a parity table already exists -/
#guard_msgs in
run_lam 200
