/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# The summatory Liouville function

`L v` sums `ArithmeticFunction.liouville` over `1 … v`. Pólya conjectured `L v ≤ 0` for `v ≥ 2`.
-/

namespace PrimeCert.Polya

open ArithmeticFunction Finset

/-- `L v = ∑_{n = 1}^{v} λ n`, the summatory Liouville function. -/
public def L (v : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 v, liouville n

/-- The summation range as a half-open interval, the form the mathlib divisor-sum lemmas take. -/
public theorem L_eq_sum_Ioc (v : ℕ) : L v = ∑ n ∈ Finset.Ioc 0 v, liouville n := by
  rw [L]
  congr 1

@[simp] public theorem L_zero : L 0 = 0 := by simp [L]

@[simp] public theorem L_one : L 1 = 1 := by simp [L, liouville_apply_one]

/-- One more term. -/
public theorem L_succ (v : ℕ) : L (v + 1) = L v + liouville (v + 1) := by
  rw [L, L, Finset.sum_Icc_succ_top (by omega)]

end PrimeCert.Polya
