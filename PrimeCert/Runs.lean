/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Runs of equal quotients

Fix `v`. As `k` runs over `1, 2, …, v`, the quotient `v / k` repeats: every index from `k` up to
`v / (v / k)` inclusive gives the same quotient (`div_eq_of_run`), and that range does start at `k`
(`le_div_div`). Call such a range the run at `k`.

So a sum of `f (v / k')` over the run at `k` is the run's length times `f (v / k)` (`sum_run`). A
consumer sums over every `k ≤ v` by taking one such term and jumping from `k` to `v / (v / k) + 1`;
that the runs so visited cover `1, …, v` is the consumer's own invariant, and this file supplies
only the value of each one.
-/

namespace PrimeCert

open Finset

/-- Every index from `k` up to the end of its run has the quotient `v / k`. -/
public theorem div_eq_of_run {v k k' : ℕ} (hk : k ≠ 0) (hkk' : k ≤ k')
    (hk' : k' ≤ v / (v / k)) : v / k' = v / k := by
  refine Nat.le_antisymm (Nat.div_le_div_left hkk' (by omega))
    ((Nat.le_div_iff_mul_le (by omega)).2 ?_)
  calc (v / k) * k' ≤ (v / k) * (v / (v / k)) := Nat.mul_le_mul_left _ hk'
    _ = (v / (v / k)) * (v / k) := Nat.mul_comm _ _
    _ ≤ v := Nat.div_mul_le_self v (v / k)

/-- The run at `k` contains `k`, so it is a range from `k` upwards. -/
public theorem le_div_div {v k : ℕ} (hk : k ≠ 0) (hkv : k ≤ v) : k ≤ v / (v / k) := by
  refine (Nat.le_div_iff_mul_le (Nat.div_pos hkv (by omega))).2 ?_
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self v k

/-- A sum of `f (v / k')` over the run at `k` is the run's length times `f (v / k)`. -/
public theorem sum_run {v k : ℕ} (hk : k ≠ 0) (hkv : k ≤ v) (f : ℕ → ℤ) :
    ∑ k' ∈ Finset.Icc k (v / (v / k)), f (v / k')
      = (v / (v / k) - k + 1 : ℕ) * f (v / k) := by
  have hle : k ≤ v / (v / k) := le_div_div hk hkv
  rw [Finset.sum_congr rfl fun k' hk' => ?_, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  · congr 2
    omega
  · simp only [Finset.mem_Icc] at hk'
    rw [div_eq_of_run hk hk'.1 hk'.2]

end PrimeCert
