/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Summatory
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Runs of equal quotients

The indices `k` with `v / k` equal to a given value form a contiguous run ending at `v / (v / k)`
(`div_eq_of_run`), so a sum over the indices collapses to one term per run (`sum_run`). The block
loop walks those runs.
-/

namespace PrimeCert.Polya

open Finset

/-- Inside a run the quotient is constant. -/
public theorem div_eq_of_run {v k k' : ℕ} (hk : 0 < k) (hkv : k ≤ v) (hkk' : k ≤ k')
    (hk' : k' ≤ v / (v / k)) : v / k' = v / k := by
  have hq : 0 < v / k := Nat.div_pos hkv hk
  have hk'0 : 0 < k' := by omega
  refine Nat.le_antisymm (Nat.div_le_div_left hkk' hk) ?_
  have h1 : (v / k) * k' ≤ v :=
    calc (v / k) * k' ≤ (v / k) * (v / (v / k)) := Nat.mul_le_mul_left _ hk'
      _ = (v / (v / k)) * (v / k) := Nat.mul_comm _ _
      _ ≤ v := Nat.div_mul_le_self v (v / k)
  exact (Nat.le_div_iff_mul_le hk'0).2 h1

/-- The run starting at `k` ends at or after `k`. -/
public theorem le_div_div {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v) : k ≤ v / (v / k) :=
  (Nat.le_div_iff_mul_le (Nat.div_pos hkv hk)).2 (Nat.mul_comm k (v / k) ▸ Nat.div_mul_le_self v k)

/-- The run stays inside `1 … v`. -/
public theorem div_div_le (v k : ℕ) : v / (v / k) ≤ v := Nat.div_le_self _ _

/-- A sum over one run is its length times the value at the run's quotient. -/
public theorem sum_run {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v) (f : ℕ → ℤ) :
    ∑ k' ∈ Finset.Icc k (v / (v / k)), f (v / k')
      = (v / (v / k) - k + 1 : ℕ) * f (v / k) := by
  have hle : k ≤ v / (v / k) := le_div_div hk hkv
  rw [Finset.sum_congr rfl fun k' hk' => ?_, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  · congr 2
    omega
  · simp only [Finset.mem_Icc] at hk'
    rw [div_eq_of_run hk hkv hk'.1 hk'.2]

end PrimeCert.Polya
