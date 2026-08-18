/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Sums over the intervals where `v / k` is constant

Every `k'` in `Icc k (v / (v / k))` has `v / k' = v / k` (`div_eq_div_of_le`, `le_div_div`), so
summing `f (v / k')` there gives one term (`sum_Icc_div_div`), which `sum_Ico_extend` adds to a sum
already taken over `Ico a k`. Repeating that from `k = 1` builds `∑_{k ≤ v} f (v / k)` with one term
per distinct quotient.
-/

namespace PrimeCert

/-- The quotient stays `v / k` from `k` up to `v / (v / k)`. -/
public theorem div_eq_div_of_le {v k k' : ℕ} (hk : k ≠ 0) (hkk' : k ≤ k')
    (hk' : k' ≤ v / (v / k)) : v / k' = v / k := by
  refine (Nat.div_le_div_left hkk' (Nat.pos_of_ne_zero hk)).antisymm ?_
  grw [Nat.le_div_iff_mul_le (by lia), hk', Nat.mul_div_le]

/-- `k` is at most `v / (v / k)`. -/
public theorem le_div_div {v k : ℕ} (hk : k ≠ 0) (hkv : k ≤ v) : k ≤ v / (v / k) := by
  grw [Nat.le_div_iff_mul_le (Nat.div_pos hkv (Nat.pos_of_ne_zero hk)), Nat.mul_div_le]

open Finset

/-- A sum of `f (v / k')` over `Icc k (v / (v / k))` is its length times `f (v / k)`. -/
public theorem sum_Icc_div_div {α : Type*} [AddCommMonoid α] {v k : ℕ} (hk : k ≠ 0) (hkv : k ≤ v)
    (f : ℕ → α) :
    ∑ k' ∈ Icc k (v / (v / k)), f (v / k') = (v / (v / k) - k + 1) • f (v / k) := by
  have hle : k ≤ v / (v / k) := le_div_div hk hkv
  rw [Finset.sum_congr rfl fun k' hk' => ?_, Finset.sum_const, Nat.card_Icc]
  · congr 1
    grind
  · simp only [Finset.mem_Icc] at hk'
    rw [div_eq_div_of_le hk hk'.1 hk'.2]

/-- Extend a sum over `Ico a k` by the whole interval starting at `k`, which adds one term. -/
public theorem sum_Ico_extend {α : Type*} [AddCommMonoid α] {v a k : ℕ} (hk : k ≠ 0) (hkv : k ≤ v)
    (hak : a ≤ k) (f : ℕ → α) :
    (∑ k' ∈ Ico a k, f (v / k')) + (v / (v / k) - k + 1) • f (v / k)
      = ∑ k' ∈ Ico a (v / (v / k) + 1), f (v / k') := by
  have hle : k ≤ v / (v / k) := le_div_div hk hkv
  rw [← sum_Icc_div_div hk hkv f, ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a k (v / (v / k) + 1)),
    Finset.Ico_union_Ico_eq_Ico hak (by omega)]

end PrimeCert
