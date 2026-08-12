/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Polya.Summatory
public import Mathlib.Algebra.Ring.Parity

/-!
# The summatory function from a count

`λ n` is `-1` exactly when `Ω n` is odd, so `L v` is `v` less twice the number of `n ≤ v` with `Ω n`
odd (`L_eq_sub_two_mul`). That count is what the parity table's set bits record.
-/

namespace PrimeCert.Polya

open ArithmeticFunction Finset

/-- The Liouville function reads off the parity of the prime factor count. -/
public theorem liouville_eq_ite {n : ℕ} (hn : n ≠ 0) :
    liouville n = if Odd (cardFactors n) then -1 else 1 := by
  rw [liouville_apply hn]
  rcases Nat.even_or_odd (cardFactors n) with h | h
  · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h), h.neg_one_pow]
  · rw [if_pos h, h.neg_one_pow]

/-- `L v` counts the numbers up to `v` with an even number of prime factors against those with an
odd number. -/
public theorem L_eq_sub_two_mul (v : ℕ) :
    L v = (v : ℤ) - 2 * ({n ∈ Finset.Icc 1 v | Odd (cardFactors n)}).card := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hIcc : Finset.Icc 1 (v + 1) = insert (v + 1) (Finset.Icc 1 v) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (v + 1) ∉ {n ∈ Finset.Icc 1 v | Odd (cardFactors n)} := by simp
    rw [L_succ, ih, hIcc, Finset.filter_insert, liouville_eq_ite (by omega)]
    by_cases hodd : Odd (cardFactors (v + 1))
    · rw [if_pos hodd, if_pos hodd, Finset.card_insert_of_notMem hnot]
      push_cast
      ring
    · rw [if_neg hodd, if_neg hodd]
      push_cast
      ring

end PrimeCert.Polya
