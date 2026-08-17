/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Theory.Summatory
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
  rcases Nat.even_or_odd (cardFactors n) with h | h <;>
    simp [liouville_apply hn, h.neg_one_pow, h, Nat.not_odd_iff_even]

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
    split_ifs with hodd
    · rw [Finset.card_insert_of_notMem hnot]
      push_cast
      ring
    · push_cast
      ring

end PrimeCert.Polya
