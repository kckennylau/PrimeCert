/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve
public import Mathlib.Data.Nat.Prime.Basic

import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import PrimeCert.ForLean
import PrimeCert.ForMathlib

/-!
# Correctness of the mod-6 wheel sieve

Bit `t` of `PrimeCert.Sieve.sieveK n sqrtN` is set exactly when the number at index `t` is prime
(`sieveK_testBit_iff`), and `prime_of_sieve_eq` turns one bit of a cached sieve literal into
`Nat.Prime`. The argument runs in four steps:

1. reading a bit as `0` or `1` agrees with `Nat.testBit`, and `initK` has bits `1 … M` set;
2. `buildMaskK` sets the positions `A, A + 2*p, A + 4*p, …` and the same from `B`;
3. `markMaskK` clears exactly those positions, which hold the multiples `p*k` with `k ≥ 5`
   coprime to 6;
4. the bits left standing are exactly the primes.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Layer 1: bit reading and encoding -/

@[simp, grind =] public theorem numK_eq_num : numK = num := rfl

/-- `testBitK` reads bit `i` as a `ℕ` (`0` or `1`); it agrees with `Nat.testBit`. -/
@[grind =]
theorem testBitK_eq_testBit {b i : ℕ} : testBitK b i = if b.testBit i then 1 else 0 := by
  simp [testBitK, Nat.shiftRight_eq_div_pow]
  grind

public theorem testBitK_eq_one_iff {b i : ℕ} : testBitK b i = 1 ↔ b.testBit i := by
  grind

lemma initK_eq {M : ℕ} : initK M = (2 ^ M - 1) <<< 1 := by
  simp [initK, Nat.shiftLeft_eq]
  grind

/-- `initK M = 2^(M+1) - 2` has bits `1 … M` set and bit `0` clear. -/
theorem testBit_initK {M t : ℕ} :
    (initK M).testBit t ↔ 1 ≤ t ∧ t ≤ M := by grind [initK_eq]

/-! ## Layer 2: `buildMaskK` sets two progressions stepping by `2*p` -/

@[simp, grind =] theorem buildMaskK_zero {p M A B : ℕ} :
    buildMaskK p M A B 0 = 1 <<< A ||| 1 <<< B := rfl

theorem buildMaskK_succ_raw {p M A B n : ℕ} :
    buildMaskK p M A B (n + 1)
      = Bool.rec (buildMaskK p M A B n)
          ((buildMaskK p M A B n).lor
            ((buildMaskK p M A B n).shiftLeft (p.shiftLeft n.succ)))
          ((p.shiftLeft n.succ).ble M) := rfl

theorem buildMaskK_succ {p M A B n : ℕ} :
    buildMaskK p M A B (n + 1)
      = if p * 2 ^ (n + 1) ≤ M
        then buildMaskK p M A B n ||| buildMaskK p M A B n <<< (p * 2 ^ (n + 1))
        else buildMaskK p M A B n := by
  have hs : p <<< (n + 1) = p * 2 ^ (n + 1) := by grind [Nat.shiftLeft_eq]
  simp [buildMaskK_succ_raw, hs, Bool.rec_eq]

/-- After `n` doublings, `buildMaskK` sets exactly the bits at `A + 2*p*j` and `B + 2*p*j` with
`j < 2^n`. -/
theorem testBit_buildMaskK_pow {p M A B n t : ℕ} (ht : t ≤ M) :
    (buildMaskK p M A B n).testBit t ↔ (∃ j < 2 ^ n, t = A + 2 * p * j ∨ t = B + 2 * p * j) := by
  induction n generalizing t with
  | zero => grind [one_shiftLeft]
  | succ n ih =>
    rw [buildMaskK_succ]
    have h : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by grind
    obtain hg | hg := le_or_gt (p * 2 ^ (n + 1)) M
    · rw [if_pos hg, Nat.testBit_or, Nat.testBit_shiftLeft]
      simp only [ge_iff_le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih (by lia), ih (by lia), h, exists_lt_add_iff_lt_left, ← exists_and_left]
      congr! 1
      apply exists_congr (by grind)
    · rw [if_neg hg.not_ge, ih ht, h, exists_lt_add_iff_lt_left, iff_self_or]
      grind [mul_add]

theorem prog_iff_dvd {c t p B : ℕ} (hB : t < 2 * p * B) :
    (∃ j < B, t = c + 2 * p * j) ↔ (c ≤ t ∧ 2 * p ∣ t - c) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Nat.le_add_right _ _, ⟨j, by lia⟩⟩
  · rintro ⟨hc, k, hk⟩
    refine ⟨k, ?_, by lia⟩
    have hlt : 2 * p * k < 2 * p * B := by lia
    exact Nat.lt_of_mul_lt_mul_left hlt

theorem testBit_buildMaskK {p M A B n t : ℕ} (hp : p ≠ 0) (ht : t ≤ M) (hM : M < 2 ^ n) :
    (buildMaskK p M A B n).testBit t ↔
      (A ≤ t ∧ 2 * p ∣ t - A) ∨ (B ≤ t ∧ 2 * p ∣ t - B) := by
  have : t < 2 * p * 2 ^ n := by
    grw [ht, hM]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  simp_rw [← prog_iff_dvd this, ← exists_or, testBit_buildMaskK_pow ht, and_or_left]

end PrimeCert.Sieve
