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

1. reading a bit as `0` or `1` agrees with `Nat.testBit`, `initK` has bits `1 … M` set, and `num`
   sends an index to the number it stands for;
2. `buildMaskK` marks the positions `A, A + 2*p, A + 4*p, …` and the same from `B`, which hold
   the multiples `p*k` with `k ≥ 5` coprime to 6;
3. `markMaskK` clears exactly the marked positions;
4. the bits left standing are exactly the primes.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Layer 1: bit reading and encoding -/

@[simp, grind =] public theorem numK_eq_num : numK = num := rfl

/-- The loop's bit test agrees with `Nat.testBit`. -/
@[grind =]
public theorem testBitK_eq_testBit {b i : ℕ} : testBitK b i = b.testBit i := by
  have h : testBitK b i = Nat.ble 1 (b &&& (1 <<< i)) := rfl
  rw [h, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow]
  cases hb : b.testBit i
  · simp only [Bool.toNat_false, Nat.zero_mul]; rfl
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact Nat.ble_eq_true_of_le Nat.one_le_two_pow

lemma initK_eq {M : ℕ} : initK M = (2 ^ M - 1) <<< 1 := by
  simp [initK, Nat.shiftLeft_eq]
  grind

/-- `initK M = 2^(M+1) - 2` has bits `1 … M` set and bit `0` clear. -/
theorem testBit_initK {M t : ℕ} :
    (initK M).testBit t ↔ 1 ≤ t ∧ t ≤ M := by grind [initK_eq]

/-- Adding an even amount `2*m` to the index adds `6*m` to the number. -/
@[grind =]
theorem num_add_two_mul {k m : ℕ} : num (k + 2 * m) = num k + 6 * m := by grind [num]

@[grind =]
theorem num_startA {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) : num ((p * 5 - 1) / 3) = 5 * p := by
  grind [num]

@[grind =]
theorem num_startB {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) : num ((p * 7 - 1) / 3) = 7 * p := by
  grind [num]

theorem num_strictMono : StrictMono num := by grind [num, StrictMono]

@[grind inj] theorem num_inj : Function.Injective num := num_strictMono.injective

/-! ## Layer 2: what the mask marks

`buildMaskK` sets the two progressions stepping by `2*p`, and `num` carries those positions to the
coprime-to-6 multiples `p*k` with `k ≥ 5`, which is `mask_iff` at the end of the section. -/

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

/-- `buildMaskK` started at indices `(5*p-1)/3`, `(7*p-1)/3`, the form `markMaskK` uses, marks
index `t` iff `num t` is a coprime-to-6 multiple `p*k` with `k ≥ 5`. -/
theorem mask_iff (p M t : ℕ) (hp6 : p % 6 = 1 ∨ p % 6 = 5)
    (hM : M < 2 ^ 32) (ht : t ≤ M) :
    (buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32).testBit t ↔
      ∃ k, 5 ≤ k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧ num t = p * k := by
  rw [testBit_buildMaskK (by lia) ht hM]
  constructor
  · rintro (⟨hle, c, hc⟩ | ⟨hle, c, hc⟩)
    · exact ⟨5 + 6 * c, by grind [num]⟩
    · exact ⟨7 + 6 * c, by grind [num]⟩
  · rintro ⟨k, hk5, hk6, hnum⟩
    rcases hk6 with h1 | h5
    · right
      obtain ⟨j, rfl⟩ : ∃ j, k = 7 + 6 * j := ⟨(k - 7) / 6, by grind⟩
      have ht2 : num t = num ((p * 7 - 1) / 3 + 2 * (p * j)) := by grind
      exact ⟨by grind, j, by grind⟩
    · left
      obtain ⟨j, rfl⟩ : ∃ j, k = 5 + 6 * j := ⟨(k - 5) / 6, by grind⟩
      have ht2 : num t = num ((p * 5 - 1) / 3 + 2 * (p * j)) := by grind
      exact ⟨by grind, j, by grind⟩

/-! ## Layer 3: `markMaskK` clears exactly the mask bits -/

/-- `markMaskK bits p M` is bitwise `ldiff` of `bits` against `buildMaskK` (subtracting a
submask). -/
theorem markMaskK_eq_ldiff {bits p M : ℕ} :
    markMaskK bits p M = bits.ldiff (buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32) := by
  rw [markMaskK]
  simp [sub_and_eq_ldiff, Nat.div_eq_div]

/-- `markMaskK` clears exactly the bits set in `buildMaskK`, keeping the rest of `bits`. -/
theorem testBit_markMaskK {bits p M t : ℕ} :
    (markMaskK bits p M).testBit t
      = (bits.testBit t && !(buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32).testBit t) := by
  rw [markMaskK_eq_ldiff, Nat.testBit_ldiff]

end PrimeCert.Sieve
