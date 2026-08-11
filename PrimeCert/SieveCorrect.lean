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
(`sieveK_testBit_iff`). The argument runs in three steps:

1. the loop's bit test agrees with `Nat.testBit`, `initK` has bits `1 … M` set, and `num`
   sends an index to the number it stands for;
2. `buildMaskK` marks the positions `A, A + 2*p, A + 4*p, …` and the same from `B`, which hold
   the multiples `p*k` with `k ≥ 5` coprime to 6;
3. `markMaskK` clears exactly the marked positions, so running it over every candidate index
   leaves the primes and nothing else.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Bit reading and the index-to-number map -/

@[simp, grind =] public theorem numK_eq_num : numK = num := rfl

/-- The loop's bit test agrees with `Nat.testBit`. -/
@[grind =]
public theorem testBitK_eq_testBit {b i : ℕ} : testBitK b i = b.testBit i := by
  grind [testBitK, shiftLeft_eq', one_shiftLeft, land_eq, and_two_pow, Nat.ble_eq]

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

@[grind .] theorem num_mod6 (k : ℕ) : num k % 6 = 1 ∨ num k % 6 = 5 := by grind [num]

@[grind .] theorem five_le_num {k : ℕ} (hk : k ≠ 0) : 5 ≤ num k := by grind [num]

@[grind .] theorem num_wheel {q : ℕ} (hq : q % 6 = 1 ∨ q % 6 = 5) : num ((q - 1) / 3) = q := by
  grind [num]

theorem num_strictMono : StrictMono num := by grind [num, StrictMono]

@[grind inj] theorem num_inj : Function.Injective num := num_strictMono.injective

/-! ## What the mask marks

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
theorem mask_iff {p M t : ℕ} (hp6 : p % 6 = 1 ∨ p % 6 = 5)
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

/-! ## Clearing: one pass, then the whole sieve

`markMaskK` removes exactly the marked positions, and running it over every candidate index leaves
the primes and nothing else. -/

/-! ### One pass -/

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

/-! ### From one pass to the whole sieve

`markMaskK` clears composite bits alone, so prime bits survive (completeness). For soundness, a
composite `num t` has a smallest prime factor `q ≤ √(num t) ≤ sqrtN`; the loop reaches `q` while its
own bit still stands, so its `markMaskK` fires and clears `t`. -/

theorem sieveLoopK_succ_eq_ite {M bits start fuel : ℕ} :
    sieveLoopK M bits start (fuel + 1)
      = if (sieveLoopK M bits start fuel).testBit (start + fuel)
        then markMaskK (sieveLoopK M bits start fuel) (num (start + fuel)) M
        else sieveLoopK M bits start fuel := by
  grind [sieveLoopK_succ, Bool.rec_eq]

/-- `markMaskK` (sieving by a wheel candidate `p ≥ 5`) preserves every bit whose number is prime:
the mask marks composite `num t = p * k` with `p, k ≥ 5`. -/
theorem markMaskK_preserves_prime {b p M t : ℕ} (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hp5 : 5 ≤ p)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hprime : (num t).Prime) :
    (markMaskK b p M).testBit t = b.testBit t := by
  rw [testBit_markMaskK]
  suffices h : (buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32).testBit t = false by simp [h]
  by_contra hc
  rw [Bool.not_eq_false, mask_iff hp6 hM ht] at hc
  obtain ⟨k, hk5, _, hnum⟩ := hc
  rcases hprime.eq_one_or_self_of_dvd p ⟨k, hnum⟩ with rfl | hself
  · lia
  · have : 1 = k := Nat.eq_of_mul_eq_mul_left (n := p) (by lia) (by lia)
    lia

/-- The loop preserves any prime bit: it stays at its initial value. -/
theorem sieveLoopK_preserves {M bits start fuel t : ℕ} (hstart : start ≠ 0)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hprime : (num t).Prime) :
    (sieveLoopK M bits start fuel).testBit t = bits.testBit t := by
  induction fuel with
  | zero => rfl
  | succ f ih =>
    rw [sieveLoopK_succ_eq_ite]
    split
    · rw [markMaskK_preserves_prime (by grind) (five_le_num (by grind)) hM ht hprime, ih]
    · exact ih

/-- Completeness: every prime bit in range survives the sieve. -/
theorem sieve_prime_set {n sqrtN t : ℕ} (ht1 : t ≠ 0) (htM : t ≤ (n - 1) / 3)
    (hM : (n - 1) / 3 < 2 ^ 32) (hprime : (num t).Prime) :
    (sieveK n sqrtN).testBit t = true := by
  grind [sieveK, div_eq_div, sieveLoopK_preserves, testBit_initK]

/-- If a prime index `j` in the processed range witnesses `num t = num j * m` (`m ≥ 5` coprime to
6), the sieve clears bit `t`. The bit at `j` still stands when the loop reaches it, so its
`markMaskK` fires, and every later step preserves the clear. -/
theorem sieveLoopK_clears {M start t j m : ℕ} (hstart : start ≠ 0)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hjprime : (num j).Prime) (hjt : j ≤ t)
    (hm5 : 5 ≤ m) (hm6 : m % 6 = 1 ∨ m % 6 = 5) (hnum : num t = num j * m) (hj_lo : start ≤ j)
    (fuel : ℕ) (hfuel : j < start + fuel) :
    (sieveLoopK M (initK M) start fuel).testBit t = false := by
  induction fuel with
  | zero => lia
  | succ f ih =>
    rw [sieveLoopK_succ_eq_ite]
    rcases Nat.lt_or_ge j (start + f) with hlt | hge
    · split <;> simp [testBit_markMaskK, ih hlt]
    · have hset : (sieveLoopK M (initK M) start f).testBit (start + f) = true := by
        rw [sieveLoopK_preserves hstart hM (by lia) (by grind)]
        grind [testBit_initK]
      simp_rw [if_pos hset, testBit_markMaskK, Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not,
        Bool.not_false]
      rw [mask_iff (num_mod6 _) hM ht]
      exact Or.inr ⟨m, by grind⟩

/-! ### Soundness number theory -/

theorem num_coprime6 {t : ℕ} : Nat.Coprime (num t) 6 := by
  have h := num_mod6 (k := t)
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  rcases h with h | h <;> simp [h]

theorem coprime6_mod {m : ℕ} : m.Coprime 6 ↔ m % 6 = 1 ∨ m % 6 = 5 := by
  have : ∀ t < 6, t.gcd 6 = 1 ↔ t % 6 = 1 ∨ t % 6 = 5 := by decide
  simpa using this (m % 6) (Nat.mod_lt _ (by simp))

/-- For `1 ≤ t ≤ (n-1)/3` with `num t ≤ n ≤ sqrtN*sqrtN`, bit `t` of the sieve is set iff `num t`
is prime. -/
public theorem sieveK_testBit_iff {n sqrtN t : ℕ} (ht : t ≠ 0) (htM : t ≤ (n - 1) / 3)
    (hM : (n - 1) / 3 < 2 ^ 32) (hbound : num t ≤ n) (hsqrt : n ≤ sqrtN * sqrtN) :
    (sieveK n sqrtN).testBit t ↔ (num t).Prime := by
  set k := (n - 1) / 3
  refine ⟨fun hset => ?_, sieve_prime_set ht htM hM⟩
  by_contra hnp
  have h5 : 5 ≤ num t := five_le_num (by lia)
  have hnt2 : num t % 2 = 1 := by have := num_mod6 (k := t); omega
  have hnt3 : num t % 3 ≠ 0 := by have := num_mod6 (k := t); omega
  obtain ⟨q, hqprime, hqdvd, hqsq⟩ : ∃ q, q.Prime ∧ q ∣ num t ∧ q ^ 2 ≤ num t :=
    ⟨(num t).minFac, minFac_prime (by omega), minFac_dvd _, minFac_sq_le_self (by omega) hnp⟩
  have hq2le : 2 ≤ q := hqprime.two_le
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 :=
    hqprime.mod_six_eq_one_or_five (by rintro rfl; lia) (by rintro rfl; lia)
  obtain ⟨m, hm⟩ := hqdvd
  have hqm : q ≤ m := Nat.le_of_mul_le_mul_left (by rw [← pow_two]; omega) (by lia)
  have hm5 : 5 ≤ m := by lia
  have hmdvd : m ∣ num t := ⟨q, by grind⟩
  have hm6 : m % 6 = 1 ∨ m % 6 = 5 := by
    rw [← coprime6_mod] at hq6 ⊢
    exact num_coprime6.coprime_dvd_left hmdvd
  have hqlt : q < num t := by nlinarith
  have hjqt : (q - 1) / 3 ≤ t := by
    rw [← num_strictMono.le_iff_le]
    grind
  have hqsqrt : q ≤ sqrtN := by nlinarith
  have hcleared : (sieveLoopK k (initK k) 1 ((sqrtN - 1) / 3)).testBit t = false := by
    grind [sieveLoopK_clears, num_wheel hq6]
  simp only [sieveK, sub_eq, div_eq_div] at hset
  grind

/-! ### Reading a prime off a cached sieve -/

theorem markMaskK_le {bits p M : ℕ} : markMaskK bits p M ≤ bits := by
  grind [markMaskK_eq_ldiff, Nat.and_add_ldiff]

grind_pattern markMaskK_le => markMaskK bits p M

theorem sieveLoopK_le {M bits start fuel : ℕ} : sieveLoopK M bits start fuel ≤ bits := by
  induction fuel with
  | zero => rfl
  | succ f ih => grind [sieveLoopK_succ_eq_ite]

grind_pattern sieveLoopK_le => sieveLoopK M bits start fuel

/-- The sieve leaves every bit above its top index clear. -/
public theorem sieveK_lt {n sqrtN : ℕ} : sieveK n sqrtN < 2 ^ ((n - 1) / 3 + 1) := by
  have h : sieveK n sqrtN ≤ initK ((n - 1) / 3) := by grind [sieveK, Nat.div_eq_div]
  have hp : 0 < 2 ^ ((n - 1) / 3) := by positivity
  have hi : initK ((n - 1) / 3) < 2 ^ ((n - 1) / 3 + 1) := by
    rw [initK_eq, Nat.shiftLeft_eq, pow_one, Nat.pow_succ]
    lia
  lia

/-- The number at an index bounds the index: `num t ≤ n` forces `t ≤ (n-1)/3`. -/
theorem le_div_of_num_le {n t : ℕ} (h : num t ≤ n) : t ≤ (n - 1) / 3 := by grind [num]

/-- `lit` decides primality for the numbers up to `n`: bit `t` is set exactly when `num t`, the
number at that index, is prime. `IsSieve.prime` reads it in the kernel-checked form. -/
@[expose] public def IsSieve (n lit : ℕ) : Prop :=
  ∀ t ≠ 0, num t ≤ n → (lit.testBit t ↔ (num t).Prime)

/-- A cached sieve satisfies `IsSieve`. `run_sieve` applies this once, so a consumer works from
`IsSieve` alone and never mentions `sieveK` or its square root. -/
public theorem isSieve_of_sieveK_eq {n sqrtN lit : ℕ} (hEq : sieveK n sqrtN = lit)
    (h3 : n.ble 12884901888) (h5 : n.ble (sqrtN.mul sqrtN)) :
    IsSieve n lit := by
  grind [IsSieve, sieveK_testBit_iff, le_div_of_num_le, Nat.ble_eq, Nat.div_eq_div]

/-- Read a prime off a sieve: a set bit at index `t` with `numK t = p` makes `p` prime. -/
public theorem IsSieve.prime {n lit t p : ℕ} (h : IsSieve n lit) (h1 : Nat.ble 1 t)
    (h4 : p.ble n) (hbit : testBitK lit t) (hp : (numK t).beq p) :
    Nat.Prime p := by
  grind [IsSieve, Nat.beq_eq, Nat.ble_eq]

end PrimeCert.Sieve
