/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve
import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import PrimeCert.ForLean

/-!
# Correctness of the mod-6 wheel sieve

Bit `t` of `PrimeCert.Sieve.sieveK n sqrtN` is set exactly when the number at index `t` is prime
(`sieveK_testBit_iff`), and `prime_of_sieve_eq` turns one bit of a cached sieve literal into
`Nat.Prime`. The section headers below mark the four steps of the argument.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Layer 1: bit reading and encoding -/

/-- `bitVal` reads bit `i` as a `Nat` (`0` or `1`); it agrees with `Nat.testBit`. -/
theorem bitVal_eq_testBit (b i : Nat) : bitVal b i = if b.testBit i then 1 else 0 := by
  simp [bitVal, Nat.shiftRight_eq_div_pow]
  grind

public theorem bitVal_eq_one_iff {b i : Nat} : bitVal b i = 1 ↔ b.testBit i := by
  grind [bitVal_eq_testBit]

lemma initK_eq {M : Nat} : initK M = (2 ^ M - 1) <<< 1 := by
  simp [initK, Nat.shiftLeft_eq]
  grind

/-- `initK M = 2^(M+1) - 2` has bits `1 … M` set and bit `0` clear. -/
theorem testBit_initK (M t : Nat) :
    (initK M).testBit t ↔ 1 ≤ t ∧ t ≤ M := by grind [initK_eq]

/-! ## Layer 2: `buildMaskK` sets two progressions stepping by `2*p` -/

@[simp] lemma Nat.ldiff_zero_left {b : Nat} : Nat.ldiff 0 b = 0 :=
  Nat.eq_of_testBit_eq (by simp)

@[simp] lemma Nat.ldiff_zero_right {b : Nat} : Nat.ldiff b 0 = b :=
  Nat.eq_of_testBit_eq (by simp)

/-- Disjoint OR equals ADD, for `Nat`; hence subtracting a submask acts as bitwise `ldiff`. -/
theorem and_add_ldiff {a b : Nat} : (a &&& b) + a.ldiff b = a := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit ba a' ih =>
    induction b using Nat.binaryRec with
    | zero => simp
    | bit bb b' _ => grind [Nat.land_bit, Nat.ldiff_bit, Nat.bit_val, cases Bool]

theorem sub_and_eq_ldiff {a b : Nat} : a - (a &&& b) = a.ldiff b := by grind [and_add_ldiff]

@[simp, grind =] theorem buildMaskK_zero {p M A B : Nat} :
    buildMaskK p M A B 0 = (1 <<< A) ||| (1 <<< B) := rfl

theorem buildMaskK_succ_raw {p M A B n : Nat} :
    buildMaskK p M A B (n + 1)
      = Bool.rec (buildMaskK p M A B n)
          ((buildMaskK p M A B n).lor
            ((buildMaskK p M A B n).shiftLeft (p.shiftLeft n.succ)))
          ((p.shiftLeft n.succ).ble M) := rfl

theorem buildMaskK_succ {p M A B n : Nat} :
    buildMaskK p M A B (n + 1)
      = if p * 2 ^ (n + 1) ≤ M
        then buildMaskK p M A B n ||| (buildMaskK p M A B n) <<< (p * 2 ^ (n + 1))
        else buildMaskK p M A B n := by
  have hs : p <<< (n + 1)  = p * 2 ^ (n + 1) := by grind [Nat.shiftLeft_eq]
  simp [buildMaskK_succ_raw, hs, Bool.rec_eq]

/-- After `n` doublings, `buildMaskK` sets exactly the bits at `A + 2*p*j` and `B + 2*p*j` with
`j < 2^n`. -/
theorem testBit_buildMaskK_pow {p M A B n t : Nat} (ht : t ≤ M) :
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

theorem prog_iff_dvd {c t p B : Nat} (hB : t < 2 * p * B) :
    (∃ j < B, t = c + 2 * p * j) ↔ (c ≤ t ∧ 2 * p ∣ t - c) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Nat.le_add_right _ _, ⟨j, by lia⟩⟩
  · rintro ⟨hc, k, hk⟩
    refine ⟨k, ?_, by lia⟩
    have hlt : 2 * p * k < 2 * p * B := by lia
    exact Nat.lt_of_mul_lt_mul_left hlt

theorem testBit_buildMaskK {p M A B n t : Nat} (hp : p ≠ 0) (ht : t ≤ M) (hM : M < 2 ^ n) :
    (buildMaskK p M A B n).testBit t ↔
      (A ≤ t ∧ 2 * p ∣ t - A) ∨ (B ≤ t ∧ 2 * p ∣ t - B) := by
  have : t < 2 * p * 2 ^ n := by
    grw [ht, hM]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  simp_rw [← prog_iff_dvd this, ← exists_or, testBit_buildMaskK_pow ht, and_or_left]

/-! ## Layer 3a: `markMaskK` clears exactly the mask bits -/

/-- `markMaskK bits p M` is bitwise `ldiff` of `bits` against `buildMaskK` (subtracting a
submask). -/
theorem markMaskK_eq_ldiff {bits p M : Nat} :
    markMaskK bits p M = bits.ldiff (buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32) := by
  rw [markMaskK]
  simp [sub_and_eq_ldiff, Nat.div_eq_div]

/-- `markMaskK` clears exactly the bits set in `buildMaskK`, keeping the rest of `bits`. -/
theorem testBit_markMaskK {bits p M t : Nat} :
    (markMaskK bits p M).testBit t
      = (bits.testBit t && !(buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32).testBit t) := by
  rw [markMaskK_eq_ldiff, Nat.testBit_ldiff]

/-! ## Layer 3b: the cleared bits are the coprime-to-6 multiples of `p`

`num` (the number at an index) grows by `6*m` when the index grows by `2*m`, and the starting
indices `(5*p-1)/3`, `(7*p-1)/3` hold the numbers `5*p`, `7*p` (for `p` coprime to 6). Hence the two
progressions carry exactly the coprime-to-6 multiples `p*k` with `k ≥ 5`. -/

/-- Adding an even amount `2*m` to the index adds `6*m` to the number. -/
theorem num_add_two_mul {k m : Nat} : num (k + 2 * m) = num k + 6 * m := by grind [num]

theorem num_startA {p : Nat} (hp : p % 6 = 1 ∨ p % 6 = 5) : num ((p * 5 - 1) / 3) = 5 * p := by
  grind [num]

theorem num_startB {p : Nat} (hp : p % 6 = 1 ∨ p % 6 = 5) : num ((p * 7 - 1) / 3) = 7 * p := by
  grind [num]

/-- The `A` progression carries `num` to `p*(5 + 6*j)` (numbers `≡ 5 mod 6`). -/
theorem numA {p t j : Nat} (hp : p % 6 = 1 ∨ p % 6 = 5)
    (h : t = (p * 5 - 1) / 3 + 2 * p * j) : num t = p * (5 + 6 * j) := by
  grind [mul_assoc, num_add_two_mul, num_startA hp]

/-- The `B` progression carries `num` to `p*(7 + 6*j)` (numbers `≡ 1 mod 6`). -/
theorem numB {p t j : Nat} (hp : p % 6 = 1 ∨ p % 6 = 5)
    (h : t = (p * 7 - 1) / 3 + 2 * p * j) : num t = p * (7 + 6 * j) := by
  grind [mul_assoc, num_add_two_mul, num_startB hp]

theorem num_strictMono : StrictMono num := by grind [num, StrictMono]

@[grind inj] theorem num_inj : Function.Injective num := num_strictMono.injective

/-- `buildMaskK` started at indices `(5*p-1)/3`, `(7*p-1)/3`, the form `markMaskK` uses, marks
index `t` iff `num t` is a coprime-to-6 multiple `p*k` with `k ≥ 5`. -/
theorem mask_iff (p M t : Nat) (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hp : p ≠ 0)
    (hM : M < 2 ^ 32) (ht : t ≤ M) :
    (buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32).testBit t ↔
      ∃ k, 5 ≤ k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧ num t = p * k := by
  rw [testBit_buildMaskK hp ht hM]
  constructor
  · rintro (⟨hle, c, hc⟩ | ⟨hle, c, hc⟩)
    · refine ⟨5 + 6 * c, by omega, Or.inr (by omega), ?_⟩
      grind [num]
    · refine ⟨7 + 6 * c, by omega, Or.inl (by omega), ?_⟩
      grind [num]
  · rintro ⟨k, hk5, hk6, hnum⟩
    rcases hk6 with h1 | h5
    · right
      obtain ⟨j, rfl⟩ : ∃ j, k = 7 + 6 * j := ⟨(k - 7) / 6, by omega⟩
      have ht2 : num t = num ((p * 7 - 1) / 3 + 2 * p * j) := by rw [numB hp6 rfl, hnum]
      have hteq : t = (p * 7 - 1) / 3 + 2 * p * j := num_inj ht2
      exact ⟨by lia, j, by lia⟩
    · left
      obtain ⟨j, rfl⟩ : ∃ j, k = 5 + 6 * j := ⟨(k - 5) / 6, by omega⟩
      have ht2 : num t = num ((p * 5 - 1) / 3 + 2 * p * j) := by rw [numA hp6 rfl, hnum]
      have hteq : t = (p * 5 - 1) / 3 + 2 * p * j := num_inj ht2
      exact ⟨by lia, j, by lia⟩

/-! ## Layer 4: the surviving bits are exactly the primes (sieve of Eratosthenes)

`markMaskK` clears composite bits alone, so prime bits survive (completeness). For soundness, a
composite `num t` has a smallest prime factor `q ≤ √(num t) ≤ sqrtN`; the loop reaches `q` while its
own bit still stands, so its `markMaskK` fires and clears `t`. -/

theorem num_mod6 {k : Nat} : num k % 6 = 1 ∨ num k % 6 = 5 := by grind [num]

theorem five_le_num {k : Nat} (hk : 1 ≤ k) : 5 ≤ num k := by grind [num]

/-- The loop's "is bit `j` set" test (`1 ≤ b &&& 2^j`) is `b.testBit j`. -/
theorem ble_one_and_eq {b j : Nat} :
    Nat.ble 1 (b &&& (1 <<< j)) = b.testBit j := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow]
  cases h : b.testBit j
  · simp only [Bool.toNat_false, Nat.zero_mul]; rfl
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact Nat.ble_eq_true_of_le Nat.one_le_two_pow

theorem sieveLoopK_succ_if {M bits start fuel : Nat} :
    sieveLoopK M bits start (fuel + 1)
      = if (sieveLoopK M bits start fuel).testBit (start + fuel)
        then markMaskK (sieveLoopK M bits start fuel) (num (start + fuel)) M
        else sieveLoopK M bits start fuel := by
  grind [sieveLoopK_succ, ble_one_and_eq, Bool.rec_eq]

/-- `markMaskK` (sieving by a wheel candidate `p ≥ 5`) preserves every bit whose number is prime:
the mask marks composite `num t = p * k` with `p, k ≥ 5`. -/
theorem markMaskK_preserves_prime {b p M t : Nat} (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hp5 : 5 ≤ p)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hprime : (num t).Prime) :
    (markMaskK b p M).testBit t = b.testBit t := by
  rw [testBit_markMaskK]
  suffices h : (buildMaskK p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3) 32).testBit t = false by
    simp [h]
  by_contra hc
  rw [Bool.not_eq_false, mask_iff p M t hp6 (by lia) hM ht] at hc
  obtain ⟨k, hk5, _, hnum⟩ := hc
  rcases hprime.eq_one_or_self_of_dvd p ⟨k, hnum⟩ with h1 | hself
  · lia
  · have hpk : p * 1 = p * k := by lia
    have : (1 : Nat) = k := Nat.eq_of_mul_eq_mul_left (by lia) hpk
    lia

/-- The loop preserves any prime bit: it stays at its initial value. -/
theorem sieveLoopK_preserves {M bits start fuel t : Nat} (hstart : 1 ≤ start)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hprime : (num t).Prime) :
    (sieveLoopK M bits start fuel).testBit t = bits.testBit t := by
  induction fuel with
  | zero => rfl
  | succ f ih =>
    rw [sieveLoopK_succ_if]
    split
    · rw [markMaskK_preserves_prime num_mod6 (five_le_num (by lia)) hM ht hprime, ih]
    · exact ih

/-- Completeness: every prime bit in range survives the sieve. -/
theorem sieve_prime_set {n sqrtN t : Nat} (ht1 : 1 ≤ t) (htM : t ≤ (n - 1) / 3)
    (hM : (n - 1) / 3 < 2 ^ 32) (hprime : (num t).Prime) :
    (sieveK n sqrtN).testBit t = true := by
  unfold sieveK
  change (sieveLoopK ((n - 1) / 3) (initK ((n - 1) / 3)) 1 ((sqrtN - 1) / 3)).testBit t = true
  grind [sieveLoopK_preserves, testBit_initK]

/-- If a prime index `j` in the processed range witnesses `num t = num j * m` (`m ≥ 5` coprime to
6), the sieve clears bit `t`. The bit at `j` still stands when the loop reaches it, so its
`markMaskK` fires, and every later step preserves the clear. -/
theorem sieveLoopK_clears {M start t j m : Nat} (hstart : 1 ≤ start)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hjprime : (num j).Prime) (hjt : j ≤ t)
    (hm5 : 5 ≤ m) (hm6 : m % 6 = 1 ∨ m % 6 = 5) (hnum : num t = num j * m) (hj_lo : start ≤ j) :
    ∀ fuel, j < start + fuel → (sieveLoopK M (initK M) start fuel).testBit t = false := by
  intro fuel
  induction fuel with
  | zero => intro h; lia
  | succ f ih =>
    intro hj_hi
    rw [sieveLoopK_succ_if]
    rcases Nat.lt_or_ge j (start + f) with hlt | hge
    · split <;> simp [testBit_markMaskK, ih hlt]
    · have hje : j = start + f := by lia
      have hset : (sieveLoopK M (initK M) start f).testBit (start + f) = true := by
        rw [sieveLoopK_preserves hstart hM (by lia) (hje ▸ hjprime), testBit_initK]
        lia
      rw [if_pos hset, testBit_markMaskK]
      have hmask : (buildMaskK (num (start + f)) M ((num (start + f) * 5 - 1) / 3)
          ((num (start + f) * 7 - 1) / 3) 32).testBit t = true := by
        rw [mask_iff (num (start + f)) M t num_mod6
          (by have := five_le_num (k := start + f) (by lia); lia) hM ht]
        exact ⟨m, hm5, hm6, by grind⟩
      simp [hmask]

/-! ### Soundness number theory -/

theorem num_wheel {q : Nat} (hq : q % 6 = 1 ∨ q % 6 = 5) : num ((q - 1) / 3) = q := by grind [num]

theorem num_coprime6 {t : Nat} : Nat.Coprime (num t) 6 := by
  have h := num_mod6 (k := t)
  change Nat.gcd (num t) 6 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases h with h | h <;> rw [h] <;> decide

theorem coprime6_mod {m : Nat} (h : Nat.Coprime m 6) : m % 6 = 1 ∨ m % 6 = 5 := by
  have hg : Nat.gcd (m % 6) 6 = 1 := by rw [← Nat.gcd_rec, Nat.gcd_comm]; exact h
  have hlt : m % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases (m % 6) <;> revert hg <;> decide

theorem prime_ge5_mod6 {q : Nat} (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  have h2 : q % 2 = 1 := Nat.odd_iff.mp (hq.eq_two_or_odd'.resolve_left (by lia))
  have h3 : q % 3 ≠ 0 := fun hh => by
    rcases hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hh) with h' | h' <;> lia
  lia

/-- For `1 ≤ t ≤ (n-1)/3` with `num t ≤ n ≤ sqrtN*sqrtN`, bit `t` of the sieve is set iff `num t`
is prime. -/
public theorem sieveK_testBit_iff (n sqrtN t : Nat) (ht1 : 1 ≤ t) (htM : t ≤ (n - 1) / 3)
    (hM : (n - 1) / 3 < 2 ^ 32) (hbound : num t ≤ n) (hsqrt : n ≤ sqrtN * sqrtN) :
    (sieveK n sqrtN).testBit t ↔ (num t).Prime := by
  refine ⟨fun hset => ?_, sieve_prime_set ht1 htM hM⟩
  by_contra hnp
  have h5 : 5 ≤ num t := five_le_num ht1
  have hnt2 : num t % 2 = 1 := by have := num_mod6 (k := t); omega
  have hnt3 : num t % 3 ≠ 0 := by have := num_mod6 (k := t); omega
  obtain ⟨q, hqprime, hqdvd, hqsq⟩ : ∃ q, q.Prime ∧ q ∣ num t ∧ q ^ 2 ≤ num t :=
    ⟨(num t).minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd _,
      Nat.minFac_sq_le_self (by omega) hnp⟩
  have hq2le : 2 ≤ q := hqprime.two_le
  have hq2 : q ≠ 2 := by rintro rfl; obtain ⟨c, hc⟩ := hqdvd; omega
  have hq3 : q ≠ 3 := by rintro rfl; obtain ⟨c, hc⟩ := hqdvd; omega
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hqprime.eq_two_or_odd'.resolve_left hq2)
  have hq5 : 5 ≤ q := by omega
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := prime_ge5_mod6 hqprime hq5
  obtain ⟨m, hm⟩ := hqdvd
  have hqm : q ≤ m := Nat.le_of_mul_le_mul_left (by rw [← pow_two]; omega) (by omega)
  have hm5 : 5 ≤ m := by omega
  have hmdvd : m ∣ num t := ⟨q, by grind⟩
  have hm6 : m % 6 = 1 ∨ m % 6 = 5 := coprime6_mod (num_coprime6.coprime_dvd_left hmdvd)
  have hnumjq : num ((q - 1) / 3) = q := num_wheel hq6
  have hjq1 : 1 ≤ (q - 1) / 3 := by omega
  have hnum2 : num t = num ((q - 1) / 3) * m := by grind
  have hqlt : q < num t := by nlinarith
  have hjqt : (q - 1) / 3 ≤ t := by
    by_contra! hc
    have := num_strictMono hc
    grind
  have hqsqrt : q ≤ sqrtN := by nlinarith
  have hjqfuel : (q - 1) / 3 < 1 + (sqrtN - 1) / 3 := by
    have hnj := hnumjq
    grind [num]
  have hcleared := sieveLoopK_clears (le_refl 1) hM htM
    (by rw [hnumjq]; exact hqprime) hjqt hm5 hm6 hnum2 hjq1 ((sqrtN - 1) / 3) hjqfuel
  unfold sieveK at hset
  change (sieveLoopK ((n - 1) / 3) (initK ((n - 1) / 3)) 1 ((sqrtN - 1) / 3)).testBit t = true
    at hset
  rw [hcleared] at hset
  exact Bool.noConfusion hset

/-! ### Reading a prime off a cached sieve -/

/-- From the numeric side-conditions (each as `Nat.ble … = true`), "bit `t` of the sieve literal
`lit` is set", and `numK t = p`, conclude `p` is prime. The kernel reads the bit from `lit`, and
`hEq : sieveK n sqrtN = lit`, the equation `run_sieve` proves, carries it back to the sieve. -/
public theorem prime_of_sieve_eq (n sqrtN t lit p : Nat) (hEq : sieveK n sqrtN = lit)
    (h1 : Nat.ble 1 t)
    (h2 : t.ble ((n.sub 1).div 3))
    (h3 : (((n.sub 1).div 3).add 1).ble (Nat.pow 2 32))
    (h4 : (numK t).ble n)
    (h5 : n.ble (sqrtN.mul sqrtN))
    (hbit : (bitVal lit t).beq 1)
    (hp : (numK t).beq p) :
    Nat.Prime p := by
  rw [← Nat.eq_of_beq_eq_true hp, numK_eq_num]
  refine (sieveK_testBit_iff n sqrtN t (Nat.le_of_ble_eq_true h1) (Nat.le_of_ble_eq_true h2)
    (Nat.le_of_ble_eq_true h3) (Nat.le_of_ble_eq_true h4) (Nat.le_of_ble_eq_true h5)).mp ?_
  rw [← bitVal_eq_one_iff, hEq]
  exact Nat.eq_of_beq_eq_true hbit

end PrimeCert.Sieve
