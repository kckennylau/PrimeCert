/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Summatory
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The recurrence for the summatory Liouville function

`∑_{d ∣ n} λ d` is `1` on squares and `0` elsewhere (`sum_divisors_liouville`), so summing over
`n ≤ v` and exchanging the order of summation gives `∑_{k = 1}^{v} L ⌊v/k⌋ = ⌊√v⌋`
(`sum_L_div`). Isolating `k = 1` gives `L v = ⌊√v⌋ - ∑_{k = 2}^{v} L ⌊v/k⌋` (`L_eq_sqrt_sub`).
-/

namespace PrimeCert.Polya

open ArithmeticFunction Finset

/-! ## The divisor sum of the Liouville function -/

/-- Alternating signs over an interval of even length cancel in pairs. -/
private lemma sum_neg_one_pow (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i = if Even k then 1 else 0 := by
  by_cases h : Even k <;> simp [neg_one_geom_sum, Nat.even_add_one, h]

/-- A positive natural number is a square exactly when every exponent in its factorization is
even. -/
public theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp only [Finsupp.add_apply]
    exact ⟨_, rfl⟩
  · intro h
    refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    obtain ⟨m, hm⟩ := h p
    congr 1
    omega

/-- The Liouville function summed over the divisors of `n`: `1` when `n` is a square, `0`
otherwise. -/
public theorem sum_divisors_liouville {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, liouville d = if IsSquare n then 1 else 0 := by
  have hmul : ((zeta : ArithmeticFunction ℤ) * liouville).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul isMultiplicative_liouville
  have hpow : ∀ p k : ℕ, p.Prime →
      ((zeta : ArithmeticFunction ℤ) * liouville) (p ^ k) = if Even k then 1 else 0 := by
    intro p k hp
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, ← sum_neg_one_pow k]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
  rw [← coe_zeta_mul_apply, hmul.multiplicative_factorization _ hn, Finsupp.prod]
  by_cases hsq : IsSquare n
  · rw [if_pos hsq]
    refine Finset.prod_eq_one fun p hp => ?_
    rw [hpow p _ (Nat.prime_of_mem_primeFactors (by simpa using hp)),
      if_pos ((isSquare_iff_even_factorization hn).1 hsq p)]
  · rw [if_neg hsq]
    obtain ⟨p, hp⟩ : ∃ p, ¬ Even (n.factorization p) := by
      by_contra h
      exact hsq ((isSquare_iff_even_factorization hn).2 (by simpa using h))
    have hmem : p ∈ n.factorization.support := by
      simp only [Finsupp.mem_support_iff]
      rintro h0
      rw [h0] at hp
      exact hp ⟨0, rfl⟩
    refine Finset.prod_eq_zero hmem ?_
    rw [hpow p _ (Nat.prime_of_mem_primeFactors (by simpa using hmem)), if_neg hp]

/-! ## The identity and the recurrence -/

/-- The squares in `1 … v` are the `⌊√v⌋` numbers `j * j` with `1 ≤ j ≤ ⌊√v⌋`. -/
public theorem sum_isSquare (v : ℕ) :
    ∑ n ∈ Finset.Ioc 0 v, (if IsSquare n then (1 : ℤ) else 0) = Nat.sqrt v := by
  rw [Finset.sum_boole]
  congr 1
  have himg : {n ∈ Finset.Ioc 0 v | IsSquare n}
      = (Finset.Icc 1 (Nat.sqrt v)).image (fun j => j * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn0, hnv⟩, r, rfl⟩
      exact ⟨r, ⟨by nlinarith, Nat.le_sqrt.2 hnv⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨⟨by positivity, Nat.le_sqrt.1 hj2⟩, j, rfl⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by nlinarith [h]),
    Nat.card_Icc]
  simp

/-- Exchanging the order of summation in `∑_{n ≤ v} ∑_{d ∣ n} λ d`. -/
public theorem sum_L_div (v : ℕ) : ∑ k ∈ Finset.Ioc 0 v, L (v / k) = Nat.sqrt v := by
  have h := sum_Ioc_mul_eq_sum_sum (zeta : ArithmeticFunction ℤ) liouville v
  have hL : ∑ n ∈ Finset.Ioc 0 v,
      (zeta : ArithmeticFunction ℤ) n * ∑ m ∈ Finset.Ioc 0 (v / n), liouville m
        = ∑ k ∈ Finset.Ioc 0 v, L (v / k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by simp only [Finset.mem_Ioc] at hk; omega
    rw [natCoe_apply, zeta_apply_ne hk0, Nat.cast_one, one_mul, L_eq_sum_Ioc]
  have hS : ∑ n ∈ Finset.Ioc 0 v, ((zeta : ArithmeticFunction ℤ) * liouville) n
      = ∑ n ∈ Finset.Ioc 0 v, (if IsSquare n then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by simp only [Finset.mem_Ioc] at hn; omega
    rw [coe_zeta_mul_apply, sum_divisors_liouville hn0]
  rw [← hL, ← h, hS, sum_isSquare]

/-- The recurrence the computation evaluates: `L v` from the values at the quotients `⌊v/k⌋`. -/
public theorem L_eq_sqrt_sub {v : ℕ} (hv : 0 < v) :
    L v = Nat.sqrt v - ∑ k ∈ Finset.Ioc 1 v, L (v / k) := by
  have hsplit : ∑ k ∈ Finset.Ioc 0 1, L (v / k) + ∑ k ∈ Finset.Ioc 1 v, L (v / k)
      = ∑ k ∈ Finset.Ioc 0 v, L (v / k) := Finset.sum_Ioc_consecutive _ (by omega) hv
  have h1 : (Finset.Ioc 0 1 : Finset ℕ) = {1} := rfl
  rw [sum_L_div, h1, Finset.sum_singleton, Nat.div_one] at hsplit
  omega

end PrimeCert.Polya
