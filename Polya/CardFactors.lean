/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Prime powers dividing a number

`Ω n` counts the prime factors of `n` with multiplicity, and the prime powers dividing `n` are the
`p ^ k` with `1 ≤ k ≤ v_p(n)`, so there are `∑_p v_p(n) = Ω n` of them
(`card_primePow_divisors`). This is what makes one exclusive-or per prime power give the parity of
`Ω`.
-/

namespace PrimeCert.Polya

open ArithmeticFunction

/-- The prime powers dividing `n` are as many as the prime factors of `n` counted with
multiplicity. -/
public theorem card_primePow_divisors {n : ℕ} (hn : n ≠ 0) :
    ({q ∈ n.divisors | IsPrimePow q}).card = cardFactors n := by
  have hbi : {q ∈ n.divisors | IsPrimePow q}
      = n.primeFactors.biUnion fun p => (Finset.Icc 1 (n.factorization p)).image (p ^ ·) := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hpp⟩
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hpp
      have hple : k ≤ n.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).1 hdvd
      exact ⟨p, ⟨hp, dvd_trans (dvd_pow_self p (by omega)) hdvd, hn⟩, k, ⟨hk, hple⟩, rfl⟩
    · rintro ⟨p, ⟨hp, -, -⟩, k, ⟨hk, hple⟩, rfl⟩
      exact ⟨⟨(Nat.Prime.pow_dvd_iff_le_factorization hp hn).2 hple, hn⟩,
        (isPrimePow_nat_iff _).2 ⟨p, k, hp, by omega, rfl⟩⟩
  have hdisj : ∀ p ∈ n.primeFactors, ∀ p' ∈ n.primeFactors, p ≠ p' →
      Disjoint ((Finset.Icc 1 (n.factorization p)).image (p ^ ·))
        ((Finset.Icc 1 (n.factorization p')).image (p' ^ ·)) := by
    intro p hp p' hp' hne
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_Icc]
    rintro q ⟨k, ⟨hk, -⟩, rfl⟩ ⟨k', ⟨hk', -⟩, heq⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpp' : p'.Prime := Nat.prime_of_mem_primeFactors hp'
    exact hne ((Nat.prime_dvd_prime_iff_eq hpp' hpp).1
      (hpp'.dvd_of_dvd_pow (heq ▸ dvd_pow_self p' (by omega)))).symm
  rw [hbi, Finset.card_biUnion hdisj, cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hpp.two_le), Nat.card_Icc]
  omega

end PrimeCert.Polya
