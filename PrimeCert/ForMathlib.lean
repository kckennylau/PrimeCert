/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Pairwise
public import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-! # Lemmas destined for Mathlib

General-purpose facts about `Nat.ModEq`, `multiplicity`, and primality used by the
certificate proofs. None of these are specific to primality certificates; they are collected
here as candidates for upstreaming to Mathlib.
-/

public theorem Nat.prime_iff_not_exists_mul_eq' (p : ℕ) :
    Nat.Prime p ↔ 2 ≤ p ∧ ¬∃ m n, 2 ≤ m ∧ m < p ∧ 2 ≤ n ∧ n < p ∧ m * n = p := by
  rw [prime_iff_not_exists_mul_eq]
  refine and_congr_right fun hp ↦ not_congr <| exists_congr fun m ↦ exists_congr fun n ↦ ?_
  refine ⟨fun ⟨hmp, hnp, hmnp⟩ ↦ ⟨?_, hmp, ?_, hnp, hmnp⟩, by tauto⟩
  · by_contra hm; interval_cases m <;> lia
  · by_contra hn; interval_cases n <;> lia

theorem Nat.modEq_finset_prod_iff {a b : ℕ} {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (co : (s : Set ι).Pairwise (Coprime.onFun e)) :
    a ≡ b [MOD ∏ i ∈ s, e i] ↔ ∀ i ∈ s, a ≡ b [MOD e i] := by
  classical
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  rw [List.prod_toFinset e hl, Nat.modEq_list_map_prod_iff]
  · simp_rw [List.mem_toFinset]
  · rwa [← List.pairwise_iff_coe_toFinset_pairwise hl]

public theorem Nat.modEq_iff_forall_prime_dvd {a b n : ℕ} :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] := by
  by_cases hn₀ : n = 0
  · subst hn₀
    simp_rw [modEq_zero_iff, dvd_zero, true_imp_iff]
    constructor
    · rintro rfl; exact fun _ _ ↦ by rfl
    · intro h
      obtain ⟨p, hbp, hp⟩ := exists_infinite_primes (a + b + 1)
      specialize h p hp
      rw [multiplicity_zero, pow_one] at h
      exact h.eq_of_lt_of_lt (by linarith) (by linarith)
  · conv_lhs => rw [← prod_factorization_pow_eq_self hn₀]
    rw [Finsupp.prod, modEq_finset_prod_iff]
    · simp_rw [support_factorization, mem_primeFactors_of_ne_zero hn₀, and_comm, and_imp]
      refine forall_congr' fun p ↦ imp_congr_right fun hpn ↦ imp_congr_right fun hp ↦ ?_
      rw [multiplicity_eq_factorization hp hn₀]
    · grind [support_factorization, coprime_pow_primes, Set.Pairwise]

public theorem Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div
    {q n x : ℕ} (hq : q.Prime) (hxn : x ∣ n) (hxnq : ¬ x ∣ n / q) :
    q ^ multiplicity q n ∣ x := by
  by_cases hqn : q ∣ n
  · obtain ⟨n, rfl⟩ := hqn
    rw [Nat.mul_div_cancel_left _ hq.pos] at hxnq
    by_cases hn₀ : n = 0
    · subst hn₀; exact (hxnq <| dvd_zero _).elim
    have hqn₀ : q * n ≠ 0 := mul_ne_zero hq.ne_zero hn₀
    have hx₀ : x ≠ 0 := by rintro rfl; exact hqn₀ <| zero_dvd_iff.mp hxn
    rw [← Nat.factorization_le_iff_dvd hx₀ hn₀] at hxnq
    rw [← Nat.factorization_le_iff_dvd hx₀ hqn₀] at hxn
    rw [Nat.factorization_mul hq.ne_zero hn₀, hq.factorization, add_comm] at hxn
    refine pow_dvd_of_le_multiplicity ?_
    rw [multiplicity_eq_factorization hq hqn₀, multiplicity_eq_factorization hq hx₀,
      Nat.factorization_mul hq.ne_zero hn₀, Finsupp.add_apply, hq.factorization,
      Finsupp.single_apply, if_pos rfl, add_comm]
    refine le_of_not_gt fun h ↦ hxnq fun p ↦ ?_
    by_cases hpq : p = q
    · subst hpq; exact Nat.lt_succ_iff.mp h
    convert hxn p using 1
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hpq), add_zero]
  · rw [multiplicity_eq_zero.mpr hqn, pow_zero]
    exact one_dvd _

public theorem Nat.modEq_one_of_dvd_of_prime (n b : ℕ)
    (prime : ∀ p, Nat.Prime p → p ∣ n → p ≡ 1 [MOD b])
    (d : ℕ) (hdn : d ∣ n) : d ≡ 1 [MOD b] := by
  by_cases hn : n = 0
  · have := prime 2 prime_two <| hn ▸ dvd_zero _
    rw [ModEq.comm, modEq_iff_dvd' (by lia), dvd_one] at this
    exact this ▸ modEq_one
  have hd : d ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hdn; lia
  rw [← prod_factorization_pow_eq_self hd, Finsupp.prod,
    ← Finset.prod_const_one (s := d.factorization.support)]
  refine Nat.ModEq.prod fun p hp ↦ ?_
  rw [support_factorization, mem_primeFactors] at hp
  exact ((prime p hp.1 (hp.2.1.trans hdn)).pow _).trans <| by simp; rfl

public theorem Nat.add_sq_eq_dist_sq_add_four_mul (c d : ℕ) :
    (c + d) ^ 2 = (max c d - min c d) ^ 2 + 4 * (c * d) := by
  wlog h : c ≤ d
  · rw [add_comm, max_comm, min_comm, mul_comm c d]; exact this d c (by order)
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp h
  rw [max_eq_right h, min_eq_left h, Nat.add_sub_cancel_left]
  ring
