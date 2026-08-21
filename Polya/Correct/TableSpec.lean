/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Correct.HigherPowers
public import Polya.Correct.Lam

/-!
# The packed table holds exactly the prime powers

The two blocks of the packed table are checked against the sieve by three loops, and
`isPrimePowerTable_of_checks` turns what the checks say into `IsPrimePowerTable`: the primes from 5
upward come from `bitCheckLoopK` and `popcLoopK`, the rest from `hpLoopK`.
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (IsSieve num)

/-- The powers the second block collects are none of the primes from 5 upward. -/
theorem not_prime_five_le {p k v : ℕ} (hv : v = p ^ k) (hcase : p < 5 ∨ 2 ≤ k) :
    ¬ (v.Prime ∧ 5 ≤ v) := by
  rintro ⟨hvp, hv5⟩
  subst hv
  have hpk : Prime p ∧ k = 1 := prime_pow_iff.1 (Nat.prime_iff.1 hvp)
  rcases hcase with h | h
  · rw [hpk.2, Nat.pow_one] at hv5
    omega
  · omega

/-- The numbers the walk visits stay in range. -/
theorem num_le_of_lt_fuel {M fuel t : ℕ} (hfuel : 3 * fuel + 2 ≤ M) (ht : t < 1 + fuel) :
    num t ≤ M := by
  simp only [num]
  omega

/-- What the three loops together say about the packed table. -/
public theorem isPrimePowerTable_of_checks {qs w lit M np cnt chunks e fuel st hpSt : ℕ}
    (hsieve : IsSieve M lit)
    (hbitData : bitCheckLoopK qs w lit 1 0 np = st) (hflag : st % 2 = 1)
    (hnumtop : 0 < np → num (st / 2) ≤ M)
    (hpop : popcLoopK lit 0 0 chunks = np) (hchunks : (M - 1) / 3 < 64 * chunks)
    (hhp : hpLoopK lit M w e (powLoopK M w 3 1 (powLoopK M w 2 1 0 e) e) 1 fuel = hpSt)
    (hfuelup : M < (3 * fuel + 4) * (3 * fuel + 4)) (hfueldn : 3 * fuel + 2 ≤ M)
    (hMw : M < 2 ^ w) (hM64 : M < 2 ^ 64) (hMe : M < 2 ^ e)
    (hroom : e + e + e * fuel + e + 1 < 2 ^ 64)
    (hlink : qs / 2 ^ (w * np) = hpSt / 2 ^ 128) (hcnt : np + hpSt % 2 ^ 64 = cnt) :
    IsPrimePowerTable qs w M cnt := by
  have hflag' : bitCheckLoopK qs w lit 1 0 np % 2 = 1 := by rwa [hbitData]
  have htop' : 0 < np → num (bitCheckLoopK qs w lit 1 0 np / 2) ≤ M := by rwa [hbitData]
  obtain ⟨hp1, hp2, hp3⟩ := primeBlock_spec hsieve hflag' htop' hpop hchunks
  obtain ⟨c0, pw0, V0, hst0, hc0, hs0, hcp0, hi0⟩ := seed_spec lit hMw hM64 hMe (by omega)
  obtain ⟨c1, pw1, V1, hst1, hcc1, hc1le, hs1, hcp1, hi1⟩ :=
    hpLoopK_spec fuel hsieve hst0 hMw hM64 hMe (by omega) (le_refl 1)
      (fun t ht => num_le_of_lt_fuel hfueldn ht) hs0 hcp0 hi0
  rw [hhp] at hst1
  have hV1 : V1 = qs / 2 ^ (w * np) := by rw [hlink, hst1.vals_eq]
  have hc1eq : np + c1 = cnt := by rwa [← hst1.count_eq]
  have hentry : ∀ j, entryK V1 w j = entryK qs w (np + j) := fun j => by
    rw [hV1, entryK_shiftRight]
  refine ⟨fun q hq hqM => ?_, fun i hi => ?_, fun i₁ i₂ hi₁ hi₂ heq => ?_⟩
  · obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff q).1 hq
    by_cases hcase : 5 ≤ p ∧ k = 1
    · obtain ⟨hp5, rfl⟩ := hcase
      rw [Nat.pow_one] at hpk
      subst hpk
      obtain ⟨i, hi, hiq⟩ := hp2 p hp hp5 hqM
      exact ⟨i, by omega, hiq⟩
    · obtain ⟨j, hj, hjq⟩ := hcp1 q ((hpVal_iff hsieve hfuelup).2
        ⟨p, k, hp, by omega, hpk.symm, hqM, by omega⟩)
      refine ⟨np + j, by omega, ?_⟩
      rwa [← hentry j]
  · rcases Nat.lt_or_ge i np with hin | hin
    · obtain ⟨hprime, -, -⟩ := hp1 i hin
      exact (isPrimePow_nat_iff _).2 ⟨entryK qs w i, 1, hprime, by omega, Nat.pow_one _⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hin
      rw [← hentry j]
      obtain ⟨p, k, hp, hk, hvk, -, -⟩ := (hpVal_iff hsieve hfuelup).1 (hs1 j (by omega))
      exact (isPrimePow_nat_iff _).2 ⟨p, k, hp, by omega, hvk.symm⟩
  · have hcross : ∀ a b, a < np → np ≤ b → b < cnt → entryK qs w a ≠ entryK qs w b := by
      intro a b ha hb hbc heq'
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb
      rw [← hentry j] at heq'
      obtain ⟨p, k, hp, hk, hvk, -, hpcase⟩ := (hpVal_iff hsieve hfuelup).1 (hs1 j (by omega))
      obtain ⟨hprime, hfive, -⟩ := hp1 a ha
      rw [heq'] at hprime hfive
      exact not_prime_five_le hvk hpcase ⟨hprime, hfive⟩
    rcases Nat.lt_or_ge i₁ np with h₁ | h₁ <;> rcases Nat.lt_or_ge i₂ np with h₂ | h₂
    · exact hp3 i₁ i₂ h₁ h₂ heq
    · exact absurd heq (hcross i₁ i₂ h₁ h₂ hi₂)
    · exact absurd heq.symm (hcross i₂ i₁ h₂ h₁ hi₁)
    · obtain ⟨j₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
      obtain ⟨j₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
      rw [← hentry j₁, ← hentry j₂] at heq
      have := hi1 j₁ j₂ (by omega) (by omega) heq
      omega

end PrimeCert.Polya
