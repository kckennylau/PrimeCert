/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Polya.Parity
public import PrimeCert.Polya.CardFactors

/-!
# The parity table holds the parity of `Ω`

`IsPrimePowerTable qs w M cnt` says the `cnt` fields of `qs` are exactly the prime powers at most
`M`, each appearing once. Under it, bit `n` of `lamK` is set exactly when `n` has an odd number of
prime factors counted with multiplicity (`testBit_lamK`), since the fields dividing `n` are the
prime powers dividing `n`, and there are `Ω n` of those.
-/

namespace PrimeCert.Polya

open ArithmeticFunction

/-- The `cnt` fields of `qs` are exactly the prime powers at most `M`, each appearing once. -/
@[expose] public def IsPrimePowerTable (qs w M cnt : ℕ) : Prop :=
  (∀ q, (IsPrimePow q ∧ q ≤ M) ↔ ∃ i < cnt, fieldK qs w i = q) ∧
    ∀ i₁ i₂, i₁ < cnt → i₂ < cnt → fieldK qs w i₁ = fieldK qs w i₂ → i₁ = i₂

/-- Bit `n` of the parity table is set exactly when `Ω n` is odd. -/
public theorem testBit_lamK {qs w M r cnt n : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r) (hn : 0 < n) (hnM : n ≤ M) :
    (lamK qs w M r cnt).testBit n = decide (Odd (cardFactors n)) := by
  obtain ⟨hspec, hinj⟩ := htab
  have hfield : ∀ i, i < cnt → IsPrimePow (fieldK qs w i) ∧ fieldK qs w i ≤ M :=
    fun i hi => (hspec _).2 ⟨i, hi, rfl⟩
  have hstep : ∀ i < cnt, 0 < fieldK qs w (0 + i) ∧ M < fieldK qs w (0 + i) * 2 ^ r := by
    intro i hi
    obtain ⟨hpp, -⟩ := hfield i hi
    rw [Nat.zero_add]
    have h2 : 2 ≤ fieldK qs w i := hpp.two_le
    refine ⟨by omega, lt_of_lt_of_le hr ?_⟩
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hcard : ({i ∈ Finset.range cnt | fieldK qs w (0 + i) ∣ n}).card = cardFactors n := by
    rw [← card_primePow_divisors (n := n) (by omega)]
    refine Finset.card_bij (fun i _ => fieldK qs w (0 + i)) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add] at hi ⊢
      exact ⟨Nat.mem_divisors.2 ⟨hi.2, by omega⟩, (hfield i hi.1).1⟩
    · intro i₁ h₁ i₂ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add] at h₁ h₂
      exact hinj i₁ i₂ h₁.1 h₂.1 (by simpa using heq)
    · intro q hq
      simp only [Finset.mem_filter, Nat.mem_divisors] at hq
      obtain ⟨⟨hdvd, -⟩, hpp⟩ := hq
      have hqn : q ≤ n := Nat.le_of_dvd hn hdvd
      obtain ⟨i, hi, rfl⟩ := (hspec q).1 ⟨hpp, by omega⟩
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add]; exact ⟨hi, hdvd⟩,
        by simp⟩
  rw [lamK, testBit_lamLoopK hnM hn hstep, hcard]
  simp

end PrimeCert.Polya
