/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Correct.Parity
public import Polya.Theory.CardFactors
public import PrimeCert.PopCount

/-!
# The parity table holds the parity of `Ω`

`IsPrimePowerTable qs w M cnt` says the `cnt` entries of `qs` are exactly the prime powers at most
`M`, each appearing once. Under it, bit `n` of `lamK` is set exactly when `n` has an odd number of
prime factors counted with multiplicity (`testBit_lamK`), since the entries dividing `n` are the
prime powers dividing `n`, and there are `Ω n` of those.
-/

namespace PrimeCert.Polya

open ArithmeticFunction

/-- The `cnt` entries of `qs` are prime powers, distinct, and cover every prime power at most `M`.
A entry above `M` divides no number in the table, so the covering direction is the only one that
needs the bound. -/
@[expose] public def IsPrimePowerTable (qs w M cnt : ℕ) : Prop :=
  (∀ q, IsPrimePow q → q ≤ M → ∃ i < cnt, entryK qs w i = q) ∧
    (∀ i < cnt, IsPrimePow (entryK qs w i)) ∧
      ∀ i₁ i₂, i₁ < cnt → i₂ < cnt → entryK qs w i₁ = entryK qs w i₂ → i₁ = i₂

/-- Bit `n` of the parity table is set exactly when `Ω n` is odd. -/
public theorem testBit_lamK {qs w M r cnt n : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r) (hn : 0 < n) (hnM : n ≤ M) :
    (lamK qs w M r cnt).testBit n = decide (Odd (cardFactors n)) := by
  obtain ⟨hcover, hentry, hinj⟩ := htab
  have hstep : ∀ i < cnt, 0 < entryK qs w (0 + i) ∧ M < entryK qs w (0 + i) * 2 ^ r := by
    intro i hi
    rw [Nat.zero_add]
    have h2 : 2 ≤ entryK qs w i := (hentry i hi).two_le
    exact ⟨by omega, lt_of_lt_of_le hr (Nat.le_mul_of_pos_left _ (by omega))⟩
  have hcard : ({i ∈ Finset.range cnt | entryK qs w (0 + i) ∣ n}).card = cardFactors n := by
    rw [← card_primePow_divisors (n := n) (by omega)]
    refine Finset.card_bij (fun i _ => entryK qs w (0 + i)) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add] at hi ⊢
      exact ⟨Nat.mem_divisors.2 ⟨hi.2, by omega⟩, hentry i hi.1⟩
    · intro i₁ h₁ i₂ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add] at h₁ h₂
      exact hinj i₁ i₂ h₁.1 h₂.1 (by simpa using heq)
    · intro q hq
      simp only [Finset.mem_filter, Nat.mem_divisors] at hq
      obtain ⟨⟨hdvd, -⟩, hpp⟩ := hq
      have hqn : q ≤ n := Nat.le_of_dvd hn hdvd
      obtain ⟨i, hi, rfl⟩ := hcover q hpp (by omega)
      refine ⟨i, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add]
      exact ⟨hi, hdvd⟩
  rw [lamK, testBit_lamLoopK hnM hn hstep, hcard]
  simp

/-- Position `0` of the parity table is clear. -/
public theorem testBit_lamK_zero {qs w M r cnt : ℕ} (htab : IsPrimePowerTable qs w M cnt) :
    (lamK qs w M r cnt).testBit 0 = false := by
  obtain ⟨-, hentry, -⟩ := htab
  refine testBit_lamLoopK_zero (by simp) fun i hi => ?_
  rw [Nat.zero_add]
  have := (hentry i hi).two_le
  omega

/-- The set bits of the parity table below `p` count the numbers below `p` with an odd number of
prime factors. -/
public theorem bitSum_lamK {qs w M r cnt p : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r) (hp : p ≤ M + 1) :
    bitSum (lamK qs w M r cnt) p = ({n ∈ Finset.Icc 1 (p - 1) | Odd (cardFactors n)}).card := by
  rw [bitSum_eq_card]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hi, hbit⟩
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [testBit_lamK_zero htab] at hbit
      exact absurd hbit (by simp)
    · rw [testBit_lamK htab hr hipos (by omega)] at hbit
      exact ⟨⟨hipos, by omega⟩, by simpa using hbit⟩
  · rintro ⟨⟨hi1, hi2⟩, hodd⟩
    refine ⟨by omega, ?_⟩
    rw [testBit_lamK htab hr (by omega) (by omega)]
    simpa using hodd

end PrimeCert.Polya
