/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Bits
public import PrimeCert.Entry
public import PrimeCert.ForLean
public import PrimeCert.SieveCorrect
public import Mathlib.Data.Nat.Bitwise

/-!
# What surviving the bit checks says about the packed primes

The state of `bitCheckLoopK` holds the previous entry's sieve index above bit 0 and a flag in bit
0. The flag multiplies the previous one, so it survives only when every entry passed every test:
each entry is `1` or `5` modulo 6, its sieve index rises, and its sieve bit is set
(`bitCheckLoopK_spec`).
-/

namespace PrimeCert

/-- The sieve index of a number coprime to 6. -/
@[expose] public def idx (q : ℕ) : ℕ := (q - 1) / 3

/-- One test in arithmetic form: the state becomes twice the index plus the flag. -/
theorem bitCheckStepK_eq (qs w lit st i : ℕ) :
    bitCheckStepK qs w lit st i
      = idx (entryK qs w i) * 2 +
        (st % 2) * (if (entryK qs w i) % 6 % 4 = 1 then 1 else 0) *
          (if st / 2 + 1 ≤ idx (entryK qs w i) then 1 else 0) *
          ((lit >>> idx (entryK qs w i)) % 2) := by
  simp only [bitCheckStepK, idx, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.sub_eq,
    Nat.add_eq, Nat.mul_eq, Nat.div_eq_div, Nat.mod_eq_mod, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, bool_rec_beq_eq, bool_rec_ble_eq,
    Nat.succ_eq_add_one]
  rfl

/-- The flag a step carries is a product of four tests, each `0` or `1`, so an odd state means
every test passed. -/
theorem tests_of_flag {a b c d e : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (h : (e * 2 + a * b * c * d) % 2 = 1) : a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by grind

/-- Every entry passed its tests, and the sieve indices strictly increase. -/
public theorem bitCheckLoopK_spec {qs w lit : ℕ} (fuel : ℕ)
    (h : bitCheckLoopK qs w lit 1 0 fuel % 2 = 1) :
    (∀ i < fuel, entryK qs w i % 6 % 4 = 1 ∧ 0 < idx (entryK qs w i) ∧
        (lit >>> idx (entryK qs w i)) % 2 = 1) ∧
      (∀ i j, i < j → j < fuel → idx (entryK qs w i) < idx (entryK qs w j)) ∧
      (0 < fuel → bitCheckLoopK qs w lit 1 0 fuel / 2 = idx (entryK qs w (fuel - 1))) := by
  induction fuel with
  | zero => exact ⟨by omega, by omega, by omega⟩
  | succ f ih =>
    rw [bitCheckLoopK_succ, Nat.zero_add, bitCheckStepK_eq] at h ⊢
    obtain ⟨hok, hmodif, hriseif, hset⟩ := tests_of_flag (by omega) (by split <;> omega)
      (by split <;> omega) (by omega) h
    simp only [hok, hmodif, hriseif, hset, Nat.mul_one]
    have hmod : entryK qs w f % 6 % 4 = 1 := by simpa using hmodif
    have hrise : bitCheckLoopK qs w lit 1 0 f / 2 + 1 ≤ idx (entryK qs w f) := by
      simpa using hriseif
    obtain ⟨ihtests, ihmono, ihtop⟩ := ih hok
    refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun _ => ?_⟩
    · rcases Nat.lt_or_ge i f with hif | hif
      · exact ihtests i hif
      · have : i = f := by omega
        subst this
        exact ⟨hmod, by omega, hset⟩
    · rcases Nat.lt_or_ge j f with hjf | hjf
      · exact ihmono i j hij hjf
      · have hjf' : j = f := by omega
        rw [hjf']
        have hfpos : 0 < f := by omega
        rw [ihtop hfpos] at hrise
        rcases Nat.lt_or_ge i (f - 1) with hi1 | hi1
        · exact lt_of_lt_of_le (ihmono i (f - 1) hi1 (by omega)) (by omega)
        · have hif1 : i = f - 1 := by omega
          rw [hif1]
          omega
    · simp only [Nat.add_sub_cancel]
      omega

/-! ## Reading the primes off the sieve -/

open PrimeCert.Sieve (IsSieve num)

/-- The index inverts `num` on the numbers coprime to 6. -/
public theorem num_idx {q : ℕ} (hq : q % 6 = 1 ∨ q % 6 = 5) : num (idx q) = q := by grind [num, idx]

/-- A set position read as a shift and a remainder. -/
public theorem testBit_iff_shiftRight_mod_two {v t : ℕ} : v.testBit t ↔ (v >>> t) % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp

/-- A entry that passed its tests is the number at its sieve index. -/
public theorem num_idx_entryK {qs w lit cnt : ℕ} (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    {i : ℕ} (hi : i < cnt) : num (idx (entryK qs w i)) = entryK qs w i := by
  obtain ⟨htests, -, -⟩ := bitCheckLoopK_spec cnt h
  obtain ⟨hmod, -, -⟩ := htests i hi
  exact num_idx (by omega)

/-- A entry that passed its tests and sits inside the sieve's range is a prime. -/
public theorem entryK_prime {qs w lit M cnt : ℕ} (hsieve : IsSieve M lit)
    (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    {i : ℕ} (hi : i < cnt) (hbound : entryK qs w i ≤ M) : (entryK qs w i).Prime := by
  obtain ⟨htests, -, -⟩ := bitCheckLoopK_spec cnt h
  obtain ⟨-, hpos, hset⟩ := htests i hi
  have hnum := num_idx_entryK h hi
  have hprime := (hsieve _ (by omega) (by rw [hnum]; exact hbound)).1
    (testBit_iff_shiftRight_mod_two.2 hset)
  rwa [hnum] at hprime

/-- A strictly increasing map is injective below the bound. -/
public theorem eq_of_mono {f : ℕ → ℕ} {n : ℕ} (hmono : ∀ i j, i < j → j < n → f i < f j)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : f a = f b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hab (Nat.ne_of_lt (hmono a b h hb))
  · exact h
  · exact absurd hab.symm (Nat.ne_of_lt (hmono b a h ha))

/-- The entries that passed are distinct: their sieve indices rise. -/
public theorem entryK_injOn {qs w lit cnt : ℕ} (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    {i j : ℕ} (hi : i < cnt) (hj : j < cnt) (heq : entryK qs w i = entryK qs w j) : i = j := by
  obtain ⟨-, hmono, -⟩ := bitCheckLoopK_spec cnt h
  exact eq_of_mono hmono hi hj (congrArg idx heq)

end PrimeCert
