/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Polya.PrimePowers
public import PrimeCert.Polya.Field
public import PrimeCert.ForLean
public import Mathlib.Data.Nat.Bitwise

/-!
# What surviving the bit checks says about the packed primes

The state of `bitCheckLoopK` holds the previous field's sieve index above bit 0 and a flag in bit
0. The flag multiplies the previous one, so it survives only when every field passed every test:
each field is `1` or `5` modulo 6, its sieve index rises, and its sieve bit is set
(`bitCheckLoopK_spec`).
-/

namespace PrimeCert.Polya

open Nat

/-- The sieve index of a number coprime to 6. -/
@[expose] public def idx (q : ℕ) : ℕ := (q - 1) / 3

theorem bool_rec_beq (a b : ℕ) :
    (Nat.beq a b).rec (motive := fun _ => ℕ) 0 1 = if a = b then 1 else 0 := by
  cases h : Nat.beq a b
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

theorem bool_rec_ble (a b : ℕ) :
    (Nat.ble a b).rec (motive := fun _ => ℕ) 0 1 = if a ≤ b then 1 else 0 := by
  cases h : Nat.ble a b
  · refine (if_neg fun hle => ?_).symm
    rw [Nat.ble_eq_true_of_le hle] at h
    exact Bool.noConfusion h
  · rw [if_pos (Nat.le_of_ble_eq_true h)]

/-- One test in arithmetic form: the state becomes twice the index plus the flag. -/
theorem bitCheckStepK_eq (qs w lit st i : ℕ) :
    bitCheckStepK qs w lit st i
      = idx (fieldK qs w i) * 2 +
        (st % 2) * (if (fieldK qs w i) % 6 % 4 = 1 then 1 else 0) *
          (if st / 2 + 1 ≤ idx (fieldK qs w i) then 1 else 0) *
          ((lit >>> idx (fieldK qs w i)) % 2) := by
  simp only [bitCheckStepK, idx, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.sub_eq,
    Nat.add_eq, Nat.mul_eq, Nat.div_eq_div, Nat.mod_eq_mod, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, bool_rec_beq, bool_rec_ble,
    Nat.succ_eq_add_one]
  rfl

/-- Every field passed its tests, and the sieve indices strictly increase. -/
public theorem bitCheckLoopK_spec {qs w lit : ℕ} (fuel : ℕ)
    (h : bitCheckLoopK qs w lit 1 0 fuel % 2 = 1) :
    (∀ i < fuel, fieldK qs w i % 6 % 4 = 1 ∧ 0 < idx (fieldK qs w i) ∧
        (lit >>> idx (fieldK qs w i)) % 2 = 1) ∧
      (∀ i j, i < j → j < fuel → idx (fieldK qs w i) < idx (fieldK qs w j)) ∧
      (0 < fuel → bitCheckLoopK qs w lit 1 0 fuel / 2 = idx (fieldK qs w (fuel - 1))) := by
  induction fuel with
  | zero => exact ⟨by omega, by omega, by omega⟩
  | succ f ih =>
    rw [bitCheckLoopK_succ, Nat.zero_add, bitCheckStepK_eq] at h ⊢
    have hf1 : bitCheckLoopK qs w lit 1 0 f % 2 ≤ 1 := by omega
    have hf2 : (if fieldK qs w f % 6 % 4 = 1 then 1 else 0) ≤ 1 := by split <;> omega
    have hf3 : (if bitCheckLoopK qs w lit 1 0 f / 2 + 1 ≤ idx (fieldK qs w f) then 1 else 0) ≤ 1 :=
      by split <;> omega
    have hf4 : (lit >>> idx (fieldK qs w f)) % 2 ≤ 1 := by omega
    have hple : (bitCheckLoopK qs w lit 1 0 f % 2) *
        (if fieldK qs w f % 6 % 4 = 1 then 1 else 0) *
        (if bitCheckLoopK qs w lit 1 0 f / 2 + 1 ≤ idx (fieldK qs w f) then 1 else 0) *
        ((lit >>> idx (fieldK qs w f)) % 2) ≤ 1 :=
      le_trans (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hf1 hf2) hf3) hf4) (by omega)
    have hprod : (bitCheckLoopK qs w lit 1 0 f % 2) *
        (if fieldK qs w f % 6 % 4 = 1 then 1 else 0) *
        (if bitCheckLoopK qs w lit 1 0 f / 2 + 1 ≤ idx (fieldK qs w f) then 1 else 0) *
        ((lit >>> idx (fieldK qs w f)) % 2) = 1 := by omega
    have hok : bitCheckLoopK qs w lit 1 0 f % 2 = 1 := by
      by_contra hne
      have h0 : bitCheckLoopK qs w lit 1 0 f % 2 = 0 := by omega
      simp [h0] at hprod
    have hmod : fieldK qs w f % 6 % 4 = 1 := by
      by_contra hne
      rw [if_neg hne] at hprod
      simp at hprod
    have hrise : bitCheckLoopK qs w lit 1 0 f / 2 + 1 ≤ idx (fieldK qs w f) := by
      by_contra hne
      rw [if_neg hne] at hprod
      simp at hprod
    have hset : (lit >>> idx (fieldK qs w f)) % 2 = 1 := by
      by_contra hne
      have h0 : (lit >>> idx (fieldK qs w f)) % 2 = 0 := by omega
      simp [h0] at hprod
    rw [hprod] at h ⊢
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

end PrimeCert.Polya
