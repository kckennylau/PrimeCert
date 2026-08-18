/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Field
public import Polya.PowerDefs

import Mathlib.Tactic.Ring

/-!
# The packed state of the power collection

The state of `powStepK` holds a count of collected values in its low 64 bits, the running power in
the next 64, and the values as `w`-bit fields above bit 128 (`IsPowState`). One step appends the
next power of the base while it stays below the cutoff (`powStepK_of_le`), and `powLoopK` appends
the powers `seed * q ^ 1, …, seed * q ^ m` for the largest such `m` (`powLoopK_spec`).
-/

namespace PrimeCert.Polya

/-! ### Writing a field by addition -/

/-- Writing above a table adds, since the two parts share no bits. -/
theorem add_mul_eq_lor {V val w c : ℕ} (hV : V < 2 ^ (w * c)) :
    V + val * 2 ^ (w * c) = V ||| val <<< (w * c) := by
  rw [Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hV, Nat.lor_comm]

/-- Fields other than the one being written keep their values. -/
theorem fieldK_add_mul_ne {V val w c j : ℕ} (hV : V < 2 ^ (w * c)) (hval : val < 2 ^ w)
    (hj : j ≠ c) : fieldK (V + val * 2 ^ (w * c)) w j = fieldK V w j := by
  rw [add_mul_eq_lor hV, fieldK_lor_shiftLeft_ne hval hj]

/-- The value written reads back from its own field. -/
theorem fieldK_add_mul_self {V val w c : ℕ} (hV : V < 2 ^ (w * c)) (hval : val < 2 ^ w) :
    fieldK (V + val * 2 ^ (w * c)) w c = val := by
  rw [add_mul_eq_lor hV, fieldK_lor_shiftLeft_of_zero (fieldK_eq_zero_of_lt hV) hval]

/-- The table with one more value written stops below position `w * (c + 1)`. -/
theorem add_mul_two_pow_lt {V val w c : ℕ} (hV : V < 2 ^ (w * c)) (hval : val < 2 ^ w) :
    V + val * 2 ^ (w * c) < 2 ^ (w * (c + 1)) := by
  rw [add_mul_eq_lor hV]
  exact lor_shiftLeft_lt hV hval

/-! ### The state -/

/-- The state of the collection: `c` values packed in `V`, and a running power `pw`. -/
@[expose] public def IsPowState (w st c pw V : ℕ) : Prop :=
  st = c + 2 ^ 64 * pw + 2 ^ 128 * V ∧ c < 2 ^ 64 ∧ pw < 2 ^ 64 ∧ V < 2 ^ (w * c)

/-- The count, the running power and the values read back off a state. -/
public theorem IsPowState.split {w st c pw V : ℕ} (h : IsPowState w st c pw V) :
    st % 2 ^ 64 = c ∧ st / 2 ^ 64 % 2 ^ 64 = pw ∧ st / 2 ^ 128 = V := by
  obtain ⟨hst, hc, hpw, -⟩ := h
  omega

/-- The count occupies the bottom 64 bits. -/
public theorem IsPowState.count_eq {w st c pw V : ℕ} (h : IsPowState w st c pw V) :
    st % 2 ^ 64 = c := h.split.1

/-- The running power occupies bits 64 to 127. -/
theorem IsPowState.pow_eq {w st c pw V : ℕ} (h : IsPowState w st c pw V) :
    st / 2 ^ 64 % 2 ^ 64 = pw := h.split.2.1

/-- The values sit above bit 128, so they read back by one shift. -/
public theorem IsPowState.vals_eq {w st c pw V : ℕ} (h : IsPowState w st c pw V) :
    st / 2 ^ 128 = V := h.split.2.2

/-! ### One step -/

/-- One step in arithmetic form. -/
theorem powStepK_eq (M w q st : ℕ) :
    powStepK M w q st =
      if st / 2 ^ 64 % 2 ^ 64 * q ≤ M then
        st + 1 + (st / 2 ^ 64 % 2 ^ 64 * q - st / 2 ^ 64 % 2 ^ 64) * 2 ^ 64 +
          st / 2 ^ 64 % 2 ^ 64 * q * 2 ^ (128 + w * (st % 2 ^ 64))
      else st := by
  simp only [powStepK, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.and_two_pow_sub_one_eq_mod, bool_rec_ble_eq]

/-- A step below the cutoff appends the next power. -/
theorem powStepK_of_le {M w q st c pw V : ℕ} (h : IsPowState w st c pw V) (hq : 1 ≤ q)
    (hle : pw * q ≤ M) (hM : M < 2 ^ w) (hM64 : M < 2 ^ 64) (hc : c + 1 < 2 ^ 64) :
    IsPowState w (powStepK M w q st) (c + 1) (pw * q) (V + pw * q * 2 ^ (w * c)) := by
  rw [powStepK_eq, h.pow_eq, h.count_eq, if_pos hle]
  obtain ⟨hst, hc64, hpw64, hV⟩ := h
  obtain ⟨d, hd⟩ : ∃ d, pw * q = pw + d := ⟨pw * q - pw, by
    have := Nat.le_mul_of_pos_right pw (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    omega⟩
  refine ⟨?_, by omega, by omega, add_mul_two_pow_lt hV (by omega)⟩
  rw [hst, hd, Nat.pow_add, Nat.add_sub_cancel_left]
  ring

/-- A step above the cutoff returns its input state. -/
theorem powStepK_of_gt {M w q st c pw V : ℕ} (h : IsPowState w st c pw V) (hgt : M < pw * q) :
    powStepK M w q st = st := by rw [powStepK_eq, IsPowState.pow_eq h, if_neg (by omega)]

/-! ### The loop -/

/-- Entering the loop replaces the running power by the seed. -/
theorem powLoopK_zero_eq (M w q seed st : ℕ) :
    powLoopK M w q seed st 0 = st - st / 2 ^ 64 % 2 ^ 64 * 2 ^ 64 + seed * 2 ^ 64 := by
  simp only [powLoopK, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem powLoopK_succ_eq (M w q seed st fuel : ℕ) :
    powLoopK M w q seed st (fuel + 1) = powStepK M w q (powLoopK M w q seed st fuel) := rfl

theorem powLoopK_zero {M w q seed st c pw V : ℕ} (h : IsPowState w st c pw V)
    (hseed : seed < 2 ^ 64) : IsPowState w (powLoopK M w q seed st 0) c seed V := by
  obtain ⟨hst, hc64, hpw64, hV⟩ := h
  have harith : st - st / 2 ^ 64 % 2 ^ 64 * 2 ^ 64 = c + 2 ^ 128 * V := by omega
  rw [powLoopK_zero_eq, harith]
  exact ⟨by ring, hc64, hseed, hV⟩

/-- After `fuel` steps the loop has appended `seed * q ^ 1, …, seed * q ^ m`, where `m` is the
largest exponent whose power stays below the cutoff, or `fuel` if they all do. -/
public theorem powLoopK_spec {M w q seed st c pw V : ℕ} (fuel : ℕ) (h : IsPowState w st c pw V)
    (hq : 2 ≤ q) (hseed : seed < 2 ^ 64) (hM : M < 2 ^ w) (hM64 : M < 2 ^ 64)
    (hroom : c + fuel + 1 < 2 ^ 64) :
    ∃ m ≤ fuel, ∃ V', IsPowState w (powLoopK M w q seed st fuel) (c + m) (seed * q ^ m) V' ∧
      (∀ j < c, fieldK V' w j = fieldK V w j) ∧
        (∀ j < m, fieldK V' w (c + j) = seed * q ^ (j + 1)) ∧
          (∀ j < m, seed * q ^ (j + 1) ≤ M) ∧ (m < fuel → M < seed * q ^ (m + 1)) := by
  induction fuel with
  | zero =>
    refine ⟨0, le_rfl, V, ?_, fun j _ => rfl, by omega, by omega, by omega⟩
    simpa using powLoopK_zero h hseed
  | succ f ih =>
    obtain ⟨m, hmf, V', hstate, hbelow, hfields, hle, htop⟩ := ih (by omega)
    rw [powLoopK_succ_eq]
    obtain ⟨hst', hc', hpw', hV'⟩ := hstate
    have hpow : seed * q ^ m * q = seed * q ^ (m + 1) := by rw [Nat.pow_succ]; ring
    rcases Nat.lt_or_ge M (seed * q ^ m * q) with hgt | hnext
    · refine ⟨m, by omega, V', ?_, hbelow, hfields, hle, fun _ => ?_⟩
      · rw [powStepK_of_gt ⟨hst', hc', hpw', hV'⟩ hgt]
        exact ⟨hst', hc', hpw', hV'⟩
      · rw [← hpow]
        exact hgt
    · have hstep := powStepK_of_le ⟨hst', hc', hpw', hV'⟩ (by omega) hnext hM hM64 (by omega)
      rw [hpow] at hstep
      refine ⟨m + 1, by omega, V' + seed * q ^ (m + 1) * 2 ^ (w * (c + m)), ?_, fun j hj => ?_,
        fun j hj => ?_, fun j hj => ?_, fun hlt => ?_⟩
      · rw [← Nat.add_assoc]
        exact hstep
      · rw [fieldK_add_mul_ne hV' (by rw [← hpow]; omega) (by omega)]
        exact hbelow j hj
      · rcases Nat.lt_or_ge j m with hjm | hjm
        · rw [fieldK_add_mul_ne hV' (by rw [← hpow]; omega) (by omega)]
          exact hfields j hjm
        · have hjm' : j = m := by omega
          subst hjm'
          exact fieldK_add_mul_self hV' (by rw [← hpow]; omega)
      · rcases Nat.lt_or_ge j m with hjm | hjm
        · exact hle j hjm
        · have hjm' : j = m := by omega
          subst hjm'
          rwa [← hpow]
      · exact absurd (htop (by omega)) (by rw [← hpow]; omega)

end PrimeCert.Polya
