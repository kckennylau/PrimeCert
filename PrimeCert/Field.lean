/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Bits
public import Mathlib.Data.Nat.Bitwise

/-!
# Reading a packed field

A table is one natural number holding `w`-bit fields, lowest first, and `fieldK qs w i` reads field
`i` (`fieldK_eq_div_mod`). The loops build such a table one field at a time, so the lemmas here
cover writing field `i`: a clear field reads the value back (`fieldK_lor_shiftLeft_of_zero`), the
other fields keep their values (`fieldK_lor_shiftLeft_ne`), and the result stops below position
`w * (i + 1)` (`lor_shiftLeft_lt`). A table that stops below `w * i` has field `i` clear
(`fieldK_eq_zero_of_lt`), which is how the loops meet the first of these.
-/

namespace PrimeCert

open Nat

/-- A comparison of naturals scrutinised by `Bool.rec`, in `if` form. -/
public theorem bool_rec_beq_eq {α : Sort*} (a b : ℕ) (x y : α) :
    (Nat.beq a b).rec (motive := fun _ => α) x y = if a = b then y else x := by
  cases h : Nat.beq a b
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

/-- An order test of naturals scrutinised by `Bool.rec`, in `if` form. -/
public theorem bool_rec_ble_eq {α : Sort*} (a b : ℕ) (x y : α) :
    (Nat.ble a b).rec (motive := fun _ => α) x y = if a ≤ b then y else x := by
  cases h : Nat.ble a b
  · refine (if_neg fun hle => ?_).symm
    rw [Nat.ble_eq_true_of_le hle] at h
    exact Bool.noConfusion h
  · rw [if_pos (Nat.le_of_ble_eq_true h)]

/-- `fieldK qs w i` is `w` bits of `qs` read at position `w * i`. -/
public theorem fieldK_eq_div_mod (qs w i : ℕ) : fieldK qs w i = qs / 2 ^ (w * i) % 2 ^ w := by
  simp [fieldK, Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

/-- A field holds `w` bits. -/
public theorem fieldK_lt (qs w i : ℕ) : fieldK qs w i < 2 ^ w := by
  rw [fieldK_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Bit `j` of field `i`, for `j < w`, is bit `j + w * i` of the table. -/
@[simp] public theorem testBit_fieldK (qs w i j : ℕ) :
    (fieldK qs w i).testBit j = (decide (j < w) && qs.testBit (j + w * i)) := by
  rw [fieldK_eq_div_mod, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

/-- A table that stops below position `w * i` has field `i` clear. -/
public theorem fieldK_eq_zero_of_lt {t w i : ℕ} (ht : t < 2 ^ (w * i)) : fieldK t w i = 0 := by
  rw [fieldK_eq_div_mod, Nat.div_eq_of_lt ht, Nat.zero_mod]

/-- One field further along starts `w` positions higher. -/
theorem mul_succ_le_mul {w a b : ℕ} (h : a < b) : w * a + w ≤ w * b := by
  rw [← Nat.mul_succ]
  exact Nat.mul_le_mul_left w h

/-- Reading a field distributes over a bitwise or. -/
theorem fieldK_lor (a b w j : ℕ) : fieldK (a ||| b) w j = fieldK a w j ||| fieldK b w j := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp [Bool.and_or_distrib_left]

/-- A value written at field `i` reads back there. -/
theorem fieldK_shiftLeft_self {val w i : ℕ} (hv : val < 2 ^ w) :
    fieldK (val <<< (w * i)) w i = val := by
  rw [fieldK_eq_div_mod, Nat.shiftLeft_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
    Nat.mod_eq_of_lt hv]

/-- Every field other than `i` of a value written at field `i` is zero. -/
theorem fieldK_shiftLeft_ne {val w i j : ℕ} (hv : val < 2 ^ w) (hij : j ≠ i) :
    fieldK (val <<< (w * i)) w j = 0 := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rcases Nat.lt_or_ge b w with hb | hb
  · rcases Nat.lt_or_ge j i with h | h
    · have := mul_succ_le_mul (w := w) h
      simp [hb, Nat.testBit_shiftLeft, Nat.not_le.2 (by omega : b + w * j < w * i)]
    · have := mul_succ_le_mul (w := w) (by omega : i < j)
      have hzero : val.testBit (b + w * j - w * i) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hb, Nat.testBit_shiftLeft, hzero]
  · simp [Nat.not_lt.2 hb]

/-- Writing at field `i` gives field `j ≠ i` the value it has in `t`. -/
public theorem fieldK_lor_shiftLeft_ne {t val w i j : ℕ} (hv : val < 2 ^ w) (hij : j ≠ i) :
    fieldK (t ||| val <<< (w * i)) w j = fieldK t w j := by
  rw [fieldK_lor, fieldK_shiftLeft_ne hv hij, Nat.or_zero]

/-- Writing over a clear field reads the value back. -/
public theorem fieldK_lor_shiftLeft_of_zero {t val w i : ℕ} (ht : fieldK t w i = 0)
    (hv : val < 2 ^ w) : fieldK (t ||| val <<< (w * i)) w i = val := by
  rw [fieldK_lor, ht, fieldK_shiftLeft_self hv, Nat.zero_or]

/-- Shifting a table down by whole fields renumbers them. -/
public theorem fieldK_shiftRight (qs w n j : ℕ) :
    fieldK (qs / 2 ^ (w * n)) w j = fieldK qs w (n + j) := by
  rw [fieldK_eq_div_mod, fieldK_eq_div_mod, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add]

/-- A table built one field per step from an empty table at `start`: the fields it covers read back
the values written, and the fields outside stay clear. -/
public theorem fieldK_of_lor_chain {wb start : ℕ} {F t : ℕ → ℕ} (h0 : t 0 = 0)
    (hsucc : ∀ f, t (f + 1) = t f ||| F (start + f) <<< (wb * (start + f))) (fuel : ℕ)
    (hval : ∀ j, start ≤ j → j < start + fuel → F j < 2 ^ wb) :
    (∀ j, start ≤ j → j < start + fuel → fieldK (t fuel) wb j = F j) ∧
      ∀ j, (j < start ∨ start + fuel ≤ j) → fieldK (t fuel) wb j = 0 := by
  induction fuel with
  | zero =>
    refine ⟨by omega, fun j _ => ?_⟩
    rw [h0]
    exact fieldK_eq_zero_of_lt (Nat.two_pow_pos _)
  | succ f ih =>
    obtain ⟨ihfield, ihzero⟩ := ih fun j hj1 hj2 => hval j hj1 (by omega)
    have hlast : F (start + f) < 2 ^ wb := hval _ (by omega) (by omega)
    rw [hsucc f]
    refine ⟨fun j hj1 hj2 => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (start + f) with h | h
      · rw [fieldK_lor_shiftLeft_ne hlast (by omega)]
        exact ihfield j hj1 h
      · have hjf : j = start + f := by omega
        subst hjf
        exact fieldK_lor_shiftLeft_of_zero (ihzero (start + f) (by omega)) hlast
    · rw [fieldK_lor_shiftLeft_ne hlast (by omega)]
      exact ihzero j (by omega)

/-- The table with field `i` written stops below position `w * (i + 1)`. -/
public theorem lor_shiftLeft_lt {t val w i : ℕ} (ht : t < 2 ^ (w * i)) (hv : val < 2 ^ w) :
    (t ||| val <<< (w * i)) < 2 ^ (w * (i + 1)) := by
  have hle : w * i ≤ w * (i + 1) := Nat.mul_le_mul_left w (by omega)
  refine Nat.or_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega) hle)) ?_
  rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.pow_add,
    Nat.mul_comm (2 ^ (w * i)) (2 ^ w)]
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hv

end PrimeCert
