/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Polya
public import Mathlib.Data.Nat.Bitwise

/-!
# Reading a packed field

A table is one natural number holding `w`-bit fields, lowest first, and `fieldK qs w i` reads field
`i` (`fieldK_eq_div_mod`). The loops build such a table one field at a time, so the lemmas here
cover writing field `i` on top of a table that stops below position `w * i`: the new field reads
back (`fieldK_lor_shiftLeft_self`), the fields below it keep their values
(`fieldK_lor_shiftLeft_of_lt`), and the result stops below position `w * (i + 1)`
(`lor_shiftLeft_lt`).
-/

namespace PrimeCert.Polya

open Nat

/-- `fieldK qs w i` is `w` bits of `qs` read at position `w * i`. -/
public theorem fieldK_eq_div_mod (qs w i : ℕ) : fieldK qs w i = qs / 2 ^ (w * i) % 2 ^ w := by
  simp [fieldK, Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

public theorem fieldK_lt (qs w i : ℕ) : fieldK qs w i < 2 ^ w := by
  rw [fieldK_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

@[simp] public theorem testBit_fieldK (qs w i j : ℕ) :
    (fieldK qs w i).testBit j = (decide (j < w) && qs.testBit (j + w * i)) := by
  rw [fieldK_eq_div_mod, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

/-- Writing field `i` on top of a table that stops below position `w * i`. -/
public theorem fieldK_lor_shiftLeft_self {t val w i : ℕ} (ht : t < 2 ^ (w * i))
    (hv : val < 2 ^ w) : fieldK (t ||| val <<< (w * i)) w i = val := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_fieldK]
  rcases lt_or_ge j w with hj | hj
  · have htb : t.testBit (j + w * i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hj, htb]
  · have : val.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hj))
    simp [Nat.not_lt.2 hj, this]

/-- Fields below the one being written keep their values. -/
public theorem fieldK_lor_shiftLeft_of_lt {t val w i j : ℕ} (hij : j < i) :
    fieldK (t ||| val <<< (w * i)) w j = fieldK t w j := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_fieldK, testBit_fieldK]
  rcases lt_or_ge b w with hb | hb
  · have hlt : b + w * j < w * i := by
      have h1 : w * j + w ≤ w * i := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left w hij
      omega
    simp [hb, Nat.not_le.2 hlt]
  · simp [Nat.not_lt.2 hb]

/-- The table with field `i` written stops below position `w * (i + 1)`. -/
public theorem lor_shiftLeft_lt {t val w i : ℕ} (ht : t < 2 ^ (w * i)) (hv : val < 2 ^ w) :
    (t ||| val <<< (w * i)) < 2 ^ (w * (i + 1)) := by
  have hle : w * i ≤ w * (i + 1) := Nat.mul_le_mul_left w (by omega)
  refine Nat.or_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega) hle)) ?_
  rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.pow_add,
    Nat.mul_comm (2 ^ (w * i)) (2 ^ w)]
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hv

end PrimeCert.Polya
