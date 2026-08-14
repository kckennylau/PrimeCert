/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Defs
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

/-- Writing a field leaves the other fields alone, wherever it is written. -/
public theorem fieldK_lor_shiftLeft_ne {t val w i j : ℕ} (hv : val < 2 ^ w) (hij : j ≠ i) :
    fieldK (t ||| val <<< (w * i)) w j = fieldK t w j := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_fieldK, testBit_fieldK]
  rcases lt_or_ge b w with hb | hb
  · have hne : val.testBit (b + w * j - w * i) = false ∨ b + w * j < w * i := by
      rcases Nat.lt_or_ge j i with h | h
      · refine Or.inr ?_
        have h1 : w * j + w ≤ w * i := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left w h
        omega
      · have hji : i < j := by omega
        refine Or.inl (Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right ?_ ?_)))
        · omega
        · have h1 : w * i + w ≤ w * j := by
            rw [← Nat.mul_succ]
            exact Nat.mul_le_mul_left w hji
          omega
    rcases hne with h | h
    · simp [hb, Nat.testBit_shiftLeft, h]
    · simp [hb, Nat.testBit_shiftLeft, Nat.not_le.2 h]
  · simp [Nat.not_lt.2 hb]

/-- Writing over a clear field reads the value back. -/
public theorem fieldK_lor_shiftLeft_of_zero {t val w i : ℕ} (ht : fieldK t w i = 0)
    (hv : val < 2 ^ w) : fieldK (t ||| val <<< (w * i)) w i = val := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_fieldK]
  rcases lt_or_ge b w with hb | hb
  · have htb : t.testBit (b + w * i) = false := by
      have h0 : (fieldK t w i).testBit b = false := by
        rw [ht]
        simp
      rw [testBit_fieldK] at h0
      simpa [hb] using h0
    simp [hb, Nat.testBit_shiftLeft, htb]
  · have : val.testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hb))
    simp [Nat.not_lt.2 hb, this]

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
    rw [h0, fieldK_eq_div_mod]
    simp
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

end PrimeCert.Polya
