/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Bits
import Mathlib.Data.Nat.Bitwise

/-!
# Reading a packed entry

A table is one natural number holding `w`-bit entries, lowest first, and `entryK qs w i` reads entry
`i` (`entryK_eq_div_mod`). A loop writing one entry per step reads its entries back from
`entryK_of_lor_chain`.
-/

namespace PrimeCert

/-- `entryK qs w i` is `w` bits of `qs` read at position `w * i`. -/
public theorem entryK_eq_div_mod (qs w i : ℕ) : entryK qs w i = qs / 2 ^ (w * i) % 2 ^ w := by
  simp [entryK, Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

/-- An entry holds `w` bits. -/
public theorem entryK_lt (qs w i : ℕ) : entryK qs w i < 2 ^ w := by
  rw [entryK_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Bit `j` of entry `i`, for `j < w`, is bit `j + w * i` of the table. -/
@[simp] public theorem testBit_entryK (qs w i j : ℕ) :
    (entryK qs w i).testBit j = (decide (j < w) && qs.testBit (j + w * i)) := by
  rw [entryK_eq_div_mod, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

/-- A table that stops below position `w * i` has entry `i` clear. -/
public theorem entryK_eq_zero_of_lt {t w i : ℕ} (ht : t < 2 ^ (w * i)) : entryK t w i = 0 := by
  rw [entryK_eq_div_mod, Nat.div_eq_of_lt ht, Nat.zero_mod]

/-- One entry further along starts `w` positions higher. -/
theorem mul_succ_le_mul {w a b : ℕ} (h : a < b) : w * a + w ≤ w * b := by
  rw [← Nat.mul_succ]
  exact Nat.mul_le_mul_left w h

/-- Reading an entry distributes over a bitwise or. -/
theorem entryK_lor (a b w j : ℕ) : entryK (a ||| b) w j = entryK a w j ||| entryK b w j := by
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp [Bool.and_or_distrib_left]

/-- A value written at entry `i` reads back there. -/
theorem entryK_shiftLeft_self {val w i : ℕ} (hv : val < 2 ^ w) :
    entryK (val <<< (w * i)) w i = val := by
  rw [entryK_eq_div_mod, Nat.shiftLeft_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
    Nat.mod_eq_of_lt hv]

/-- Every entry other than `i` of a value written at entry `i` is zero. -/
theorem entryK_shiftLeft_ne {val w i j : ℕ} (hv : val < 2 ^ w) (hij : j ≠ i) :
    entryK (val <<< (w * i)) w j = 0 := by
  refine Nat.eq_of_testBit_eq fun b ↦ ?_
  rcases Nat.lt_or_ge b w with hb | hb
  · rcases Nat.lt_or_ge j i with h | h
    · have := mul_succ_le_mul (w := w) h
      simp [hb, Nat.testBit_shiftLeft, Nat.not_le.2 (by lia : b + w * j < w * i)]
    · have := mul_succ_le_mul (w := w) (by lia : i < j)
      have hzero : val.testBit (b + w * j - w * i) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by lia) (by lia)))
      simp [hb, Nat.testBit_shiftLeft, hzero]
  · simp [Nat.not_lt.2 hb]

/-- Writing at entry `i` gives entry `j ≠ i` the value it has in `t`. -/
public theorem entryK_lor_shiftLeft_ne {t val w i j : ℕ} (hv : val < 2 ^ w) (hij : j ≠ i) :
    entryK (t ||| val <<< (w * i)) w j = entryK t w j := by
  rw [entryK_lor, entryK_shiftLeft_ne hv hij, Nat.or_zero]

/-- Writing over a clear entry reads the value back. -/
public theorem entryK_lor_shiftLeft_of_zero {t val w i : ℕ} (ht : entryK t w i = 0)
    (hv : val < 2 ^ w) : entryK (t ||| val <<< (w * i)) w i = val := by
  rw [entryK_lor, ht, entryK_shiftLeft_self hv, Nat.zero_or]

/-- Shifting a table down by whole entries renumbers them. -/
public theorem entryK_shiftRight (qs w n j : ℕ) :
    entryK (qs / 2 ^ (w * n)) w j = entryK qs w (n + j) := by
  grind [entryK_eq_div_mod, Nat.div_div_eq_div_mul, Nat.pow_add, Nat.mul_add]

/-- A table built one entry per step from an empty table at `start`: the entries it covers read back
the values written, and the entries outside stay clear. -/
public theorem entryK_of_lor_chain {wb start : ℕ} {F t : ℕ → ℕ} (h0 : t 0 = 0)
    (hsucc : ∀ f, t (f + 1) = t f ||| F (start + f) <<< (wb * (start + f))) (fuel : ℕ)
    (hval : ∀ j, start ≤ j → j < start + fuel → F j < 2 ^ wb) :
    (∀ j, start ≤ j → j < start + fuel → entryK (t fuel) wb j = F j) ∧
      ∀ j, (j < start ∨ start + fuel ≤ j) → entryK (t fuel) wb j = 0 := by
  induction fuel with
  | zero =>
    refine ⟨by lia, fun j _ ↦ ?_⟩
    rw [h0]
    exact entryK_eq_zero_of_lt (Nat.two_pow_pos _)
  | succ f ih =>
    obtain ⟨ihentry, ihzero⟩ := ih fun j hj1 hj2 ↦ hval j hj1 (by lia)
    have hlast : F (start + f) < 2 ^ wb := hval _ (by lia) (by lia)
    rw [hsucc f]
    refine ⟨fun j hj1 hj2 ↦ ?_, fun j hj ↦ ?_⟩
    · rcases Nat.lt_or_ge j (start + f) with h | h
      · rw [entryK_lor_shiftLeft_ne hlast (by lia)]
        exact ihentry j hj1 h
      · have hjf : j = start + f := by lia
        subst hjf
        exact entryK_lor_shiftLeft_of_zero (ihzero (start + f) (by lia)) hlast
    · rw [entryK_lor_shiftLeft_ne hlast (by lia)]
      exact ihzero j (by lia)

/-- The table with entry `i` written stops below position `w * (i + 1)`. -/
public theorem lor_shiftLeft_lt {t val w i : ℕ} (ht : t < 2 ^ (w * i)) (hv : val < 2 ^ w) :
    (t ||| val <<< (w * i)) < 2 ^ (w * (i + 1)) := by
  have hle : w * i ≤ w * (i + 1) := Nat.mul_le_mul_left w (by lia)
  refine Nat.or_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by lia) hle)) ?_
  rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.pow_add,
    Nat.mul_comm (2 ^ (w * i)) (2 ^ w)]
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hv

end PrimeCert
