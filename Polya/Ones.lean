/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.PopCount
public import Polya.Field
public import PrimeCert.ForLean

/-!
# The running counts of set bits

Field `i` of `onesK lam w cnt` holds the set bits of `lam` below position `32 * i`
(`fieldK_onesK`), and `onesBelowK` reads the count below an arbitrary position from that table and
one partial chunk (`onesBelowK_eq`).
-/

namespace PrimeCert.Polya

open Nat

/-- Masking a window and shifting it down reads the window in place. -/
theorem land_shiftLeft_shiftRight (x M s : ℕ) : (x &&& (M <<< s)) >>> s = (x >>> s) &&& M := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_shiftLeft]

/-- The set bits of one 32-position chunk. -/
public theorem popc32K_chunk (lam i : ℕ) :
    popc32K ((lam >>> (32 * i)) &&& ((1 <<< 32) - 1)) = bitSum (lam / 2 ^ (32 * i)) 32 := by
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    popc32K_eq_bitSum, bitSum_mod]

/-- The counts table after `fuel` steps: field `i` holds the set bits below position `32 * i`, and
the table stops below field `fuel + 1`. -/
theorem onesLoopK_spec {lam w : ℕ} (hw : ∀ n, bitSum lam n < 2 ^ w) (fuel : ℕ) :
    (∀ i ≤ fuel, fieldK (onesLoopK lam w 0 0 fuel) w i = bitSum lam (32 * i)) ∧
      onesLoopK lam w 0 0 fuel < 2 ^ (w * (fuel + 1)) := by
  induction fuel with
  | zero =>
    constructor
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [onesLoopK, fieldK_eq_div_mod, bitSum]
    · simp only [onesLoopK]
      exact Nat.two_pow_pos _
  | succ f ih =>
    obtain ⟨ihfield, ihlt⟩ := ih
    have hval : fieldK (onesLoopK lam w 0 0 f) w f +
        popc32K ((lam >>> (32 * f)) &&& ((1 <<< 32) - 1))
        = bitSum lam (32 * (f + 1)) := by
      rw [ihfield f (by omega), popc32K_chunk lam f]
      have hsplit := bitSum_add lam (32 * f) 32
      have harith : 32 * f + 32 = 32 * (f + 1) := by omega
      rw [harith] at hsplit
      omega
    have hlt : bitSum lam (32 * (f + 1)) < 2 ^ w := hw _
    have hstep : onesLoopK lam w 0 0 (f + 1)
        = onesLoopK lam w 0 0 f ||| (bitSum lam (32 * (f + 1))) <<< (w * (f + 1)) := by
      rw [onesLoopK_succ]
      simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.land_eq, Nat.sub_eq,
        Nat.add_eq, Nat.succ_eq_add_one, Nat.zero_add]
      rw [hval]
    rw [hstep]
    constructor
    · intro i hi
      rcases Nat.lt_or_ge i (f + 1) with h | h
      · rw [fieldK_lor_shiftLeft_ne hlt (by omega), ihfield i (by omega)]
      · have hif : i = f + 1 := by omega
        subst hif
        rw [fieldK_lor_shiftLeft_of_zero (fieldK_eq_zero_of_lt ihlt) hlt]
    · exact lor_shiftLeft_lt ihlt hlt

/-- Field `i` of the counts table holds the set bits of `lam` below position `32 * i`. -/
public theorem fieldK_onesK {lam w cnt i : ℕ} (hw : ∀ n, bitSum lam n < 2 ^ w) (hi : i ≤ cnt) :
    fieldK (onesK lam w cnt) w i = bitSum lam (32 * i) :=
  (onesLoopK_spec hw cnt).1 i hi

/-- `onesBelowK` counts the set bits of `lam` below `p`, from the recorded count at the nearest
lower multiple of 32 and the bits of the partial chunk. -/
public theorem onesBelowK_eq {lam ones wc p : ℕ}
    (hones : fieldK ones wc (p / 32) = bitSum lam (32 * (p / 32))) :
    onesBelowK lam ones wc p = bitSum lam p := by
  have hfield : ((ones &&& ((2 ^ wc - 1) <<< (wc * (p / 32)))) >>> (wc * (p / 32)))
      = fieldK ones wc (p / 32) := by
    rw [land_shiftLeft_shiftRight, fieldK]
    simp [Nat.one_shiftLeft]
  have hlt : (lam / 2 ^ (32 * (p / 32))) % 2 ^ (p % 32) < 2 ^ (p % 32) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpart : popc32K ((lam &&& ((2 ^ (p % 32) - 1) <<< ((p / 32) * 32))) >>> ((p / 32) * 32))
      = bitSum (lam / 2 ^ (32 * (p / 32))) (p % 32) := by
    rw [land_shiftLeft_shiftRight, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Nat.mul_comm (p / 32) 32, popc32K_eq_bitSum _, bitSum_of_lt hlt (by omega), bitSum_mod]
  rw [onesBelowK]
  simp only [Nat.div_eq_div, Nat.mod_eq_mod, Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq',
    Nat.sub_eq, Nat.add_eq, Nat.mul_eq, Nat.one_shiftLeft]
  rw [hfield, hones, hpart]
  have hsplit := bitSum_add lam (32 * (p / 32)) (p % 32)
  have harith : 32 * (p / 32) + p % 32 = p := by omega
  rw [harith] at hsplit
  omega

end PrimeCert.Polya
