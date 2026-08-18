/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Bits
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.BigOperators.Intervals

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The set-bit count of a 32-bit word

`popc32K` sums bit counts within groups of 2, 4 and 8 bits and then adds the four bytes through one
multiplication. Each of the three stages acts byte by byte (`stageA_succ`, `stageB_succ`,
`stageC_succ`), the byte case is a finite check (`byte_pipeline`), and the multiplication collects
the four byte counts, giving `popc32K v = bitSum v 32` (`popc32K_eq_bitSum`).
-/

namespace PrimeCert

/-- Set bits of `v` below position `n`. -/
@[expose] public def bitSum (v n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (v >>> i) % 2

/-- Set bits of a byte. -/
public def pop8 (e : ℕ) : ℕ :=
  e % 2 + e / 2 % 2 + e / 4 % 2 + e / 8 % 2 + e / 16 % 2 + e / 32 % 2 + e / 64 % 2 + e / 128 % 2

/-! ## Splitting bitwise operations at a bit boundary -/

theorem land_mod_two_pow (x m t : ℕ) : (x &&& m) % 2 ^ t = (x % 2 ^ t) &&& (m % 2 ^ t) := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and]
  cases Nat.decLt i t with
  | isTrue h => simp [h]
  | isFalse h => simp [h]

theorem land_div_two_pow (x m t : ℕ) : (x &&& m) / 2 ^ t = (x / 2 ^ t) &&& (m / 2 ^ t) := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp [Nat.testBit_div_two_pow, Nat.testBit_and]

/-- A bitwise and splits at any bit boundary. -/
theorem land_split (x m t : ℕ) :
    x &&& m = ((x % 2 ^ t) &&& (m % 2 ^ t)) + 2 ^ t * ((x / 2 ^ t) &&& (m / 2 ^ t)) := by
  conv_lhs => rw [← Nat.div_add_mod (x &&& m) (2 ^ t)]
  rw [land_mod_two_pow, land_div_two_pow]
  omega

/-- The byte-wide split, the form the stages use. -/
theorem land_split_byte (x m : ℕ) :
    x &&& m = ((x % 256) &&& (m % 256)) + 256 * ((x / 256) &&& (m / 256)) :=
  land_split x m 8

/-- Masking a shifted value stays below the value shifted. -/
theorem and_shiftRight_le (x m s : ℕ) : (x >>> s) &&& m ≤ x :=
  le_trans Nat.and_le_left (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)

theorem land_15 (x : ℕ) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

theorem land_255 (x : ℕ) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

/-! ## The three stages

`rep b k` is the `k`-byte constant repeating the byte `b`, so the masks of `popc32K` are `rep 85 4`,
`rep 51 4` and `rep 15 4`, and its multiplier is `rep 1 4`. -/

/-- The `k`-byte constant repeating the byte `b`. -/
public def rep (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => b + 256 * rep b k

/-- Counts within 2-bit groups. -/
public def stageA (k v : ℕ) : ℕ := v - ((v >>> 1) &&& rep 85 k)

/-- Counts within 4-bit groups. -/
public def stageB (k v : ℕ) : ℕ :=
  (stageA k v &&& rep 51 k) + ((stageA k v >>> 2) &&& rep 51 k)

/-- Counts within 8-bit groups. -/
public def stageC (k v : ℕ) : ℕ := (stageB k v + (stageB k v >>> 4)) &&& rep 15 k

theorem rep_succ (b k : ℕ) : rep b (k + 1) = b + 256 * rep b k := rfl

@[simp] theorem rep_zero (b : ℕ) : rep b 0 = 0 := rfl

@[simp] theorem rep_one (b : ℕ) : rep b 1 = b := rfl

theorem rep_mod_byte {b k : ℕ} (hb : b < 256) : rep b (k + 1) % 256 = b := by
  rw [rep_succ]
  omega

theorem rep_div_byte {b k : ℕ} (hb : b < 256) : rep b (k + 1) / 256 = rep b k := by
  rw [rep_succ]
  omega

@[simp] theorem stageB_zero (v : ℕ) : stageB 0 v = 0 := by simp [stageB]

@[simp] theorem stageC_zero (v : ℕ) : stageC 0 v = 0 := by simp [stageC]

set_option maxRecDepth 100000 in
/-- The byte case, by finite check: the stages stay inside the byte and the last holds its set-bit
count. -/
theorem byte_pipeline : ∀ e < 256,
    stageA 1 e < 256 ∧ stageB 1 e ≤ 68 ∧ stageB 1 e % 16 ≤ 4 ∧ stageC 1 e ≤ 8 ∧
      stageC 1 e = pop8 e := by decide

/-! ## Peeling one byte -/

/-- A repeated-byte mask splits at the byte boundary. -/
theorem land_rep_succ {v m k : ℕ} (hm : m < 256) :
    v &&& rep m (k + 1) = ((v % 256) &&& m) + 256 * ((v / 256) &&& rep m k) := by
  rw [land_split_byte, rep_mod_byte hm, rep_div_byte hm]

theorem shiftRight_div_byte (v s : ℕ) : (v >>> s) / 256 = (v / 256) >>> s := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- A mask that stops below `2 ^ (8 - s)` reads the same byte before and after the shift. -/
theorem land_shiftRight_byte {v m s : ℕ} (hs : s ≤ 8) (hm : m < 2 ^ (8 - s)) :
    ((v >>> s) % 256) &&& m = ((v % 256) >>> s) &&& m := by
  have h8 : (256 : ℕ) = 2 ^ 8 := rfl
  rw [h8]
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases Nat.lt_or_ge i (8 - s) with h | h
  · have hi8 : i < 8 := by omega
    have hsi8 : s + i < 8 := by omega
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi8, hsi8,
      decide_true, Bool.true_and]
  · have hmi : m.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) h))
    simp [Nat.testBit_and, hmi]

/-- A masked shift splits at the byte boundary. -/
theorem land_shiftRight_rep_succ {v m k s : ℕ} (hs : s ≤ 8) (hm : m < 2 ^ (8 - s)) :
    (v >>> s) &&& rep m (k + 1)
      = (((v % 256) >>> s) &&& m) + 256 * (((v / 256) >>> s) &&& rep m k) := by
  have hm256 : m < 256 := by
    have hpow : (2 : ℕ) ^ (8 - s) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rw [land_rep_succ hm256, land_shiftRight_byte hs hm, shiftRight_div_byte]

theorem stageA_succ (k v : ℕ) :
    stageA (k + 1) v = stageA 1 (v % 256) + 256 * stageA k (v / 256) := by
  have hle1 : ((v % 256) >>> 1) &&& 85 ≤ v % 256 := and_shiftRight_le _ _ _
  have hle2 : ((v / 256) >>> 1) &&& rep 85 k ≤ v / 256 := and_shiftRight_le _ _ _
  simp only [stageA, rep_one]
  rw [land_shiftRight_rep_succ (by omega) (by norm_num)]
  omega

theorem stageB_succ (k v : ℕ) :
    stageB (k + 1) v = stageB 1 (v % 256) + 256 * stageB k (v / 256) := by
  have hAlt : stageA 1 (v % 256) < 256 := (byte_pipeline _ (Nat.mod_lt _ (by omega))).1
  have h3 : (stageA 1 (v % 256) + 256 * stageA k (v / 256)) % 256 = stageA 1 (v % 256) := by omega
  have h4 : (stageA 1 (v % 256) + 256 * stageA k (v / 256)) / 256 = stageA k (v / 256) := by omega
  simp only [stageB, rep_one]
  rw [stageA_succ k v, land_rep_succ (by norm_num),
    land_shiftRight_rep_succ (by omega) (by norm_num), h3, h4]
  omega

theorem stageB_mod_16 (k v : ℕ) : stageB k v % 16 ≤ 4 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [stageB_succ]
    have h := (byte_pipeline (v % 256) (Nat.mod_lt _ (by omega))).2.2.1
    omega

/-- The last stage of a two-byte value splits into the stages of its bytes. -/
theorem stageC_byte_split {a b k : ℕ} (ha : a ≤ 68) (hb : b % 16 ≤ 4) :
    (a + 256 * b + ((a + 256 * b) >>> 4)) &&& rep 15 (k + 1)
      = ((a + a >>> 4) &&& 15) + 256 * ((b + b >>> 4) &&& rep 15 k) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  rw [(by omega : a + 256 * b + (a + 256 * b) / 16
      = a + a / 16 + 16 * (b % 16) + 256 * (b + b / 16)),
    land_rep_succ (by omega : (15:ℕ) < 256),
    (by omega : (a + a / 16 + 16 * (b % 16) + 256 * (b + b / 16)) % 256
      = a + a / 16 + 16 * (b % 16)),
    (by omega : (a + a / 16 + 16 * (b % 16) + 256 * (b + b / 16)) / 256 = b + b / 16),
    land_15, land_15]
  omega

theorem stageC_succ (k v : ℕ) :
    stageC (k + 1) v = stageC 1 (v % 256) + 256 * stageC k (v / 256) := by
  rw [stageC, stageB_succ, stageC_byte_split (byte_pipeline _ (Nat.mod_lt _ (by omega))).2.1
    (stageB_mod_16 k (v / 256))]
  simp only [stageC, rep_one]

/-! ## The word count from the byte counts -/

theorem shiftRight_mod_two (x i : ℕ) : (x >>> i) % 2 = if x.testBit i then 1 else 0 := by
  grind [Nat.shiftRight_eq_div_pow]

/-- The count as the size of the set of set positions. -/
public theorem bitSum_eq_card (v n : ℕ) :
    bitSum v n = ({i ∈ Finset.range n | v.testBit i}).card := by
  rw [bitSum, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => shiftRight_mod_two v i

/-- A count over `s` positions reads only the value modulo `2 ^ s`. -/
public theorem bitSum_mod (v s : ℕ) : bitSum (v % 2 ^ s) s = bitSum v s := by
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [shiftRight_mod_two, shiftRight_mod_two, Nat.testBit_mod_two_pow]
  simp [hi]

/-- Splitting the range at `s` splits the count. -/
public theorem bitSum_add (v s t : ℕ) : bitSum v (s + t) = bitSum v s + bitSum (v / 2 ^ s) t := by
  rw [bitSum, bitSum, bitSum, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_add, Nat.div_div_eq_div_mul]

/-- Zero has no set bits. -/
@[simp] public theorem bitSum_zero_left (n : ℕ) : bitSum 0 n = 0 := by simp [bitSum]

/-- Positions above the top set bit contribute nothing. -/
public theorem bitSum_of_lt {y m n : ℕ} (hy : y < 2 ^ m) (hmn : m ≤ n) :
    bitSum y n = bitSum y m := by
  grind [bitSum_add, Nat.div_eq_of_lt, bitSum_zero_left, Nat.exists_eq_add_of_le]

/-- Each position contributes at most one. -/
public theorem bitSum_le (v n : ℕ) : bitSum v n ≤ n := by
  rw [bitSum_eq_card]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- A count over any range is bounded by the width of the value. -/
public theorem bitSum_le_of_lt {v m : ℕ} (hv : v < 2 ^ m) (n : ℕ) : bitSum v n ≤ m := by
  rcases Nat.le_total m n with h | h
  · rw [bitSum_of_lt hv h]
    exact bitSum_le v m
  · exact le_trans (bitSum_le v n) h

theorem bitSum_byte (e : ℕ) : bitSum e 8 = pop8 e := by
  simp [bitSum, pop8, Finset.sum_range_succ, Nat.shiftRight_eq_div_pow]

/-- Splitting a count at a byte boundary. -/
theorem bitSum_byte_split (v n : ℕ) : bitSum v (8 + n) = bitSum v 8 + bitSum (v / 256) n :=
  bitSum_add v 8 n

/-- The four masks and the multiplier of `popc32K` repeat one byte across the word. -/
theorem rep_85 : rep 85 4 = 1431655765 := rfl

theorem rep_51 : rep 51 4 = 858993459 := rfl

theorem rep_15 : rep 15 4 = 252645135 := rfl

/-- The multiplication by `rep 1 4` places the sum of the four byte counts in the top byte. -/
theorem byte_merge {c0 c1 c2 c3 : ℕ} (h0 : c0 ≤ 8) (h1 : c1 ≤ 8) (h2 : c2 ≤ 8) (h3 : c3 ≤ 8) :
    ((c0 + 256 * (c1 + 256 * (c2 + 256 * c3))) * 16843009) / 16777216 % 256
      = c0 + c1 + c2 + c3 := by
  have hexp : (c0 + 256 * (c1 + 256 * (c2 + 256 * c3))) * 16843009
      = (c0 + 256 * (c0 + c1) + 65536 * (c0 + c1 + c2)) +
        16777216 * ((c0 + c1 + c2 + c3) +
          256 * ((c1 + c2 + c3) + 256 * ((c2 + c3) + 256 * c3))) := by ring
  have hlow : c0 + 256 * (c0 + c1) + 65536 * (c0 + c1 + c2) < 16777216 := by omega
  rw [hexp, Nat.add_mul_div_left _ _ (by omega : 0 < 16777216), Nat.div_eq_of_lt hlow]
  omega

/-- `popc32K` counts the set bits of a 32-bit word. -/
public theorem popc32K_eq_bitSum (v : ℕ) : popc32K v = bitSum v 32 := by
  have hdef : popc32K v = ((stageC 4 v * 16843009) >>> 24) &&& 255 := by
    simp only [popc32K, stageC, stageB, stageA, rep_85, rep_51, rep_15, Nat.land_eq, Nat.sub_eq,
      Nat.add_eq, Nat.mul_eq, Nat.shiftRight_eq']
  have hbytes : stageC 4 v = stageC 1 (v % 256) + 256 * (stageC 1 (v / 256 % 256) +
      256 * (stageC 1 (v / 256 / 256 % 256) + 256 * stageC 1 (v / 256 / 256 / 256 % 256))) := by
    rw [stageC_succ 3 v, stageC_succ 2 (v / 256), stageC_succ 1 (v / 256 / 256),
      stageC_succ 0 (v / 256 / 256 / 256)]
    simp
  have hb : ∀ y : ℕ, stageC 1 (y % 256) ≤ 8 := fun y =>
    (byte_pipeline _ (Nat.mod_lt _ (by omega))).2.2.2.1
  have hcount : bitSum v 32 = stageC 1 (v % 256) + stageC 1 (v / 256 % 256) +
      stageC 1 (v / 256 / 256 % 256) + stageC 1 (v / 256 / 256 / 256 % 256) := by
    have e0 : bitSum v 32 = bitSum v 8 + bitSum (v / 256) 24 := bitSum_byte_split v 24
    have e1 : bitSum (v / 256) 24 = bitSum (v / 256) 8 + bitSum (v / 256 / 256) 16 :=
      bitSum_byte_split _ 16
    have e2 : bitSum (v / 256 / 256) 16
        = bitSum (v / 256 / 256) 8 + bitSum (v / 256 / 256 / 256) 8 := bitSum_byte_split _ 8
    have byte : ∀ x : ℕ, bitSum x 8 = stageC 1 (x % 256) := by
      intro x
      have h : (2 : ℕ) ^ 8 = 256 := rfl
      rw [← bitSum_mod x 8, h, bitSum_byte, (byte_pipeline _ (Nat.mod_lt _ (by omega))).2.2.2.2]
    rw [e0, e1, e2, byte v, byte (v / 256), byte (v / 256 / 256), byte (v / 256 / 256 / 256)]
    omega
  have hp24 : (2 : ℕ) ^ 24 = 16777216 := rfl
  rw [hdef, hbytes, Nat.shiftRight_eq_div_pow, hp24, land_255, hcount]
  exact byte_merge (hb v) (hb (v / 256)) (hb (v / 256 / 256)) (hb (v / 256 / 256 / 256))

end PrimeCert
