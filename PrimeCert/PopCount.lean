/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Bits
public import Mathlib.Algebra.BigOperators.Intervals

import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The set-bit count of a word

`popc64K` sums bit counts within groups of 2, 4 and 8 bits and then adds the bytes through one
multiplication. Each of the three stages acts byte by byte (`stageA_succ`, `stageB_succ`,
`stageC_succ`), the byte case is a finite check (`byte_pipeline`), and the multiplication collects
the byte counts at any width (`stageC_mul_rep`), giving `popc64K v = bitSum v 64`
(`popc64K_eq_bitSum`).
-/

namespace PrimeCert

/-- Set bits of `v` below position `n`. -/
@[expose] public def bitSum (v n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (v >>> i) % 2

/-- Set bits of a byte. -/
public def pop8 (e : ℕ) : ℕ :=
  e % 2 + e / 2 % 2 + e / 4 % 2 + e / 8 % 2 + e / 16 % 2 + e / 32 % 2 + e / 64 % 2 + e / 128 % 2

/-! ## Splitting bitwise operations at a bit boundary -/

/-- A bitwise and splits at any bit boundary. -/
theorem land_split (x m t : ℕ) :
    x &&& m = ((x % 2 ^ t) &&& (m % 2 ^ t)) + 2 ^ t * ((x / 2 ^ t) &&& (m / 2 ^ t)) := by
  grind [Nat.and_mod_two_pow, Nat.and_div_two_pow, Nat.div_add_mod]

/-- The byte-wide split, the form the stages use. -/
theorem land_split_byte (x m : ℕ) :
    x &&& m = ((x % 256) &&& (m % 256)) + 256 * ((x / 256) &&& (m / 256)) :=
  land_split x m 8

/-- Masking a shifted value stays below the value shifted. -/
theorem and_shiftRight_le (x m s : ℕ) : (x >>> s) &&& m ≤ x :=
  Nat.and_le_left.trans (Nat.shiftRight_le _ _)

theorem land_15 (x : ℕ) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

theorem land_255 (x : ℕ) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

/-! ## The three stages

`rep b k` is the `k`-byte constant repeating the byte `b`, so the masks of `popc64K` are `rep 85 8`,
`rep 51 8` and `rep 15 8`, and its multiplier is `rep 1 8`. -/

/-- The `k`-byte constant repeating the byte `b`. -/
public def rep (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => b + 256 * rep b k

/-- Counts within 2-bit groups of a `k`-byte value. -/
def stageA (k v : ℕ) : ℕ := v - (v >>> 1 &&& rep 85 k)

/-- Counts within 4-bit groups of a `k`-byte value. -/
def stageB (k v : ℕ) : ℕ := (stageA k v &&& rep 51 k) + (stageA k v >>> 2 &&& rep 51 k)

/-- Counts within 8-bit groups. -/
def stageC (k v : ℕ) : ℕ := (stageB k v + (stageB k v >>> 4)) &&& rep 15 k

@[simp] lemma popc64K_eq' {v : ℕ} : popc64K v = (stageC 8 v * rep 1 8) >>> 56 &&& 255 := rfl

@[simp, grind =] theorem rep_succ (b k : ℕ) : rep b (k + 1) = b + 256 * rep b k := rfl

@[simp] theorem rep_zero (b : ℕ) : rep b 0 = 0 := rfl

@[simp] theorem rep_one (b : ℕ) : rep b 1 = b := rfl

theorem rep_mod_byte {b k : ℕ} (hb : b < 256) : rep b (k + 1) % 256 = b := by grind

theorem rep_div_byte {b k : ℕ} (hb : b < 256) : rep b (k + 1) / 256 = rep b k := by grind

@[simp] theorem stageB_zero (v : ℕ) : stageB 0 v = 0 := by simp [stageB]
@[simp] theorem stageC_zero (v : ℕ) : stageC 0 v = 0 := by simp [stageC]

/-- On a byte the stages stay inside the byte, and the last one holds its set-bit count. -/
theorem byte_pipeline {e : ℕ} (he : e < 256) :
    stageA 1 e < 256 ∧ stageB 1 e ≤ 68 ∧ stageB 1 e % 16 ≤ 4 ∧ stageC 1 e ≤ 8 ∧
      stageC 1 e = bitSum e 8 := by decide +kernel +revert

/-! ## Peeling one byte -/

/-- A repeated-byte mask splits at the byte boundary. -/
theorem land_rep_succ {v m k : ℕ} (hm : m < 256) :
    v &&& rep m (k + 1) = ((v % 256) &&& m) + 256 * ((v / 256) &&& rep m k) := by
  grind [land_split_byte, rep_mod_byte, rep_div_byte]

theorem shiftRight_div_byte (v s : ℕ) : (v >>> s) / 256 = (v / 256) >>> s := by
  grind [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

/-- A mask that stops below `2 ^ (8 - s)` reads the same byte before and after the shift. -/
theorem land_shiftRight_byte {v m s : ℕ} (hs : s ≤ 8) (hm : m < 2 ^ (8 - s)) :
    ((v >>> s) % 256) &&& m = ((v % 256) >>> s) &&& m := by
  have h8 : (256 : ℕ) = 2 ^ 8 := rfl
  rw [h8]
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  rcases Nat.lt_or_ge i (8 - s) with h | h
  · have hi8 : i < 8 := by lia
    have hsi8 : s + i < 8 := by lia
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi8, hsi8,
      decide_true, Bool.true_and]
  · have hmi : m.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by lia) h))
    simp [Nat.testBit_and, hmi]

/-- A masked shift splits at the byte boundary. -/
theorem land_shiftRight_rep_succ {v m k s : ℕ} (hs : s ≤ 8) (hm : m < 2 ^ (8 - s)) :
    (v >>> s) &&& rep m (k + 1)
      = (((v % 256) >>> s) &&& m) + 256 * (((v / 256) >>> s) &&& rep m k) := by
  have hm256 : m < 256 := by
    have hpow : (2 : ℕ) ^ (8 - s) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by lia) (by lia)
    lia
  rw [land_rep_succ hm256, land_shiftRight_byte hs hm, shiftRight_div_byte]

theorem stageA_succ (k v : ℕ) :
    stageA (k + 1) v = stageA 1 (v % 256) + 256 * stageA k (v / 256) := by
  have hle1 : ((v % 256) >>> 1) &&& 85 ≤ v % 256 := and_shiftRight_le _ _ _
  have hle2 : ((v / 256) >>> 1) &&& rep 85 k ≤ v / 256 := and_shiftRight_le _ _ _
  simp only [stageA, rep_one]
  grind [land_shiftRight_rep_succ]

theorem stageB_succ (k v : ℕ) :
    stageB (k + 1) v = stageB 1 (v % 256) + 256 * stageB k (v / 256) := by
  have hAlt : stageA 1 (v % 256) < 256 := (byte_pipeline (Nat.mod_lt _ (by lia))).1
  have h3 : (stageA 1 (v % 256) + 256 * stageA k (v / 256)) % 256 = stageA 1 (v % 256) := by lia
  have h4 : (stageA 1 (v % 256) + 256 * stageA k (v / 256)) / 256 = stageA k (v / 256) := by lia
  simp only [stageB, rep_one]
  rw [stageA_succ k v, land_rep_succ (by norm_num),
    land_shiftRight_rep_succ (by lia) (by norm_num), h3, h4]
  grind

theorem stageB_mod_16 (k v : ℕ) : stageB k v % 16 ≤ 4 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [stageB_succ]
    have h := (byte_pipeline (e := v % 256) (Nat.mod_lt _ (by lia))).2.2.1
    lia

/-- The last stage of a two-byte value splits into the stages of its bytes. -/
theorem stageC_byte_split {a b k : ℕ} (ha : a ≤ 68) (hb : b % 16 ≤ 4) :
    (a + 256 * b + ((a + 256 * b) >>> 4)) &&& rep 15 (k + 1)
      = ((a + a >>> 4) &&& 15) + 256 * ((b + b >>> 4) &&& rep 15 k) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  rw [(by lia : a + 256 * b + (a + 256 * b) / 16
      = a + a / 16 + 16 * (b % 16) + 256 * (b + b / 16)),
    land_rep_succ (by lia : (15:ℕ) < 256),
    (by lia : (a + a / 16 + 16 * (b % 16) + 256 * (b + b / 16)) % 256
      = a + a / 16 + 16 * (b % 16)),
    (by lia : (a + a / 16 + 16 * (b % 16) + 256 * (b + b / 16)) / 256 = b + b / 16),
    land_15, land_15]
  grind

theorem stageC_succ (k v : ℕ) :
    stageC (k + 1) v = stageC 1 (v % 256) + 256 * stageC k (v / 256) := by
  rw [stageC, stageB_succ, stageC_byte_split (byte_pipeline (Nat.mod_lt _ (by lia))).2.1
    (stageB_mod_16 k (v / 256))]
  simp only [stageC, rep_one]

/-! ## The word count from the byte counts -/

theorem shiftRight_mod_two (x i : ℕ) : (x >>> i) % 2 = if x.testBit i then 1 else 0 := by
  grind [Nat.shiftRight_eq_div_pow]

/-- The count as the size of the set of set positions. -/
public theorem bitSum_eq_card (v n : ℕ) :
    bitSum v n = {i ∈ Finset.range n | v.testBit i}.card := by
  grind [bitSum, Finset.card_filter, shiftRight_mod_two]

/-- A count over `s` positions reads only the value modulo `2 ^ s`. -/
public theorem bitSum_mod (v s : ℕ) : bitSum (v % 2 ^ s) s = bitSum v s := by
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [Finset.mem_range] at hi
  grind [shiftRight_mod_two]

/-- Splitting the range at `s` splits the count. -/
public theorem bitSum_add (v s t : ℕ) : bitSum v (s + t) = bitSum v s + bitSum (v / 2 ^ s) t := by
  rw [bitSum, bitSum, bitSum, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  grind [Nat.shiftRight_eq_div_pow, Nat.pow_add, Nat.div_div_eq_div_mul]

/-- Zero has no set bits. -/
@[simp] public theorem bitSum_zero_left (n : ℕ) : bitSum 0 n = 0 := by simp [bitSum]

/-- Positions above the top set bit contribute nothing. -/
public theorem bitSum_of_lt {y m n : ℕ} (hy : y < 2 ^ m) (hmn : m ≤ n) :
    bitSum y n = bitSum y m := by
  grind [bitSum_add, Nat.div_eq_of_lt, bitSum_zero_left, Nat.exists_eq_add_of_le]

/-- Each position contributes at most one. -/
public theorem bitSum_le (v n : ℕ) : bitSum v n ≤ n := by
  grind [bitSum_eq_card, Finset.card_filter_le, Finset.card_range]

/-- A count over any range is bounded by the width of the value. -/
public theorem bitSum_le_of_lt {v m : ℕ} (hv : v < 2 ^ m) (n : ℕ) : bitSum v n ≤ m := by
  rcases Nat.le_total m n with h | h
  · rw [bitSum_of_lt hv h]
    exact bitSum_le v m
  · exact le_trans (bitSum_le v n) h

/-- Splitting a count at a byte boundary. -/
theorem bitSum_byte_split (v n : ℕ) : bitSum v (8 + n) = bitSum v 8 + bitSum (v / 256) n :=
  bitSum_add v 8 n

/-! ## The merge -/

/-- Sum of the low `k` bytes of `v`. -/
public def byteSum : ℕ → ℕ → ℕ
  | _, 0 => 0
  | v, k + 1 => v % 256 + byteSum (v / 256) k

@[simp] theorem byteSum_zero (v : ℕ) : byteSum v 0 = 0 := rfl

theorem byteSum_succ (v k : ℕ) : byteSum v (k + 1) = v % 256 + byteSum (v / 256) k := rfl

/-- The top byte of a repeated-byte constant. -/
theorem rep_succ_top (b k : ℕ) : rep b (k + 1) = rep b k + 256 ^ k * b := by
  induction k with
  | zero => simp
  | succ k ih => grind

/-- `rep 1 k` fills `k` bytes with ones. -/
theorem rep_one_mul (k : ℕ) : 255 * rep 1 k + 1 = 256 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => grind [pow_succ]

/-- Multiplying by `rep 1 (k + 1)` places the sum of the low `k + 1` bytes in byte `k`, over a low
part bounded by that sum. -/
theorem mul_rep_split (k v : ℕ) :
    ∃ L T, L ≤ byteSum v (k + 1) * rep 1 k ∧
      v * rep 1 (k + 1) = L + 256 ^ k * (byteSum v (k + 1) + 256 * T) := by
  induction k generalizing v with
  | zero => exact ⟨0, v / 256, by simp, by grind [byteSum_succ, byteSum_zero, rep_one]⟩
  | succ k ih =>
    obtain ⟨L, T, hL, hLT⟩ := ih (v / 256)
    have h1 : 256 * rep 1 k ≤ rep 1 (k + 1) := by grind
    have hw : v = v % 256 + 256 * (v / 256) := by lia
    refine ⟨v % 256 * rep 1 (k + 1) + 256 * L, T + v / 256, ?_, ?_⟩
    · have h2 : 256 * L ≤ byteSum (v / 256) (k + 1) * rep 1 (k + 1) :=
        calc 256 * L ≤ 256 * (byteSum (v / 256) (k + 1) * rep 1 k) := by lia
          _ = byteSum (v / 256) (k + 1) * (256 * rep 1 k) := by ring
          _ ≤ byteSum (v / 256) (k + 1) * rep 1 (k + 1) := Nat.mul_le_mul_left _ h1
      rw [byteSum_succ, add_mul]
      lia
    · rw [byteSum_succ, rep_succ_top 1 (k + 1), mul_one]
      grind

/-- The multiplication by `rep 1 (k + 1)` reads the sum of the low `k + 1` bytes off byte `k`. -/
theorem byteSum_mul_rep {k v : ℕ} (h : byteSum v (k + 1) < 256) :
    v * rep 1 (k + 1) / 256 ^ k % 256 = byteSum v (k + 1) := by
  obtain ⟨L, T, hL, hLT⟩ := mul_rep_split k v
  have h255 : byteSum v (k + 1) * rep 1 k ≤ 255 * rep 1 k := Nat.mul_le_mul_right _ (by lia)
  have hlt : L < 256 ^ k := by
    have := rep_one_mul k
    lia
  rw [hLT, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt]
  lia

/-- The last stage of a byte holds the count of that byte. -/
theorem stageC_byte (v : ℕ) : stageC 1 (v % 256) = bitSum v 8 := by
  rw [← bitSum_mod v 8, (by norm_num : (2 : ℕ) ^ 8 = 256),
    (byte_pipeline (Nat.mod_lt _ (by lia))).2.2.2.2]

/-- The bytes of the last stage sum to the count of the word. -/
theorem byteSum_stageC (k v : ℕ) : byteSum (stageC k v) k = bitSum v (8 * k) := by
  induction k generalizing v with
  | zero => simp [bitSum]
  | succ k ih =>
    have hb : stageC 1 (v % 256) ≤ 8 := (byte_pipeline (Nat.mod_lt _ (by lia))).2.2.2.1
    have hm : (stageC 1 (v % 256) + 256 * stageC k (v / 256)) % 256 = stageC 1 (v % 256) := by lia
    have hd : (stageC 1 (v % 256) + 256 * stageC k (v / 256)) / 256 = stageC k (v / 256) := by lia
    rw [byteSum_succ, stageC_succ, hm, hd, ih, (by ring : 8 * (k + 1) = 8 + 8 * k),
      bitSum_byte_split, stageC_byte]

/-- The pipeline over `k + 1` bytes counts the set bits of those bytes. -/
theorem stageC_mul_rep {k : ℕ} (hk : k < 31) (v : ℕ) :
    stageC (k + 1) v * rep 1 (k + 1) / 256 ^ k % 256 = bitSum v (8 * (k + 1)) := by
  grind [byteSum_mul_rep, byteSum_stageC, bitSum_le]

theorem rep_85_eight : rep 85 8 = 6148914691236517205 := rfl

theorem rep_51_eight : rep 51 8 = 3689348814741910323 := rfl

theorem rep_15_eight : rep 15 8 = 1085102592571150095 := rfl

theorem rep_one_eight : rep 1 8 = 72340172838076673 := rfl

/-- `popc64K` counts the set bits of a 64-bit word. -/
public theorem popc64K_eq_bitSum (v : ℕ) : popc64K v = bitSum v 64 := by
  have hdef : popc64K v = ((stageC 8 v * rep 1 8) >>> 56) &&& 255 := by
    simp only [popc64K, stageC, stageB, stageA, rep_85_eight, rep_51_eight, rep_15_eight,
      rep_one_eight, Nat.land_eq, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, Nat.shiftRight_eq']
  have key : stageC 8 v * rep 1 8 / 256 ^ 7 % 256 = bitSum v 64 := by
    simpa using stageC_mul_rep (k := 7) (by norm_num) v
  rw [hdef, Nat.shiftRight_eq_div_pow, land_255, (by norm_num : (2 : ℕ) ^ 56 = 256 ^ 7), key]

end PrimeCert
