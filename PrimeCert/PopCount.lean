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

/-- The number of bits of `v` that are set below position `n`. -/
@[expose] public def bitSum (v n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (v >>> i) % 2

/-! ## Splitting bitwise operations at a bit boundary -/

/-- A bitwise and splits at any bit boundary. -/
theorem land_split (x m t : ℕ) :
    x &&& m = (x % 2 ^ t &&& m % 2 ^ t) + 2 ^ t * (x / 2 ^ t &&& m / 2 ^ t) := by
  rw [← Nat.and_mod_two_pow, ← Nat.and_div_two_pow, Nat.mod_add_div]

/-- The byte-wide split, the form the stages use. -/
theorem land_split_byte (x m : ℕ) :
    x &&& m = (x % 256 &&& m % 256) + 256 * (x / 256 &&& m / 256) :=
  land_split x m 8

/-- Two values split at the byte boundary combine byte by byte under a bitwise and. -/
lemma land_split' {a b a' b' : ℕ} (ha : a < 256) (ha' : a' < 256) :
    (a + 256 * b) &&& (a' + 256 * b') = (a &&& a') + 256 * (b &&& b') := by
  rw [land_split_byte]
  grind

/-- Masking a value shifted down, then shifting back up, masks with the mask shifted up. -/
lemma shiftLeft_land_shiftRight (v w s : ℕ) :
    ((v >>> s) &&& w) <<< s = v &&& (w <<< s) :=
  Nat.eq_of_testBit_eq fun j ↦ by grind

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

@[simp, grind =] theorem rep_zero (b : ℕ) : rep b 0 = 0 := rfl

@[simp, grind =] theorem rep_one (b : ℕ) : rep b 1 = b := rfl

theorem rep_mod_byte {b k : ℕ} (hb : b < 256) : rep b (k + 1) % 256 = b := by grind

theorem rep_div_byte {b k : ℕ} (hb : b < 256) : rep b (k + 1) / 256 = rep b k := by grind

lemma rep_mul_two_pow (b s k : ℕ) : rep b k <<< s = rep (b <<< s) k := by
  induction k with grind [Nat.shiftLeft_eq]

/-- The top byte of a repeated-byte constant. -/
theorem rep_succ_top {b k : ℕ} : rep b (k + 1) = rep b k + 256 ^ k * b := by
  induction k with grind

/-- `rep 1 k` fills `k` bytes with ones. -/
theorem rep_one_mul (k : ℕ) : 255 * rep 1 k + 1 = 256 ^ k := by induction k with grind [pow_succ]

@[simp] theorem stageB_zero (v : ℕ) : stageB 0 v = 0 := by simp [stageB]
@[simp] theorem stageC_zero (v : ℕ) : stageC 0 v = 0 := by simp [stageC]

/-- On a byte the stages stay inside the byte, and the last one holds its set-bit count. -/
theorem byte_pipeline {e : ℕ} (he : e < 256) :
    stageA 1 e < 256 ∧ stageB 1 e ≤ 68 ∧ stageB 1 e % 16 ≤ 4 ∧ stageC 1 e ≤ 8 ∧
      stageC 1 e = bitSum e 8 := by decide +kernel +revert

/-! ## Peeling one byte -/

def isBytewise (f : ℕ → ℕ → ℕ) : Prop :=
  ∀ v k, f v (k + 1) = f (v % 256) 1 + 256 * f (v / 256) k

lemma isBytewise.eq {f : ℕ → ℕ → ℕ} (hf : isBytewise f) {v k : ℕ} :
    f v (k + 1) = f (v % 256) 1 + 256 * f (v / 256) k :=
  hf v k

lemma isBytewise_id : isBytewise fun v _ ↦ v := by grind [isBytewise, Nat.mod_add_div]

lemma isBytewise.add {f g : ℕ → ℕ → ℕ} (hf : isBytewise f) (hg : isBytewise g) :
    isBytewise fun v k ↦ f v k + g v k := by grind [isBytewise]

lemma isBytewise.sub {f g : ℕ → ℕ → ℕ} (hf : isBytewise f) (hg : isBytewise g)
    (hfg : ∀ v k, g v k ≤ f v k) :
    isBytewise fun v k ↦ f v k - g v k := by grind [isBytewise]

theorem isBytewise.land {f g : ℕ → ℕ → ℕ} (hf : isBytewise f) (hg : isBytewise g)
    (hf' : ∀ v < 256, f v 1 < 256) (hg' : ∀ v < 256, g v 1 < 256) :
    isBytewise fun v k ↦ f v k &&& g v k := fun v k ↦ by
  simp only [hf v k, hg v k]
  rw [land_split' (hf' _ (Nat.mod_lt _ (by lia))) (hg' _ (Nat.mod_lt _ (by lia)))]

lemma isBytewise.of_shiftLeft {s : ℕ} {f : ℕ → ℕ → ℕ}
    (h : isBytewise fun v k ↦ f v k <<< s) : isBytewise f := fun v k ↦
  Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos s) (by grind [isBytewise, Nat.shiftLeft_eq])

theorem isBytewise_rep {m : ℕ} : isBytewise fun _ k ↦ rep m k := fun v k ↦ by simp

/-- A repeated-byte mask splits at the byte boundary. -/
theorem land_rep_succ {v m k : ℕ} (hm : m < 256) :
    v &&& rep m (k + 1) = (v % 256 &&& m) + 256 * (v / 256 &&& rep m k) := by
  grind [land_split_byte, rep_mod_byte, rep_div_byte]

theorem isBytewise.shiftRight_land_rep {f : ℕ → ℕ → ℕ} (hf : isBytewise f)
    (hf' : ∀ v < 256, f v 1 < 256) {m s : ℕ} (hms : m <<< s < 256) :
    isBytewise fun v k ↦ f v k >>> s &&& rep m k := by
  apply isBytewise.of_shiftLeft (s := s)
  simp_rw [shiftLeft_land_shiftRight, rep_mul_two_pow]
  exact isBytewise.land hf isBytewise_rep hf' (by simp [hms])

theorem land_shiftRight_rep_succ' {m s : ℕ} (hs : s ≤ 8) (hm : m < 2 ^ (8 - s)) :
    isBytewise fun v k ↦ v >>> s &&& rep m k := by
  refine isBytewise.shiftRight_land_rep isBytewise_id (by simp) ?_
  grw [Nat.shiftLeft_eq, hm, ← Nat.pow_add]
  grind

theorem isBytewise_stageA : isBytewise fun v k ↦ stageA k v :=
  isBytewise_id.sub (land_shiftRight_rep_succ' (by simp) (by simp))
    (by grind [Nat.and_le_left, Nat.shiftRight_le])

theorem isBytewise_stageB : isBytewise fun v k ↦ stageB k v :=
  (isBytewise.land isBytewise_stageA isBytewise_rep (by grind [byte_pipeline]) (by simp)).add
    (isBytewise.shiftRight_land_rep isBytewise_stageA (by grind [byte_pipeline]) (by simp))

theorem stageB_mod_16 (k v : ℕ) : stageB k v % 16 ≤ 4 := by
  cases k with grind
    [stageB_zero, isBytewise_stageB.eq, byte_pipeline (e := v % 256) (Nat.mod_lt _ (by lia))]

/-- The last stage of a two-byte value splits into the stages of its bytes. -/
theorem stageC_byte_split {a b k : ℕ} (ha : a ≤ 68) (hb : b % 16 ≤ 4) :
    (a + 256 * b + ((a + 256 * b) >>> 4)) &&& rep 15 (k + 1)
      = ((a + a >>> 4) &&& 15) + 256 * ((b + b >>> 4) &&& rep 15 k) := by
  grind [land_rep_succ, land_15, Nat.shiftRight_eq_div_pow]

/-- Adding a value to itself shifted right by 4 and masking to 4-bit groups splits at the byte
boundary, given the bounds the previous stage supplies. -/
theorem isBytewise.add_shiftRight_land_15 {f : ℕ → ℕ → ℕ} (hf : isBytewise f)
    (hbyte : ∀ v < 256, f v 1 ≤ 68) (hmod : ∀ v k, f v k % 16 ≤ 4) :
    isBytewise fun v k ↦ (f v k + f v k >>> 4) &&& rep 15 k := fun v k ↦ by
  simpa [hf v k] using stageC_byte_split (hbyte _ (Nat.mod_lt _ (by lia))) (hmod _ _)

theorem isBytewise_stageC : isBytewise fun v k ↦ stageC k v :=
  isBytewise_stageB.add_shiftRight_land_15 (fun _ hv ↦ (byte_pipeline hv).2.1)
    fun v k ↦ stageB_mod_16 k v

theorem stageC_succ (k v : ℕ) :
    stageC (k + 1) v = stageC 1 (v % 256) + 256 * stageC k (v / 256) :=
  isBytewise_stageC.eq

/-! ## The word count from the byte counts -/

theorem shiftRight_mod_two (x i : ℕ) : (x >>> i) % 2 = if x.testBit i then 1 else 0 := by
  grind [Nat.shiftRight_eq_div_pow]

/-- The count as the size of the set of set positions. -/
public theorem bitSum_eq_card (v n : ℕ) :
    bitSum v n = {i ∈ Finset.range n | v.testBit i}.card := by
  grind [bitSum, Finset.card_filter, Nat.shiftRight_eq_div_pow]

/-- A count over `s` positions reads only the value modulo `2 ^ s`. -/
public theorem bitSum_mod (v s : ℕ) : bitSum (v % 2 ^ s) s = bitSum v s :=
  Finset.sum_congr rfl fun i hi ↦ by grind [shiftRight_mod_two]

/-- Splitting the range at `s` splits the count. -/
public theorem bitSum_add (v s t : ℕ) : bitSum v (s + t) = bitSum v s + bitSum (v / 2 ^ s) t := by
  grind [bitSum, Finset.sum_range_add, Finset.sum_congr, Nat.shiftRight_eq_div_pow, Nat.pow_add,
    Nat.div_div_eq_div_mul]

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

/-! ## The merge -/

/-- Sum of the low `k` bytes of `v`. -/
public def byteSum : ℕ → ℕ → ℕ
  | _, 0 => 0
  | v, k + 1 => v % 256 + byteSum (v / 256) k

@[simp] theorem byteSum_zero (v : ℕ) : byteSum v 0 = 0 := rfl

theorem byteSum_succ (v k : ℕ) : byteSum v (k + 1) = v % 256 + byteSum (v / 256) k := rfl

/-- Multiplying by `rep 1 (k + 1)` places the sum of the low `k + 1` bytes in byte `k`, over a low
part bounded by that sum. -/
theorem mul_rep_split (k v : ℕ) :
    ∃ L T, L ≤ byteSum v (k + 1) * rep 1 k ∧
      v * rep 1 (k + 1) = L + 256 ^ k * (byteSum v (k + 1) + 256 * T) := by
  induction k generalizing v with
  | zero => exact ⟨0, v / 256, by simp, by grind [byteSum_succ, byteSum_zero]⟩
  | succ k ih =>
    obtain ⟨L, T, hL, hLT⟩ := ih (v / 256)
    have h1 : 256 * rep 1 k ≤ rep 1 (k + 1) := by grind
    have hw : v = v % 256 + 256 * (v / 256) := by lia
    refine ⟨v % 256 * rep 1 (k + 1) + 256 * L, T + v / 256, ?_, ?_⟩
    · have h2 : 256 * L ≤ byteSum (v / 256) (k + 1) * rep 1 (k + 1) := by
        grind [Nat.mul_le_mul_left 256 hL,
          Nat.mul_le_mul_left (byteSum (v / 256) (k + 1)) h1]
      rw [byteSum_succ, add_mul]
      lia
    · grind [byteSum_succ, rep_succ_top]

/-- The multiplication by `rep 1 (k + 1)` reads the sum of the low `k + 1` bytes off byte `k`. -/
theorem byteSum_mul_rep {k v : ℕ} (h : byteSum v (k + 1) < 256) :
    v * rep 1 (k + 1) / 256 ^ k % 256 = byteSum v (k + 1) := by
  obtain ⟨L, T, hL, hLT⟩ := mul_rep_split k v
  have h255 : byteSum v (k + 1) * rep 1 k ≤ 255 * rep 1 k := Nat.mul_le_mul_right _ (by lia)
  have hlt : L < 256 ^ k := by grind [rep_one_mul]
  rw [hLT, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt]
  lia

/-- The last stage of a byte holds the count of that byte. -/
theorem stageC_byte (v : ℕ) : stageC 1 (v % 256) = bitSum v 8 :=
  (byte_pipeline (Nat.mod_lt _ (by lia))).2.2.2.2.trans (by simpa using bitSum_mod v 8)

/-- The bytes of the last stage sum to the count of the word. -/
theorem byteSum_stageC (k v : ℕ) : byteSum (stageC k v) k = bitSum v (8 * k) := by
  induction k generalizing v with
  | zero => simp [bitSum]
  | succ k ih =>
    have hb : stageC 1 (v % 256) ≤ 8 := (byte_pipeline (Nat.mod_lt _ (by lia))).2.2.2.1
    grind [byteSum_succ, stageC_succ, bitSum_add v 8 (8 * k), stageC_byte]

/-- The pipeline over `k + 1` bytes counts the set bits of those bytes. -/
theorem stageC_mul_rep {k : ℕ} (hk : k < 31) (v : ℕ) :
    stageC (k + 1) v * rep 1 (k + 1) / 256 ^ k % 256 = bitSum v (8 * (k + 1)) := by
  grind [byteSum_mul_rep, byteSum_stageC, bitSum_le]

/-- `popc64K` counts the set bits of a 64-bit word. -/
public theorem popc64K_eq_bitSum (v : ℕ) : popc64K v = bitSum v 64 := by
  rw [popc64K_eq', Nat.shiftRight_eq_div_pow, land_255, (by norm_num : (2 : ℕ) ^ 56 = 256 ^ 7)]
  simpa using stageC_mul_rep (k := 7) (by norm_num) v

end PrimeCert
