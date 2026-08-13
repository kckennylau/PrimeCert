/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Field
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.Ring.Parity

/-!
# The stride masks and the parity table

`strideMaskK q M rounds` has bit `j` set, for `j ≤ M`, exactly at the positive multiples of `q`
(`testBit_strideMaskK`), given `M < q * 2 ^ rounds` so that the doubling reaches the top of the
table. One step of `lamLoopK` flips those bits, so bit `j` of the table counts, modulo 2, the
fields dividing `j` (`testBit_lamLoopK`).
-/

namespace PrimeCert.Polya

open Nat

/-! ## The stride mask -/

theorem strideMaskK_zero (q M : ℕ) : strideMaskK q M 0 = 2 ^ q := Nat.one_shiftLeft q

theorem strideMaskK_succ (q M r : ℕ) :
    strideMaskK q M (r + 1)
      = ((q <<< r).ble M).rec (strideMaskK q M r)
          (strideMaskK q M r ||| (strideMaskK q M r <<< (q <<< r))) := rfl

theorem strideMaskK_succ_of_le {q M r : ℕ} (h : q <<< r ≤ M) :
    strideMaskK q M (r + 1) = strideMaskK q M r ||| (strideMaskK q M r <<< (q <<< r)) := by
  have hb : (q <<< r).ble M = true := by simpa using h
  rw [strideMaskK_succ, hb]

theorem strideMaskK_succ_of_gt {q M r : ℕ} (h : M < q <<< r) :
    strideMaskK q M (r + 1) = strideMaskK q M r := by
  have hb : (q <<< r).ble M = false := by
    simp only [Bool.eq_false_iff, ne_eq, Nat.ble_eq]
    omega
  rw [strideMaskK_succ, hb]

/-- Every set bit of a stride mask sits at a positive multiple of `q`. -/
public theorem dvd_of_testBit_strideMaskK {q M r j : ℕ} (hq : 0 < q)
    (h : (strideMaskK q M r).testBit j = true) : q ∣ j ∧ j ≠ 0 := by
  induction r generalizing j with
  | zero =>
    rw [strideMaskK_zero, Nat.testBit_two_pow] at h
    have hqj : q = j := by simpa using h
    exact ⟨⟨1, by omega⟩, by omega⟩
  | succ r ih =>
    rcases le_or_gt (q <<< r) M with hle | hgt
    · rw [strideMaskK_succ_of_le hle, Nat.testBit_or, Nat.testBit_shiftLeft] at h
      rcases Bool.or_eq_true_iff.1 h with h1 | h1
      · exact ih h1
      · obtain ⟨hge, h2⟩ := Bool.and_eq_true_iff.1 h1
        have hge' : q <<< r ≤ j := by simpa using hge
        have hspos : 0 < q <<< r := by
          rw [Nat.shiftLeft_eq]
          exact Nat.mul_pos hq (Nat.two_pow_pos r)
        have hs : q ∣ q <<< r := by
          rw [Nat.shiftLeft_eq]
          exact ⟨2 ^ r, rfl⟩
        obtain ⟨hd, _⟩ := ih h2
        have hsum := Nat.dvd_add hd hs
        rw [Nat.sub_add_cancel hge'] at hsum
        exact ⟨hsum, by omega⟩
    · rw [strideMaskK_succ_of_gt hgt] at h
      exact ih h

/-- Every positive multiple of `q` inside the table is a set bit, once the doubling has run far
enough to reach it. -/
public theorem testBit_strideMaskK_of_dvd {q M r j : ℕ} (hq : 0 < q) (hdvd : q ∣ j) (hj : 0 < j)
    (hjM : j ≤ M) (hjr : j ≤ q * 2 ^ r) : (strideMaskK q M r).testBit j = true := by
  induction r generalizing j with
  | zero =>
    obtain ⟨c, rfl⟩ := hdvd
    have hc : c = 1 := by
      have h1 : q * c ≤ q * 1 := by simpa using hjr
      have h2 := Nat.le_of_mul_le_mul_left h1 hq
      rcases Nat.eq_zero_or_pos c with rfl | h3
      · simp at hj
      · omega
    rw [hc, Nat.mul_one, strideMaskK_zero, Nat.testBit_two_pow]
    simp
  | succ r ih =>
    have hpow : q * 2 ^ (r + 1) = q * 2 ^ r + q * 2 ^ r := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
    have hs : q <<< r = q * 2 ^ r := Nat.shiftLeft_eq _ _
    rcases le_or_gt j (q * 2 ^ r) with hle | hgt
    · have hprev := ih hdvd hj hjM hle
      rcases le_or_gt (q <<< r) M with h1 | h1
      · rw [strideMaskK_succ_of_le h1, Nat.testBit_or, hprev]
        simp
      · rw [strideMaskK_succ_of_gt h1]
        exact hprev
    · have hsM : q <<< r ≤ M := by omega
      rw [strideMaskK_succ_of_le hsM, Nat.testBit_or, Nat.testBit_shiftLeft]
      have hsub : (strideMaskK q M r).testBit (j - q <<< r) = true := by
        refine ih (Nat.dvd_sub hdvd ?_) (by omega) (by omega) (by omega)
        rw [hs]
        exact ⟨2 ^ r, rfl⟩
      have hge : q <<< r ≤ j := by omega
      rw [hsub]
      simp [hge]

/-- Inside the table, a stride mask marks exactly the positive multiples of `q`. -/
public theorem testBit_strideMaskK {q M r j : ℕ} (hq : 0 < q) (hjM : j ≤ M)
    (hM : M < q * 2 ^ r) :
    (strideMaskK q M r).testBit j = decide (q ∣ j ∧ j ≠ 0) := by
  by_cases hd : q ∣ j ∧ j ≠ 0
  · rw [decide_eq_true hd]
    exact testBit_strideMaskK_of_dvd hq hd.1 (Nat.pos_of_ne_zero hd.2) hjM (by omega)
  · rw [decide_eq_false hd]
    by_contra hcon
    exact hd (dvd_of_testBit_strideMaskK hq (by simpa using hcon))

/-- Position `0` is no multiple of a positive stride. -/
public theorem testBit_strideMaskK_zero {q M r : ℕ} (hq : 0 < q) :
    (strideMaskK q M r).testBit 0 = false := by
  rcases Bool.eq_false_or_eq_true ((strideMaskK q M r).testBit 0) with h | h
  · exact absurd (dvd_of_testBit_strideMaskK hq h).2 (by simp)
  · exact h

/-! ## One step of the table -/

/-- Inside the table, one step flips the bits at the multiples of the stride. -/
public theorem testBit_markStrideK {lam q M r j : ℕ} (hj : j ≤ M) :
    (markStrideK lam q M r).testBit j
      = Bool.xor (lam.testBit j) ((strideMaskK q M r).testBit j) := by
  simp only [markStrideK, Nat.land_eq, Nat.xor_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.one_shiftLeft,
    Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, Nat.testBit_xor]
  simp [Nat.lt_succ_of_le hj]

/-- A step leaves the table `M + 1` bits wide. -/
public theorem markStrideK_lt (lam q M r : ℕ) : markStrideK lam q M r < 2 ^ (M + 1) := by
  simp only [markStrideK, Nat.land_eq, Nat.xor_eq, Nat.sub_eq, Nat.shiftLeft_eq',
    Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The whole table is `M + 1` bits wide. -/
public theorem lamK_lt (qs w M r cnt : ℕ) : lamK qs w M r cnt < 2 ^ (M + 1) := by
  rw [lamK]
  cases cnt with
  | zero =>
    have h0 : lamLoopK qs w M r 0 0 0 = 0 := rfl
    rw [h0]
    exact Nat.two_pow_pos _
  | succ c =>
    rw [lamLoopK_succ]
    exact markStrideK_lt _ _ _ _

/-! ## The parity table -/

/-- Bit `j` of the table after `fuel` steps flips once per field dividing `j`. -/
public theorem testBit_lamLoopK {qs w M r lam start fuel j : ℕ} (hj : j ≤ M) (hjpos : 0 < j)
    (hfield : ∀ i < fuel, 0 < fieldK qs w (start + i) ∧ M < fieldK qs w (start + i) * 2 ^ r) :
    (lamLoopK qs w M r lam start fuel).testBit j
      = Bool.xor (lam.testBit j)
          (decide (Odd ({i ∈ Finset.range fuel | fieldK qs w (start + i) ∣ j}).card)) := by
  induction fuel with
  | zero => simp [lamLoopK]
  | succ f ih =>
    obtain ⟨hpos, hround⟩ := hfield f (by omega)
    rw [lamLoopK_succ, testBit_markStrideK hj, ih fun i hi => hfield i (by omega),
      testBit_strideMaskK hpos hj hround, Finset.range_add_one, Finset.filter_insert]
    have hnot : f ∉ {i ∈ Finset.range f | fieldK qs w (start + i) ∣ j} := by simp
    by_cases hdvd : fieldK qs w (start + f) ∣ j
    · rw [if_pos hdvd, Finset.card_insert_of_notMem hnot]
      simp only [hdvd, ne_eq, hjpos.ne', not_false_eq_true, and_self, decide_true,
        Nat.odd_add_one]
      cases lam.testBit j <;>
        cases Decidable.em (Odd ({i ∈ Finset.range f | fieldK qs w (start + i) ∣ j}).card) <;>
        simp_all
    · rw [if_neg hdvd]
      simp [hdvd]

/-- Position `0` stays clear: every stride is positive. -/
public theorem testBit_lamLoopK_zero {qs w M r lam start fuel : ℕ} (h0 : lam.testBit 0 = false)
    (hfield : ∀ i < fuel, 0 < fieldK qs w (start + i)) :
    (lamLoopK qs w M r lam start fuel).testBit 0 = false := by
  induction fuel with
  | zero => simpa [lamLoopK] using h0
  | succ f ih =>
    rw [lamLoopK_succ, testBit_markStrideK (Nat.zero_le M), ih fun i hi => hfield i (by omega),
      testBit_strideMaskK_zero (hfield f (by omega))]
    simp

end PrimeCert.Polya
