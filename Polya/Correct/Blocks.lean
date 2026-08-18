/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Runs
public import Polya.Correct.Tables
public import Polya.Correct.PowerPack

/-!
# The block loop accumulates the recurrence

One step of `blockStepK` covers the whole run of indices sharing a quotient, reading that
quotient's value of `L` off one of the two tables. The state holds the next index and two
accumulators standing for their difference (`blockLoopK_spec`); a final index of `v + 1` with the
second accumulator at `off * (v - 1)` says the run covered `2 … v` exactly (`blockLoopK_sum`).
-/

namespace PrimeCert.Polya

set_option maxRecDepth 100000

/-- One block in arithmetic form. -/
theorem blockStepK_eq (x v rootx low hi wb off st : ℕ) :
    blockStepK x v rootx low hi wb off st =
      st - st % 2 ^ 64 + (v / (v / (st % 2 ^ 64)) + 1) +
        ((v / (v / (st % 2 ^ 64)) - st % 2 ^ 64 + 1) *
            (if v / (st % 2 ^ 64) ≤ rootx then fieldK low wb (v / (st % 2 ^ 64))
              else fieldK hi wb (x / (v / (st % 2 ^ 64)))) * 2 ^ 64 +
          (v / (v / (st % 2 ^ 64)) - st % 2 ^ 64 + 1) * off * 2 ^ 128) := by
  unfold blockStepK
  simp only [bool_rec_ble_eq, Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul,
    Nat.and_two_pow_sub_one_eq_mod, Nat.sub_eq, Nat.add_eq, Nat.mul_eq, Nat.div_eq_div,
    Nat.succ_eq_add_one]

/-- The tables hold `L` at every quotient of `v`, offset by `off`. -/
@[expose] public def BlockValues (x v rootx low hi wb off : ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ v →
    ((if v / k ≤ rootx then fieldK low wb (v / k) else fieldK hi wb (x / (v / k))) : ℤ)
      = L (v / k) + off

/-- The loop from a state covering `2 … k₀ - 1`: either it covers an initial segment of the
indices, or its second accumulator has run past what any such segment allows. -/
theorem blockLoopK_spec {x v rootx low hi wb off st k₀ A₀ B₀ : ℕ} (hv : 0 < v)
    (hv64 : v + 1 < 2 ^ 64) (hwb : 2 ^ wb ≤ 2 * off)
    (hvals : BlockValues x v rootx low hi wb off)
    (hst : st = k₀ + 2 ^ 64 * A₀ + 2 ^ 128 * B₀) (hk₀ : 2 ≤ k₀) (hk₀v : k₀ ≤ v + 1)
    (hB₀ : B₀ = off * (k₀ - 2)) (hA₀ : A₀ ≤ 2 * B₀)
    (hsum₀ : (A₀ : ℤ) - B₀ = ∑ j ∈ Finset.Ico 2 k₀, L (v / j)) (fuel : ℕ) :
    ∃ k A B, blockLoopK x v rootx low hi wb off st fuel = k + 2 ^ 64 * A + 2 ^ 128 * B ∧
      k ≤ v + 1 ∧ A ≤ 2 * B ∧
        ((2 ≤ k ∧ B = off * (k - 2) ∧ (A : ℤ) - B = ∑ j ∈ Finset.Ico 2 k, L (v / j)) ∨
          off * (v - 1) < B) := by
  induction fuel with
  | zero => exact ⟨k₀, A₀, B₀, hst, hk₀v, hA₀, Or.inl ⟨hk₀, hB₀, hsum₀⟩⟩
  | succ f ih =>
    obtain ⟨k, A, B, hstate, hkv, hA2B, hcase⟩ := ih
    rw [blockLoopK_succ, hstate, blockStepK_eq,
      (by omega : (k + 2 ^ 64 * A + 2 ^ 128 * B) % 2 ^ 64 = k),
      (by omega : k + 2 ^ 64 * A + 2 ^ 128 * B - k = 2 ^ 64 * A + 2 ^ 128 * B)]
    have hvallt : (if v / k ≤ rootx then fieldK low wb (v / k)
        else fieldK hi wb (x / (v / k))) < 2 ^ wb := by split <;> exact fieldK_lt _ _ _
    refine ⟨v / (v / k) + 1,
      A + (v / (v / k) - k + 1) *
        (if v / k ≤ rootx then fieldK low wb (v / k) else fieldK hi wb (x / (v / k))),
      B + (v / (v / k) - k + 1) * off, by ring, ?_, ?_, ?_⟩
    · have hdle : v / (v / k) ≤ v := Nat.div_le_self _ _
      omega
    · have hstep : (v / (v / k) - k + 1) *
          (if v / k ≤ rootx then fieldK low wb (v / k) else fieldK hi wb (x / (v / k)))
            ≤ 2 * ((v / (v / k) - k + 1) * off) := by
        rw [Nat.mul_left_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    · rcases hcase with ⟨hk2, hB, hsum⟩ | hbad
      · rcases Nat.lt_or_ge v k with hgt | hle
        · obtain rfl : k = v + 1 := by omega
          have hq0 : v / (v + 1) = 0 := Nat.div_eq_of_lt (by omega)
          refine Or.inr ?_
          rw [hq0, Nat.div_zero, hB, (by omega : v + 1 - 2 = v - 1),
            (by omega : 0 - (v + 1) + 1 = 1), Nat.one_mul]
          omega
        · have hkd : k ≤ v / (v / k) := le_div_div (by omega) hle
          refine Or.inl ⟨by omega, ?_, ?_⟩
          · rw [hB]
            have hcnt : v / (v / k) + 1 - 2 = k - 2 + (v / (v / k) - k + 1) := by omega
            rw [hcnt, Nat.mul_add]
            ring
          · have hblock : ∑ j ∈ Finset.Ico k (v / (v / k) + 1), L (v / j)
                = ((v / (v / k) - k + 1 : ℕ) : ℤ) * L (v / k) := by
              rw [Finset.Ico_add_one_right_eq_Icc]
              exact sum_run (by omega) hle _
            rw [← Finset.Ico_union_Ico_eq_Ico (by omega : 2 ≤ k) (by omega),
              Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 2 k _), ← hsum, hblock]
            have hvalL : ((if v / k ≤ rootx then fieldK low wb (v / k)
                else fieldK hi wb (x / (v / k))) : ℤ) = L (v / k) + off := hvals k (by omega) hle
            push_cast
            rw [hvalL]
            ring
      · exact Or.inr (by omega)

/-- Reading the three fields back off a state. -/
public theorem state_split {S k A B : ℕ} (h : S = k + 2 ^ 64 * A + 2 ^ 128 * B) (hk : k < 2 ^ 64)
    (hA : A < 2 ^ 64) : S % 2 ^ 64 = k ∧ S / 2 ^ 64 % 2 ^ 64 = A ∧ S / 2 ^ 128 = B := by omega

/-- A run of blocks ending at index `v + 1` with the second accumulator at `off * (v - 1)` has
covered `2 … v`, so the accumulators differ by the sum in the recurrence. -/
public theorem blockLoopK_sum {x v rootx low hi wb off S fuel : ℕ} (hv : 0 < v)
    (hv64 : v + 1 < 2 ^ 64) (hwb : 2 ^ wb ≤ 2 * off)
    (hvals : BlockValues x v rootx low hi wb off)
    (hfinal : blockLoopK x v rootx low hi wb off 2 fuel = S)
    (hbound : 2 * (S / 2 ^ 128) < 2 ^ 64) (hk : S % 2 ^ 64 = v + 1)
    (hB : S / 2 ^ 128 = off * (v - 1)) :
    ((S / 2 ^ 64 % 2 ^ 64 : ℕ) : ℤ) - (off * (v - 1) : ℕ) = ∑ j ∈ Finset.Ioc 1 v, L (v / j) := by
  obtain ⟨k, A, B, hstate, hkv, hA2B, hcase⟩ :=
    blockLoopK_spec (st := 2) (k₀ := 2) (A₀ := 0) (B₀ := 0) hv hv64 hwb hvals (by ring)
      (le_refl 2) (by omega) (by simp) (by simp) (by simp) fuel
  rw [hfinal] at hstate
  have hBle : B ≤ S / 2 ^ 128 := by omega
  obtain ⟨hkS, hAS, hBS⟩ := state_split hstate (by omega) (by omega)
  have hkeq : k = v + 1 := by rwa [← hkS]
  have hBeq : B = off * (v - 1) := by rwa [← hBS]
  have hset : Finset.Ico 2 (v + 1) = Finset.Ioc 1 v := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rcases hcase with ⟨-, -, hsum⟩ | hbad
  · rw [hAS, ← hBeq, hsum, hkeq, hset]
  · rw [hBeq] at hbad
    omega

end PrimeCert.Polya
