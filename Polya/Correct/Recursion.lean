/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Correct.Blocks
public import Polya.Theory.Identity

/-!
# The two tables through the recursion

The low table holds `L q + off` at every `q` up to `√x` and the high table holds `L (x / m) + off`
at every index `m` it has reached (`IsLowTable`, `IsHiTable`). Between them they answer every read
one block of the recurrence makes (`blockValues_of_tables`), and the value a run of blocks produces
goes back into the high table one index lower (`isHiTable_write`).
-/

namespace PrimeCert.Polya

open Nat

/-- The low table holds `L q + off` at every index up to `rootx`. -/
@[expose] public def IsLowTable (rootx off wb low : ℕ) : Prop :=
  ∀ q, q ≤ rootx → ((fieldK low wb q : ℕ) : ℤ) = L q + off

/-- The high table holds `L (x / m) + off` from index `j` up to `rootx`, and is clear below. -/
@[expose] public def IsHiTable (x rootx off wb hi j : ℕ) : Prop :=
  (∀ m, j ≤ m → m ≤ rootx → ((fieldK hi wb m : ℕ) : ℤ) = L (x / m) + off) ∧
    ∀ m, m < j → fieldK hi wb m = 0

/-- The index a high-table read uses inverts the quotient. -/
theorem div_div_div {x d : ℕ} (hd : 0 < d) (hdx : d ≤ x) : x / (x / (x / d)) = x / d :=
  div_eq_of_run hd (le_div_div hd hdx) le_rfl

/-- Between them the tables answer every read a block makes at `v = x / j`. -/
public theorem blockValues_of_tables {x rootx off wb low hi j : ℕ} (hj : 0 < j) (hjr : j ≤ rootx)
    (hroot : x < (rootx + 1) * (rootx + 1))
    (hlow : IsLowTable rootx off wb low) (hhi : IsHiTable x rootx off wb hi (j + 1)) :
    BlockValues x (x / j) rootx low hi wb off := by
  intro k hk hkv
  have hjk : x / j / k = x / (j * k) := Nat.div_div_eq_div_mul x j k
  rcases Nat.lt_or_ge rootx (x / j / k) with hgt | hle
  · rw [if_neg (by omega)]
    have hjkpos : 0 < j * k := by positivity
    have hjkx : j * k ≤ x := by
      by_contra hlt
      have : x / (j * k) = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hminv : x / (x / (x / (j * k))) = x / (j * k) := div_div_div hjkpos hjkx
    have hmge : j * k ≤ x / (x / (j * k)) := le_div_div hjkpos hjkx
    have hmle : x / (x / j / k) ≤ rootx := by
      rw [hjk]
      by_contra hgt'
      have h2 : (rootx + 1) * (x / (j * k)) ≤ x := (Nat.le_div_iff_mul_le (by omega)).1 (by omega)
      nlinarith
    obtain ⟨hval, -⟩ := hhi
    have hread : ((fieldK hi wb (x / (x / j / k)) : ℕ) : ℤ)
        = L (x / (x / (x / j / k))) + off := by
      refine hval _ ?_ hmle
      rw [hjk]
      have hk2 : j + 1 ≤ j * k := by
        have : j * 2 ≤ j * k := Nat.mul_le_mul_left j hk
        omega
      omega
    have hqq : x / (x / (x / j / k)) = x / j / k := by rw [hjk, hminv]
    rw [hread, hqq]
  · rw [if_pos hle]
    exact hlow _ hle

/-- Writing the value at index `j` extends the high table by one index. -/
public theorem isHiTable_write {x rootx off wb hi j val : ℕ} (hj : 0 < j) (hjr : j ≤ rootx)
    (h : IsHiTable x rootx off wb hi (j + 1)) (hval : (val : ℤ) = L (x / j) + off)
    (hvlt : val < 2 ^ wb) : IsHiTable x rootx off wb (hi ||| val <<< (wb * j)) j := by
  obtain ⟨hfields, hzero⟩ := h
  refine ⟨fun m hm hmr => ?_, fun m hm => ?_⟩
  · rcases Nat.lt_or_ge j m with hlt | hge
    · rw [fieldK_lor_shiftLeft_ne hvlt (by omega)]
      exact hfields m (by omega) hmr
    · have hmj : m = j := by omega
      subst hmj
      rwa [fieldK_lor_shiftLeft_of_zero (hzero m (by omega)) hvlt]
  · rw [fieldK_lor_shiftLeft_ne hvlt (by omega)]
    exact hzero m (by omega)

/-- The value a run of blocks produces at `v`: the square root less the accumulated sum. -/
public theorem L_eq_of_blockLoopK {x v rootx low hi wb off S fuel : ℕ}
    (hv : 0 < v) (hv64 : v + 1 < 2 ^ 64) (hwb : 2 ^ wb ≤ 2 * off)
    (hvals : BlockValues x v rootx low hi wb off)
    (hfinal : blockLoopK x v rootx low hi wb off 2 fuel = S)
    (hbound : 2 * (S / 2 ^ 128) < 2 ^ 64) (hk : S % 2 ^ 64 = v + 1)
    (hB : S / 2 ^ 128 = off * (v - 1)) :
    L v = (Nat.sqrt v : ℤ) - ((S / 2 ^ 64 % 2 ^ 64 : ℕ) : ℤ) + (off * (v - 1) : ℕ) := by
  have hsum := blockLoopK_sum hv hv64 hwb hvals hfinal hbound hk hB
  rw [L_eq_sqrt_sub hv, ← hsum]
  ring

end PrimeCert.Polya
