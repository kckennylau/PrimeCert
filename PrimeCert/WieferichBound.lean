/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import PrimeCert.Wieferich

/-! # From the classwise folds to a statement about a prime

The sieve holds one bit per number coprime to 6; `wheelIndex n` is the position of `n`. These
lemmas read that position back and track it along a residue class.
-/

namespace PrimeCert.Wieferich

open PrimeCert PrimeCert.Sieve

public theorem wheelIndex_one {n : ℕ} (h : n % 6 = 1) : wheelIndex n = (n - 1) / 3 := by
  have hb : ((n % 6).beq 1) = true := by simp [h]
  simp [wheelIndex, hb]

public theorem wheelIndex_five {n : ℕ} (h : n % 6 = 5) : wheelIndex n = (n - 2) / 3 := by
  have hb : ((n % 6).beq 1) = false := by rw [h]; rfl
  simp [wheelIndex, hb]

/-- The sieve index of a number coprime to 6 names that number back. -/
public theorem num_wheelIndex {n : ℕ} (h : n % 6 = 1 ∨ n % 6 = 5) : num (wheelIndex n) = n := by
  rcases h with h | h
  · rw [wheelIndex_one h]; grind [num]
  · rw [wheelIndex_five h]; grind [num]

/-- Along the class of `r`, successive members sit at indices in steps of `m / 3`. -/
public theorem wheelIndex_add {r m k : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5) (hm : m % 6 = 0)
    (h1 : 1 ≤ r) : wheelIndex (r + m * k) = wheelIndex r + (m / 3) * k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 6 * j := ⟨m / 6, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, j * k = c := ⟨_, rfl⟩
  have e1 : 6 * j * k = 6 * c := by rw [mul_assoc, hc]
  have e2 : 6 * j / 3 * k = 2 * c := by rw [show 6 * j / 3 = 2 * j by omega, mul_assoc, hc]
  rw [e1, e2]
  rcases hr with h | h
  · obtain ⟨i, rfl⟩ : ∃ i, r = 6 * i + 1 := ⟨r / 6, by omega⟩
    rw [wheelIndex_one (by omega), wheelIndex_one h]
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, r = 6 * i + 5 := ⟨r / 6, by omega⟩
    rw [wheelIndex_five (by omega), wheelIndex_five h]
    omega

end PrimeCert.Wieferich
