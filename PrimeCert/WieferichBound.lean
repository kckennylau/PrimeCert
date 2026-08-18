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

end PrimeCert.Wieferich
