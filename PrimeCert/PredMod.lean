/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.Util

/-! # Efficient implementation of (n - 1) % N -/

def predModKR (a N : Nat) : Nat :=
  a.rec (predKR N) fun a _ ↦ a

theorem predModKR_eq {a N : Nat} (hn : N ≠ 0) (ha : a ≤ N) :
    predModKR a N = (a + (N - 1)) % N := by
  delta predModKR
  cases a with
  | zero => rw [Nat.zero_add, Nat.mod_eq_of_lt (by grind), predKR_eq_pred]; rfl
  | succ a =>
    rw [Nat.add_assoc, ← Nat.succ_eq_one_add, ← Nat.pred_eq_sub_one, Nat.succ_pred hn,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by grind), ← Nat.succ_eq_add_one]
