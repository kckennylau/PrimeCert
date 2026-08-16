/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/
module

/-! # Efficient computation of `(a - 1) % N`

`predModK` computes `(a + (N - 1)) % N` using `Nat.rec`, in a form the kernel reduces.
-/

/-- Kernel-reducible predecessor mod: computes `(a + (N - 1)) % N` for `a ≤ N`. -/
@[expose] public def predModK (a N : Nat) : Nat :=
  a.rec N.pred fun a _ ↦ a

public theorem predModK_eq {a N : Nat} (hn : N ≠ 0) (ha : a ≤ N) :
    predModK a N = (a + (N - 1)) % N := by
  delta predModK
  cases a with
  | zero => rw [Nat.zero_add, Nat.mod_eq_of_lt (by grind)]; rfl
  | succ a =>
    rw [Nat.add_assoc, ← Nat.succ_eq_one_add, ← Nat.pred_eq_sub_one, Nat.succ_pred hn,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by grind), ← Nat.succ_eq_add_one]
