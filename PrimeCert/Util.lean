/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Init

def Nat.eager (k : Nat → Nat) (n : Nat) : Nat := n.rec (k 0) (fun n _ ↦ k n.succ)

@[simp] theorem Nat.eager_eq {n : Nat} {k : Nat → Nat} : n.eager k = k n := by
  cases n <;> simp [eager]

theorem Bool.rec_eq_ite {α : Type*} {b : Bool} {t f : α} : b.rec f t = if b then t else f := by
  cases b <;> simp

@[simp] theorem Nat.mod_eq_mod {a b : Nat} : a.mod b = a % b := rfl
@[simp] theorem Nat.div_eq_div {a b : Nat} : a.div b = a / b := rfl
@[simp] theorem Nat.land_eq_land {a b : Nat} : a.land b = a &&& b := rfl

def predKR (N : Nat) : Nat := N.rec 0 (fun n _ ↦ n)

theorem predKR_eq_pred {N : Nat} : predKR N = N.pred := by cases N <;> rfl
