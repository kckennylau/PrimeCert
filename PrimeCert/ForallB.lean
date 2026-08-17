/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

module

import PrimeCert.PowMod
import Mathlib.Data.List.Range
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic.Ring

/-! # A kernel-reducible bounded `Bool` quantifier

`forallB f start len step` folds `f` over the `len`-term arithmetic progression
`start, start + step, …`, carrying a single `Bool` and computing each element as
`n * step + start` from the recursion index. `forallB_succ` and `forallB_zero` give the two
recursion steps, and the `forallB_iff*` lemmas rewrite the fold as an ordinary `∀`.
`List.rec_and` does the same for a `List.rec` fold of `&&` over an explicit list.
-/

public theorem List.rec_and {α : Type*} (f : α → Bool) (b : Bool) (l : List α) :
    List.rec b (fun hd _ ih ↦ f hd && ih) l = true ↔ b = true ∧ ∀ x ∈ l, f x := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp only [Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]; tauto

namespace PrimeCert

@[expose] public noncomputable def forallB (f : ℕ → Bool) (start len : ℕ) (step : ℕ := 1) : Bool :=
  len.rec true fun n b ↦ (f ((n.mul step).add start)).and' b

@[simp, grind =] public theorem forallB_zero (f : ℕ → Bool) (start step : ℕ) :
    forallB f start 0 step = true :=
  rfl

/-- One more term extends the fold by the element at index `len`. -/
@[simp, grind =] public theorem forallB_succ (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start (len + 1) step =
      (f ((len.mul step).add start)).and' (forallB f start len step) :=
  rfl

public theorem forallB_iff (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n < len, f (n * step + start) := by
  induction len with
  | zero => simp
  | succ n ih => simp [ih, Nat.forall_lt_succ_right, and_comm]

/-- Read the fold starting at `start * step + r` as a statement about the indices from `start`
to `start + len`. -/
public theorem forallB_iff' (f : ℕ → Bool) (start r len step : ℕ) :
    forallB f (start * step + r) len step ↔
    ∀ n, start ≤ n → n < start + len → f (n * step + r) := by
  simp_rw [forallB_iff, ← add_assoc, ← add_mul, le_iff_exists_add, exists_imp,
    forall_eq_apply_imp_iff, add_lt_add_iff_left, add_comm]

theorem forallB_iff_range (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n ∈ List.range' start len step, f n := by
  simp only [forallB_iff, List.mem_range', forall_exists_index, and_imp]
  grind

/-- Read the fold over `start, start + step, …` as a statement about every `n` below `len * step`
whose remainder mod `step` is `start`. -/
public theorem forallB_of_mod (f : ℕ → Bool) {start len step : ℕ}
    (h : forallB f start len step) : ∀ n < len * step, n % step = start → f n := by
  grind [forallB_iff, Nat.div_lt_of_lt_mul, Nat.div_add_mod']

end PrimeCert
