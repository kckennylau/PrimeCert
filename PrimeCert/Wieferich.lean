/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.ModEq
import PrimeCert.PowMod

/-! # Checking for Wieferich primes

We seek solutions to `2^(p-1) ≡ 1 [MOD p^2]`. Until 2025, the only known such primes are 1093 and
3511.

-/

section forallB

-- MOVE
def forallB (f : ℕ → Bool) (start len : ℕ) (step : ℕ := 1) : Bool :=
  (Nat.rec (motive := fun _ ↦ ℕ × Bool) (start, true)
    (fun _ ih ↦ ih.rec fun i b ↦ (i.add step, f i && b)) len).2

theorem forallB_iff_range' (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n ∈ List.range' start len step, f n := by
  unfold forallB
  induction len with
  | zero => simp
  | succ len ih =>
    simp only [Bool.and_eq_true, ih, List.range'_concat, List.forall_mem_append,
      List.forall_mem_singleton, and_comm]
    refine and_congr_left fun _a ↦ Eq.congr_left <| congr_arg f ?_
    clear ih _a
    induction len with
    | zero => simp
    | succ len ih => simp only; rw [ih, Nat.add_eq, mul_add_one, add_assoc]

theorem forallB_iff (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n < len, f (n * step + start) := by
  simp_rw [add_comm, mul_comm, forallB_iff_range', List.mem_range']; aesop

theorem forallB_iff' (f : ℕ → Bool) (start r len step : ℕ) :
    forallB f (start * step + r) len step ↔
    ∀ n, start ≤ n → n < start + len → f (n * step + r) := by
  simp_rw [forallB_iff, ← add_assoc, ← add_mul, le_iff_exists_add, exists_imp,
    forall_eq_apply_imp_iff, add_lt_add_iff_left, add_comm]

theorem forallB_one_iff (f : ℕ → Bool) (start len : ℕ) :
    forallB f start len ↔ ∀ n, start ≤ n → n < start + len → f n := by
  simp_rw [forallB_iff_range', List.mem_range'_1, and_imp]

end forallB

section forall_step

theorem forall_start {P : ℕ → Prop} {hi : ℕ}
    (ih : ∀ n, 0 ≤ n → n < hi → P n) : ∀ n < hi, P n :=
  fun n hn ↦ ih n n.zero_le hn

theorem forall_step {P : ℕ → Prop} {curr hi : ℕ} (next : ℕ)
    (now : P curr) (h : curr.succ = next) (ih : ∀ n, next ≤ n → n < hi → P n) :
    ∀ n, curr ≤ n → n < hi → P n :=
  fun n hn₁ hn₂ ↦ (eq_or_lt_of_le hn₁).elim (· ▸ now) fun hn₃ ↦ ih n (h ▸ hn₃) hn₂

theorem forall_last {P : ℕ → Prop} {hi : ℕ} :
    ∀ n, hi ≤ n → n < hi → P n :=
  fun _ hn₁ hn₂ ↦ (not_lt_of_ge hn₁ hn₂).elim

end forall_step
-- END MOVE

--    1, 1093, 3511
-- => 0,  546, 1755

-- #time
-- theorem wieferich_100 : ∀ n < 100, Nat.blt 1 (powModTR 4 n (n.mul 2 |>.succ |>.pow 2)) ||
--     n.beq 0 || n.beq 546 || n.beq 1755 :=
--   by decide

-- set_option maxRecDepth 10000 in
-- #time -- 796 ms
-- #reduce Nat.rec (motive := fun _ ↦ Nat × Bool) (4001, true)
--   (fun _ ih ↦ ih.rec fun n b ↦ (n.add 2, Nat.blt 1 (powModTR 2 n.pred (n.mul n)) && b)) 1000

-- #time -- 228 ms
-- #eval Nat.rec (motive := fun _ ↦ Nat × Bool) (4001, true)
--   (fun _ ih ↦ ih.rec fun n b ↦ (n.add 2, Nat.blt 1 (powModTR' 2 n.pred (n.mul n)) && b)) 1000

def Wieferich (p : ℕ) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p ^ 2]

noncomputable def wieferichKR (p : ℕ) : Bool :=
  powModTR 2 p.pred (p.pow 2) |>.beq 1

theorem wieferichKR_iff (p : ℕ) (hp : p ≠ 1) : wieferichKR p ↔ Wieferich p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Wieferich, wieferichKR, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModTR_eq, powMod, Nat.pow_eq, Nat.pred_eq_sub_one]

open Lean Meta

def checkWieferich (start step len : ℕ) : Expr :=
  have startE : Expr := mkRawNatLit start
  have stepE : Expr := mkRawNatLit step
  have lenE : Expr := mkRawNatLit len
  -- n ↦ !wieferichKR (n * step + start) = true
  have e₁ : Expr := mkApp2 (mkConst ``Nat.mul) (.bvar 0) stepE
  have e₂ : Expr := mkApp2 (mkConst ``Nat.add) e₁ startE
  have e₃ : Expr := mkApp (mkConst ``Bool.not) (mkApp (mkConst ``wieferichKR) e₂)
  have e₄ : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e₃ (mkConst ``true)
  have PE : Expr := .lam `n (mkConst ``Nat) e₄ default
  have e₅ : Expr := mkApp2 (mkConst ``forall_last) PE lenE
  let rec go (curr : ℕ) : Expr :=
    if curr < len then
      mkApp7 (mkConst ``forall_step) PE (mkRawNatLit curr) lenE (mkRawNatLit curr.succ)
        reflBoolTrue (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit curr.succ))
        (go curr.succ)
      else e₅
  mkApp3 (mkConst ``forall_start) PE lenE (go 0)

elab "check_wieferich% " start:num step:num len:num : term =>
  return checkWieferich start.getNat step.getNat len.getNat

/-! # We check odd numbers from 4001 to 6001 -/

set_option trace.profiler true
set_option trace.profiler.threshold 0
set_option maxRecDepth 99999

-- elab 18 ms
-- kernel 533 ms
theorem wieferich1 : ∀ n < 1000, !wieferichKR (n.mul 2 |>.add 4001) :=
  check_wieferich% 4001 2 1000

-- elab 1322 ms
-- kernel 413 ms
theorem wieferich2 : forallB (!wieferichKR ·) 4001 1000 2 :=
  eagerReduce (Eq.refl true)
