/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF
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

theorem forall_bisect {P : ℕ → Prop} {lo hi : ℕ} (mi : ℕ)
    (h₁ : ∀ n, lo ≤ n → n < mi → P n)
    (h₂ : ∀ n, mi ≤ n → n < hi → P n) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun n hn₁ hn₂ ↦ (le_or_gt mi n).elim (h₂ n · hn₂) (h₁ n hn₁ ·)

theorem forall_succ {P : ℕ → Prop} {lo : ℕ} (h : P lo) :
    ∀ n, lo ≤ n → n < lo.succ → P n :=
  fun _n hn₁ hn₂ ↦ le_antisymm hn₁ (Nat.le_of_lt_succ hn₂) ▸ h

theorem forall_last {P : ℕ → Prop} {hi : ℕ} :
    ∀ n, hi ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ (not_lt_of_ge hn₁ hn₂).elim

theorem forall_exceed {P : ℕ → Prop} {lo hi : ℕ} (h : hi.ble lo) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ (not_le_of_gt (hn₁.trans_lt hn₂) <| Nat.le_of_ble_eq_true h).elim

open Lean Meta

def makeForallBisect' (P : Expr) (lo hi : ℕ) (pf : ℕ → Expr) : Expr :=
  if h₁ : hi ≤ lo then
    mkApp4 (mkConst ``forall_exceed) P (mkRawNatLit lo) (mkRawNatLit hi) reflBoolTrue
  else if h₂ : lo.succ = hi then
    mkApp3 (mkConst ``forall_succ) P (mkRawNatLit lo) (pf lo)
  else
    have mi := (lo + hi) / 2
    mkApp6 (mkConst ``forall_bisect) P (mkRawNatLit lo) (mkRawNatLit hi) (mkRawNatLit mi)
      (makeForallBisect' P lo mi pf)
      (makeForallBisect' P mi hi pf)

def makeForallBisect (P : Expr) (hi : ℕ) (pf : ℕ → Expr) : Expr :=
  mkApp3 (mkConst ``forall_start) P (mkRawNatLit hi) <| makeForallBisect' P 0 hi pf

end forall_step
-- END MOVE

def Wieferich (p : ℕ) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p ^ 2]

noncomputable def wieferichKR (p : ℕ) : Bool :=
  powModTR 2 p.pred (p.pow 2) |>.beq 1

theorem wieferichKR_iff (p : ℕ) (hp : p ≠ 1) : wieferichKR p ↔ Wieferich p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Wieferich, wieferichKR, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModTR_eq, powMod, Nat.pow_eq, Nat.pred_eq_sub_one]

open Lean Meta

def makeWieferichPred (start step : ℕ) : Expr :=
  have startE : Expr := mkRawNatLit start
  have stepE : Expr := mkRawNatLit step
  -- n ↦ !wieferichKR (n * step + start) = true
  have e₁ : Expr := mkApp2 (mkConst ``Nat.mul) (.bvar 0) stepE
  have e₂ : Expr := mkApp2 (mkConst ``Nat.add) e₁ startE
  have e₃ : Expr := mkApp (mkConst ``Bool.not) (mkApp (mkConst ``wieferichKR) e₂)
  have e₄ : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e₃ (mkConst ``true)
  .lam `n (mkConst ``Nat) e₄ default

def checkWieferich (start step len : ℕ) : Expr :=
  have lenE : Expr := mkRawNatLit len
  have PE : Expr := makeWieferichPred start step
  have e₅ : Expr := mkApp2 (mkConst ``forall_last) PE lenE
  let rec go (curr : ℕ) : Expr :=
    if curr < len then
      mkApp7 (mkConst ``forall_step) PE (mkRawNatLit curr) lenE (mkRawNatLit curr.succ)
        reflBoolTrue (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit curr.succ))
        (go curr.succ)
      else e₅
  mkApp3 (mkConst ``forall_start) PE lenE (go 0)

def checkWieferichBisect (start step len : ℕ) : Expr :=
  makeForallBisect (makeWieferichPred start step) len fun _ ↦ reflBoolTrue

elab "check_wieferich% " start:num step:num len:num : term =>
  return checkWieferich start.getNat step.getNat len.getNat

elab "check_wieferich_bisect% " start:num step:num len:num : term =>
  return checkWieferichBisect start.getNat step.getNat len.getNat

/-! # We check odd numbers up to 6000 -/

-- 70 ms
-- 6n+1 to 1093
theorem wieferich₁ : ∀ n < 182, !wieferichKR (n.mul 6 |>.add 1) :=
  check_wieferich% 1 6 182

-- 274 ms
-- 6n+1 from 1099 to 3511
theorem wieferich₂ : ∀ n < 402, !wieferichKR (n.mul 6 |>.add 1099) :=
  check_wieferich% 1099 6 402

-- 283 ms
-- 6n+1 from 3517 to 5000
theorem wieferich₃ : ∀ n < 414, !wieferichKR (n.mul 6 |>.add 3517) :=
  check_wieferich% 3517 6 414

-- 570 ms
-- 6n+5 to 5000
theorem wieferich₄ : ∀ n < 1000, !wieferichKR (n.mul 6 |>.add 5) :=
  check_wieferich% 5 6 1000

theorem Nat.Prime.mod_6 {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hp₃ : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h₁ := div_add_mod p 6
  have h₂ := mod_lt p (by decide : 0 < 6)
  generalize p / 6 = k at *
  generalize p % 6 = r at *
  subst p
  interval_cases r
  · rw [add_zero, prime_mul_iff, eq_false (p := Prime 6) (by decide)] at hp
    grind
  · grind
  · rw [show 6 * k + 2 = 2 * (3 * k + 1) by ring, prime_mul_iff] at hp
    grind
  · rw [show 6 * k + 3 = 3 * (2 * k + 1) by ring, prime_mul_iff] at hp
    grind
  · rw [show 6 * k + 4 = 2 * (3 * k + 2) by ring, prime_mul_iff] at hp
    grind
  · grind

theorem wieferich {p : ℕ} (hp : p.Prime) (hp₁ : p < 6000) :
    ¬(2 ^ (p - 1) ≡ 1 [MOD p^2]) ∨ ¬(3 ^ (p - 1) ≡ 1 [MOD p^2]) := by
  by_cases hp₂ : p = 2
  · rw [hp₂]; decide
  by_cases hp₃ : p = 3
  · rw [hp₃]; decide
  rw [← Wieferich, ← wieferichKR_iff _ hp.ne_one, Bool.not_eq_true, ← Bool.not_eq_true']
  rw [Nat.ModEq, ← powMod, ← powModTR_eq]
  have h₁ := hp.mod_6 hp₂ hp₃
  clear hp₂ hp₃
  have h₂ := Nat.div_lt_div_of_lt_of_dvd (d := 6) ⟨1000, by rfl⟩ hp₁
  clear hp₁
  have h₃ := Nat.div_add_mod' p 6
  generalize p / 6 = k at *
  generalize p % 6 = r at *
  subst h₃
  obtain rfl | rfl := h₁
  · obtain h₄ | rfl | h₄ := lt_trichotomy k 182
    · exact .inl <| wieferich₁ k h₄
    · exact .inr <| by decide
    obtain ⟨k, rfl⟩ := (le_iff_exists_add' (a := 183)).mp h₄
    change k + 183 < 817 + 183 at h₂
    rw [add_lt_add_iff_right] at h₂
    rw [show (k + 183) * 6 + 1 = k * 6 + 1099 by ring]
    obtain h₅ | rfl | h₅ := lt_trichotomy k 402
    · exact .inl <| wieferich₂ k h₅
    · exact .inr <| by decide
    obtain ⟨k, rfl⟩ := (le_iff_exists_add' (a := 403)).mp h₅
    change k + 403 < 414 + 403 at h₂
    rw [add_lt_add_iff_right] at h₂
    rw [show (k + 403) * 6 + 1099 = k * 6 + 3517 by ring]
    exact .inl <| wieferich₃ k h₂
  · exact .inl <| wieferich₄ k h₂

/-
set_option trace.profiler true
set_option trace.profiler.threshold 0
set_option maxRecDepth 99999

-- elab 23 ms
-- kernel 492 ms
theorem wieferich1 : ∀ n < 1000, !wieferichKR (n.mul 2 |>.add 4001) :=
  check_wieferich% 4001 2 1000

-- elab 22 ms
-- kernel 483 ms
theorem wieferich4 : ∀ n < 1000, !wieferichKR (n.mul 2 |>.add 4001) :=
  check_wieferich_bisect% 4001 2 1000

-- elab 1192 ms
-- kernel 456 ms
theorem wieferich2 : forallB (!wieferichKR ·) 4001 1000 2 :=
  rfl

-- elab 1322 ms
-- kernel 413 ms
theorem wieferich3 : forallB (!wieferichKR ·) 4001 1000 2 :=
  eagerReduce (Eq.refl true)
-/
