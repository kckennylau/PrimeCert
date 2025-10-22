/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Nat.Totient
import PrimeCert.PowMod

/-! # Checking for Wieferich primes

We seek solutions to `2^(p-1) ≡ 1 [MOD p^2]`. Until 2025, the only known such primes are 1093 and
3511.

-/

section forallB

-- MOVE
noncomputable def forallB (f : ℕ → Bool) (start len : ℕ) (step : ℕ := 1) : Bool :=
  (Nat.rec (motive := fun _ ↦ ℕ × Bool) (start, true)
    (fun _ ih ↦ ih.rec fun i b ↦ (i.add step, (f i).and' b)) len).2

theorem forallB_iff_range' (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n ∈ List.range' start len step, f n := by
  unfold forallB
  simp only [Bool.and'_eq_and]
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
/-! # Tools for automation of ∀ n, lo ≤ n → n < hi → P n -/

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

theorem forall_succ {P : ℕ → Prop} {lo hi : ℕ} (h : P lo) (spec : hi.ble lo.succ := by rfl) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ le_antisymm hn₁
    (Nat.le_of_lt_succ <| hn₂.trans_le <| Nat.le_of_ble_eq_true spec) ▸ h

theorem forall_last {P : ℕ → Prop} {hi : ℕ} :
    ∀ n, hi ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ (not_lt_of_ge hn₁ hn₂).elim

theorem forall_exceed {P : ℕ → Prop} {lo hi : ℕ} (h : hi.ble lo) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ (not_le_of_gt (hn₁.trans_lt hn₂) <| Nat.le_of_ble_eq_true h).elim

end forall_step

section forall_mod
/-! # Tools for automation of ∀ n, lo ≤ n → n < hi → n % b = r → P n -/

theorem forall_mod_start {P : ℕ → Prop} {hi b r : ℕ}
    (ih : ∀ n, r ≤ n → n < hi → n % b = r → P n) :
    ∀ n < hi, n % b = r → P n :=
  fun n h₂ h₃ ↦ ih n (h₃ ▸ Nat.mod_le n b) h₂ h₃

theorem forall_mod_step {P : ℕ → Prop} {lo hi b r : ℕ} (next : ℕ)
    (now : P lo) (ih : ∀ n, next ≤ n → n < hi → n % b = r → P n)
    (spec₁ : lo + b = next := by rfl) (spec₂ : lo % b = r := by rfl) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  fun n h₁ h₂ h₃ ↦ (eq_or_lt_of_le h₁).elim (· ▸ now) fun h₁ ↦ by
    suffices next ≤ n from ih n this h₂ h₃
    rw [← spec₁]
    rw [← Nat.div_add_mod' lo b, ← Nat.div_add_mod' n b, spec₂, h₃] at h₁ ⊢
    replace h₁ := Nat.succ_le_of_lt <| lt_of_mul_lt_mul_right' <| (add_lt_add_iff_right _).mp h₁
    grw [add_right_comm, ← Nat.succ_mul, h₁]

-- A useful closing tool.
theorem forall_mod_succ {P : ℕ → Prop} {lo hi b r : ℕ}
    (now : P lo) (spec₁ : lo % b = r := by rfl) (spec₂ : hi.ble (lo.add b) := by rfl) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  forall_mod_step (lo + b) now (forall_exceed spec₂) rfl spec₁

-- For convenience (so that `P` does not need to change).
theorem forall_mod_bisect {P : ℕ → Prop} {lo hi b r : ℕ} (mi : ℕ)
    (ih₁ : ∀ n, lo ≤ n → n < mi → n % b = r → P n)
    (ih₂ : ∀ n, mi ≤ n → n < hi → n % b = r → P n) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  forall_bisect mi ih₁ ih₂

-- For convenience (so that `P` does not need to change).
theorem forall_mod_exceed {P : ℕ → Prop} {lo hi b r : ℕ} (h : hi.ble lo) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  forall_exceed h

end forall_mod

section Meta

open Lean Meta

local notation:max "rnl%" n => mkRawNatLit n
local notation:max "reflNat%" n => mkApp2 (mkConst `Eq.refl [1]) (mkConst `Nat) n

/-- An expression to prove statement of the form `∀ n, lo ≤ n → n < hi → P n` -/
def makeForallBisectLoHi (P : Expr) (lo hi : ℕ) (pf : ℕ → Expr) : Expr :=
  if hi ≤ lo + 1 then
    mkApp5 (mkConst ``forall_succ) P (rnl% lo) (rnl% hi) (pf lo) reflBoolTrue
  else
    have mi := (lo + hi) / 2
    mkApp6 (mkConst ``forall_bisect) P (rnl% lo) (rnl% hi) (rnl% mi)
      (makeForallBisectLoHi P lo mi pf)
      (makeForallBisectLoHi P mi hi pf)

/-- An expression to prove statement of the form `∀ n < hi → P n` -/
def makeForallBisectHi (P : Expr) (hi : ℕ) (pf : ℕ → Expr) : Expr :=
  mkApp3 (mkConst ``forall_start) P (rnl% hi) <| makeForallBisectLoHi P 0 hi pf

/-- An expression to prove statement of the form `∀ n, lo ≤ n → n < hi → n % b = r → P n`.
This always assumes `lo % b = r`. -/
partial def makeForallModBisectLoHi
    (P : Expr) (lo hi b r : ℕ) (bE rE : Expr) (pf : ℕ → Expr) : Expr :=
  if hi ≤ lo + b then
    mkApp8 (mkConst ``forall_mod_succ)
      P (rnl% lo) (rnl% hi) bE rE (pf lo) (reflNat% rE) reflBoolTrue
  else
    have mi := (lo / b + (hi - r) / b + 1) / 2 * b + r
    mkApp8 (mkConst ``forall_mod_bisect) P (rnl% lo) (rnl% hi) bE rE (rnl% mi)
      (makeForallModBisectLoHi P lo mi b r bE rE pf)
      (makeForallModBisectLoHi P mi hi b r bE rE pf)

/-- An expression to prove statement of the form `∀ n < hi → n % b = r → P n`. -/
def makeForallModBisectHi
    (P : Expr) (hi b r : ℕ) (bE rE : Expr) (pf : ℕ → Expr) : Expr :=
  mkApp5 (mkConst ``forall_mod_start) P (rnl% hi) bE rE <|
    makeForallModBisectLoHi P r hi b r bE rE pf

elab "check_interval" : tactic => Elab.Tactic.liftMetaFinishingTactic fun mId ↦ do
  let goal ← inferType <| .mvar mId
  let .forallE _ _ P₀ _ := goal | throwError "goal is not ∀"
  let .forallE _ P₁ P₂ _ := P₀ | throwError "goal is not bounded (1)"
  let mut lo? : Option ℕ := none
  let mut hiPE : Expr := default
  let mut P : Expr := default
  match P₁.getAppFnArgs with
  | (``LE.le, #[_, _, loE, .bvar _]) =>
    lo? := loE.nat?
    unless lo?.isSome do throwError "goal is not bounded (2)"
    let .forallE _ P₃ P₄ _ := P₂ | throwError "goal is not bounded (3)"
    hiPE := P₃
    P := P₄
  | _ =>
    hiPE := P₁
    P := P₂
  let (``LT.lt, #[_, _, .bvar _, hiE]) := hiPE.getAppFnArgs | throwError "goal is not bounded (4)"
  let some hi := hiE.nat? | throwError "goal is not bounded (5)"
  have br? : Option (ℕ × ℕ × Expr) := do
    let .forallE _ P₅ P₆ _ := P | none
    let (``Eq, #[_, e, rE]) := P₅.getAppFnArgs | none
    let (``HMod.hMod, #[_, _, _, _, .bvar _, bE]) := e.getAppFnArgs | none
    return (← bE.nat?, ← rE.nat?, P₆)
  if let some (_, _, PE) := br? then P := PE
  P := P.lowerLooseBVars 1 1 |>.lowerLooseBVars 1 1 |>.lowerLooseBVars 1 1
  P := .lam `n (mkConst ``Nat) P .default
  match lo?, br? with
  | some lo, none =>
    mId.assign <| makeForallBisectLoHi P lo hi fun _ ↦ reflBoolTrue
  | none, none =>
    mId.assign <| makeForallBisectHi P hi fun _ ↦ reflBoolTrue
  | some lo, some (b, r, _) =>
    mId.assign <| makeForallModBisectLoHi P lo hi b r (rnl% b) (rnl% r) fun _ ↦ reflBoolTrue
  | none, some (b, r, _) =>
    mId.assign <| makeForallModBisectHi P hi b r (rnl% b) (rnl% r) fun _ ↦ reflBoolTrue

end Meta
-- END MOVE

def Wieferich (p : ℕ) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p^2]

def Mirimanoff (p : ℕ) : Prop :=
  3 ^ (p - 1) ≡ 1 [MOD p^2]

noncomputable def wieferichKR (p : ℕ) : Bool :=
  powModTR 2 p.pred (p.pow 2) |>.beq 1

noncomputable def mirimanoffKR (p : ℕ) : Bool :=
  powModTR 3 p.pred (p.pow 2) |>.beq 1

@[simp] theorem wieferichKR_eq_true_iff (p : ℕ) (hp : p ≠ 1) : wieferichKR p ↔ Wieferich p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Wieferich, wieferichKR, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModTR_eq, powMod, Nat.pow_eq, Nat.pred_eq_sub_one]

@[simp] theorem wieferichKR_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    wieferichKR p = false ↔ ¬Wieferich p := by
  rw [← Bool.not_eq_true, wieferichKR_eq_true_iff p hp]

@[simp] theorem mirimanoffKR_eq_true_iff (p : ℕ) (hp : p ≠ 1) : mirimanoffKR p ↔ Mirimanoff p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Mirimanoff, mirimanoffKR, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModTR_eq, powMod, Nat.pow_eq, Nat.pred_eq_sub_one]

@[simp] theorem mirimanoffKR_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    mirimanoffKR p = false ↔ ¬Mirimanoff p := by
  rw [← Bool.not_eq_true, mirimanoffKR_eq_true_iff p hp]

/-! # We check odd numbers up to 6000 in the classes 1%6 and 5%6 -/

-- set_option trace.profiler true
-- set_option trace.profiler.threshold 0

-- elab: 37 ms
-- kernel: 470 ms
-- 6n+1 to 6000
theorem wieferich_mirimanoff₁ : ∀ n < 6000, n % 6 = 1 →
    (wieferichKR n).not'.or' (mirimanoffKR n).not' := by
  check_interval

-- elab: 57 ms
-- kernel: 561 ms
-- 6n+5 to 6000
theorem wieferich₅ : ∀ n < 6000, n % 6 = 5 → !wieferichKR n := by
  check_interval

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

theorem wieferich_mirimanoff {p : ℕ} (hp : p.Prime) (p_bound : p < 6000) :
    ¬(2 ^ (p - 1) ≡ 1 [MOD p^2]) ∨ ¬(3 ^ (p - 1) ≡ 1 [MOD p^2]) := by
  obtain hp₄ | hp₄ := lt_or_ge p 4
  · clear p_bound
    revert hp
    decide +revert +kernel
  have hp₁ : p ≠ 1 := by grind
  obtain h₁ | h₅ := hp.mod_6 (by grind) (by grind)
  · simpa [hp₁] using wieferich_mirimanoff₁ p p_bound h₁
  · simpa [hp₁] using Or.inl <| wieferich₅ p p_bound h₅

theorem _root_.pow_eq_one_of_dvd {M : Type*} [Monoid M] {x : M} {m n : ℕ}
    (h₁ : x ^ m = 1) (h₂ : m ∣ n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h₂
  rw [pow_mul, h₁, one_pow]

theorem miller_rabin_squarefree {n : ℕ} (hn₀ : n ≠ 0) (hn : n < 36000000)
    (h₂ : 2 ^ (n - 1) ≡ 1 [MOD n]) (h₃ : 3 ^ (n - 1) ≡ 1 [MOD n])
    {p : ℕ} (hp : p.Prime) (hpn : p ^ 2 ∣ n) : False := by
  have hn₁ : n ≠ 1 := by
    rintro rfl
    rw [Nat.dvd_one, sq, mul_eq_one, and_self] at hpn
    subst hpn
    exact absurd hp (by decide)
  have h₁ : _ < 6000 ^ 2 := (Nat.le_of_dvd (pos_of_ne_zero hn₀) hpn).trans_lt hn
  rw [Nat.pow_lt_pow_iff_left (by decide)] at h₁
  have hn₁' : n - 1 ≠ 0 := by grind
  have hp₁ : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  have := NeZero.mk hp₁
  have h₅ : (n - 1).gcd p = 1 := by
    rw [Nat.gcd_sub_left_left_of_dvd _ (by grind only)
      (dvd_trans (dvd_pow_self _ (by grind only)) hpn), Nat.gcd_one_left]
  have h₄ (a) (ha : a ^ (n - 1) ≡ 1 [MOD n]) : a ^ (p - 1) ≡ 1 [MOD p^2] := by
    replace ha := ha.of_dvd hpn
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at ha ⊢
    let a' := Units.ofPowEqOne _ _ ha hn₁'
    have ha₁ : a' ^ (n - 1) = 1 := Units.pow_ofPowEqOne _ _
    have ha₂ := pow_card_eq_one (x := a')
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp, pow_one] at ha₂
    replace ha₂ := pow_gcd_eq_one _ ha₁ ha₂
    rw [Nat.gcd_mul_right_right_of_gcd_eq_one h₅] at ha₂
    replace ha₂ := pow_eq_one_of_dvd ha₂ (Nat.gcd_dvd_right _ _)
    convert congr(($ha₂ : ZMod (p ^ 2)))
  have := wieferich_mirimanoff hp h₁
  tauto
