/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import PrimeCert.Pocklington

/-! # An improved version of Pocklington's primality test -/

theorem Nat.prime_iff_not_exists_mul_eq' (p : ℕ) :
    Nat.Prime p ↔ 2 ≤ p ∧ ¬∃ m n, 2 ≤ m ∧ m < p ∧ 2 ≤ n ∧ n < p ∧ m * n = p := by
  rw [prime_iff_not_exists_mul_eq]
  refine and_congr_right fun hp ↦ not_congr <| exists_congr fun m ↦ exists_congr fun n ↦ ?_
  refine ⟨fun ⟨hmp, hnp, hmnp⟩ ↦ ⟨?_, hmp, ?_, hnp, hmnp⟩, by tauto⟩
  · by_contra hm; interval_cases m <;> grind
  · by_contra hn; interval_cases n <;> grind

theorem Nat.modEq_prod {ι : Type*} {s : Finset ι} {f g : ι → ℕ} {b : ℕ}
    (hb : ∀ i ∈ s, f i ≡ g i [MOD b]) : (∏ i ∈ s, f i) ≡ (∏ i ∈ s, g i) [MOD b] := by
  classical induction s using Finset.induction with
  | empty => simp; rfl
  | insert a s has ih => simp_rw [Finset.prod_insert has]; exact Nat.ModEq.mul (by grind) (by grind)

theorem Nat.modEq_one_of_dvd_of_prime (n b : ℕ) (prime : ∀ p, Nat.Prime p → p ∣ n → p ≡ 1 [MOD b])
    (d : ℕ) (hdn : d ∣ n) : d ≡ 1 [MOD b] := by
  by_cases hn : n = 0
  · have := prime 2 prime_two <| hn ▸ dvd_zero _
    rw [ModEq.comm, modEq_iff_dvd' (by grind), dvd_one] at this
    exact this ▸ modEq_one
  have hd : d ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hdn; grind
  rw [← factorization_prod_pow_eq_self hd, Finsupp.prod,
    ← Finset.prod_const_one (s := d.factorization.support)]
  refine modEq_prod fun p hp ↦ ?_
  rw [support_factorization, mem_primeFactors] at hp
  exact ((prime p hp.1 (hp.2.1.trans hdn)).pow _).trans <| by simp; rfl

theorem Nat.modEq_iff_exists_mul_add {p q b : ℕ} (hqb : q < b) :
    p ≡ q [MOD b] ↔ ∃ k, k * b + q = p := by
  rw [ModEq]
  constructor
  · intro h
    rw [mod_eq_of_lt hqb] at h
    exact ⟨p / b, by rw [← h, Nat.div_add_mod']⟩
  · rintro ⟨k, rfl⟩
    rw [mul_add_mod']

theorem Nat.modEq_iff_exists_mul_add' {p q b : ℕ} (hqp : q ≤ p) :
    p ≡ q [MOD b] ↔ ∃ k, k * b + q = p := by
  rw [ModEq.comm, modEq_iff_dvd' hqp]
  rw [le_iff_exists_add'] at hqp
  obtain ⟨c, rfl⟩ := hqp
  simp_rw [add_tsub_cancel_right, add_left_inj, dvd_iff_exists_eq_mul_left, eq_comm]

theorem Nat.add_sq_eq_dist_sq_add_four_mul (c d : ℕ) :
    (c + d) ^ 2 = (max c d - min c d) ^ 2 + 4 * (c * d) := by
  wlog h : c ≤ d
  · rw [add_comm, max_comm, min_comm, mul_comm]; grind
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp h
  rw [max_eq_right h, min_eq_left h, Nat.add_sub_cancel_left]
  ring

namespace PrimeCert

section

set_option hygiene false
local notation "r" => (N - 1) / F₁ % (2 * F₁)
local notation "s" => (N - 1) / F₁ / (2 * F₁)

theorem pocklington3_test (N F₁ m : ℕ) (h2n : 2 ≤ N) (hn : Odd N) (hf₁ : F₁ ∣ N - 1)
    (hr₁ : Odd ((N - 1) / F₁))
    (primitive : ∀ p ∈ F₁.primeFactors, ∃ a, a ^ (N - 1) ≡ 1 [MOD N] ∧
      (a ^ ((N - 1) / p) - 1).gcd N = 1)
    (divisors : ∀ l, 1 ≤ l → l < m → ¬ l * F₁ + 1 ∣ N)
    (bound : N + (m * F₁ + 1) * (m * F₁) < (m * F₁ + 1) * (2 * F₁ ^ 2 + r * F₁ + 1))
    (cert : (N - 1) / F₁ < 2 * F₁ ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s) :
    Nat.Prime N := by
  set r' := r with hr
  set s' := s with hs
  simp_rw [Nat.prime_iff_not_exists_mul_eq', not_exists, not_and]
  refine ⟨by grind, fun p q h2p hpn h2q hqn hpq ↦ ?_⟩
  have := pocklington_test N F₁ (by grind) hf₁ primitive
  replace this := Nat.modEq_one_of_dvd_of_prime _ _ this
  have hp := this p (hpq ▸ dvd_mul_right _ _)
  have hq := this q (hpq ▸ dvd_mul_left _ _)
  rw [Nat.modEq_iff_exists_mul_add' (by grind)] at hp hq
  obtain ⟨c, rfl⟩ := hp
  obtain ⟨d, rfl⟩ := hq
  have hmc : m ≤ c := le_of_not_gt fun hcm ↦ by
    obtain hc | hc := le_or_gt 1 c
    · exact divisors c hc hcm (hpq ▸ dvd_mul_right _ _)
    · interval_cases c; rw [zero_mul] at h2p; grind
  have hmd : m ≤ d := le_of_not_gt fun hdm ↦ by
    obtain hd | hd := le_or_gt 1 d
    · exact divisors d hd hdm (hpq ▸ dvd_mul_left _ _)
    · interval_cases d; rw [zero_mul] at h2q; grind
  obtain ⟨R₁, hR⟩ := hf₁
  have hR₁ := (Nat.sub_eq_iff_eq_add <| by grind).mp hR
  have hf₀ : F₁ ≠ 0 := by rintro rfl; rw [zero_mul] at hR₁; grind
  rw [hR, Nat.mul_div_cancel_left _ (by grind)] at hr hs hr₁ cert
  have hR₂ := Nat.div_add_mod R₁ (2 * F₁)
  rw [← hr, ← hs] at hR₂
  rw [hR₁,
    show (c * F₁ + 1) * (d * F₁ + 1) = F₁ * ((c * d) * F₁ + (c + d)) + 1 by ring,
    add_left_inj, Nat.mul_right_inj hf₀] at hpq
  have even_f₁ : Even F₁ := by
    rw [hR₁, Nat.odd_add_one, Nat.not_odd_iff_even, Nat.even_mul,
      ← Nat.not_odd_iff_even (n := R₁)] at hn; tauto
  have odd_cd : Odd (c + d) := by
    rw [← hpq] at hr₁
    refine (Nat.odd_add'.mp hr₁).mpr <| Even.mul_left even_f₁ _
  have even_cd : Even (c * d) := by
    rw [Nat.odd_add, ← Nat.not_even_iff_odd] at odd_cd
    rw [Nat.even_mul]; tauto
  have hcdr : (c + d) % (2 * F₁) = r' := by
    obtain ⟨q, hq⟩ := even_iff_exists_two_mul.mp even_cd
    replace hpq := congr($hpq % (2 * F₁))
    rwa [hq, mul_right_comm, Nat.mul_add_mod, ← hr] at hpq
  have hcdm : (c + d) * m ≤ c * d + m ^ 2 := by
    rw [add_mul]
    obtain ⟨c, hc⟩ := le_iff_exists_add.mp hmc
    obtain ⟨d, hd⟩ := le_iff_exists_add.mp hmd
    rw [hc, hd]
    grind
  have hcdr₁ : c + d < 2 * F₁ + r' := by
    rw [hR₁, ← hpq] at bound
    conv_lhs at bound => exact
      show _ = (c * d + m ^ 2) * F₁ ^ 2 + (c + d) * F₁ + (m * F₁ + 1) by ring
    grw [← hcdm] at bound
    conv_lhs at bound => exact show _ = (m * F₁ + 1) * ((c + d) * F₁ + 1) by ring
    rw [mul_lt_mul_iff_right₀ (by grind), add_lt_add_iff_right] at bound
    conv_rhs at bound => exact show _ = (2 * F₁ + r') * F₁ by ring
    rwa [mul_lt_mul_iff_left₀ (by grind)] at bound
  have hcdr₂ := Nat.div_add_mod (c + d) (2 * F₁)
  rw [hcdr] at hcdr₂
  rw [← hcdr₂, add_lt_add_iff_right, mul_lt_iff_lt_one_right (by grind), Nat.lt_one_iff] at hcdr₁
  rw [hcdr₁, mul_zero, zero_add] at hcdr₂
  have hscd := hR₂.trans hpq.symm
  rw [← hcdr₂, add_left_inj, mul_right_comm, mul_left_inj' (by grind)] at hscd
  obtain cert | cert := cert
  · -- first case: s = 0
    rw [← Nat.div_eq_zero_iff_lt (by grind), ← hs] at cert
    rw [cert, mul_zero, eq_comm, mul_eq_zero] at hscd
    grind
  · -- second case: r^2-8s is not square
    have square : r' ^ 2 = 8 * s' + (max c d - min c d) ^ 2 := by
      rw [hcdr₂, show 8 = 4 * 2 by rfl, mul_assoc, hscd, Nat.add_sq_eq_dist_sq_add_four_mul,
        add_comm]
    rw [square, Nat.add_sub_cancel_left] at cert
    obtain cert | cert := cert
    · exact cert ⟨_, sq _⟩
    · grind

end

-- MOVE
def forallB (f : ℕ → Bool) (start len : ℕ) (step : ℕ := 1) : Bool :=
  (Nat.rec (motive := fun _ ↦ ℕ × Bool) (start, true)
    (fun _ ih ↦ ih.rec fun i b ↦ (eagerReduce (i.add step), f i && b)) len).2

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
    | succ len ih => simp only; rw [ih, eagerReduce, Nat.add_eq]; ring

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

def Pocklington3Cert (r s : ℕ) : Prop :=
  s = 0 ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s

/--
Inputs:
* `N`: the number to be certified as prime
* `F`: an even divisor of `N-1`, fully factored, to be given as a literal
* `F'`: the odd part of `F`, given in factorised form
* `e`: the exponent of `2` in `F`, so that `F = 2^e * F'`
* `R`: the quotient `(N-1)/F`, odd, given as a literal.
* `root`: a pseudo-primitive root (for `F`)
* `m`: an arbitrary number (`> 0`), which should be small for better performance.
* `s, r := divmod(R, 2*F)`, given as literals
-/
theorem pocklington3_certKR (N F F' e R root m r s : ℕ)
    (pred : PocklingtonPred N root (F'.mul <| Nat.pow 2 e))
    (cert : Pocklington3Cert r s)
    (hn : Nat.ble 2 N) (he : Nat.blt 0 e)
    (psp : (powModTR root N.pred N).beq 1)
    (e_def : F.beq <| F'.mul <| Nat.pow 2 e) (hfr : N.beq <| (F.mul R).succ)
    (odd_r : (R.mod 2).beq 1)
    (divisors : forallB (fun l ↦ Nat.blt 0 (N.mod l)) F.succ m.pred F)
    (r_def : r.beq <| R.mod <| F.mul 2) (s_def : s.beq <| R.div <| F.mul 2)
    (bound : N.add (m.mul F |>.succ |>.mul (m.mul F)) |>.blt
      (m.mul F |>.succ |>.mul (F.pow 2 |>.mul 2 |>.add (r.mul F |>.succ)))) :
    Nat.Prime N := by
  simp only [Nat.ble_eq] at hn
  simp only [Nat.blt_eq] at he
  simp only [Nat.pred_eq_sub_one, Nat.beq_eq, powModTR_eq, powMod] at psp
  simp only [Nat.pow_eq, Nat.mul_eq] at pred
  simp only [Nat.pow_eq, Nat.mul_eq, Nat.beq_eq] at e_def
  simp only [Nat.mul_eq, Nat.succ_eq_add_one, Nat.beq_eq] at hfr
  simp only [Nat.mod_eq_mod, Nat.beq_eq, ← Nat.odd_iff] at odd_r
  simp only [Nat.mul_eq, Nat.mod_eq_mod, Nat.beq_eq, mul_comm F] at r_def
  simp only [Nat.mul_eq, Nat.div_eq_div, Nat.beq_eq, mul_comm F] at s_def
  simp only [Nat.mul_eq, Nat.succ_eq_add_one, Nat.add_eq, Nat.pow_eq, Nat.blt_eq] at bound
  simp only [Pocklington3Cert] at cert
  have hf₀ : F ≠ 0 := by rintro rfl; rw [zero_mul] at hfr; grind
  have R_def : R = (N - 1) / F := by
    rw [hfr, Nat.succ_sub_one, Nat.mul_div_cancel_left _ (by grind)]
  refine pocklington3_test N F m (by simpa using hn) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hfr, Nat.odd_add_one, Nat.not_odd_iff_even, e_def, mul_right_comm]
    exact (Nat.even_pow.mpr ⟨even_two, by simpa [Nat.pos_iff_ne_zero] using he⟩).mul_left _
  · rw [hfr, Nat.succ_sub_one]; tauto
  · rwa [← R_def]
  · rw [← e_def, PocklingtonPred] at pred
    exact fun p hp ↦ ⟨root, by rwa [Nat.ModEq, Nat.one_mod_eq_one.mpr (by grind)], by tauto⟩
  · rw [show F.succ = 1 * F + 1 by simp, forallB_iff'] at divisors
    simp only [Nat.pred_eq_sub_one, Nat.mod_eq_mod, Nat.blt_eq, Nat.pos_iff_ne_zero, ne_eq,
      ← Nat.dvd_iff_mod_eq_zero] at divisors
    exact fun l hl₁ hl₂ ↦ divisors l hl₁ (by grind)
  · rwa [← R_def, ← r_def, mul_comm 2]
  · rwa [← R_def, ← r_def, ← s_def, ← Nat.div_eq_zero_iff_lt (by grind), ← s_def]

theorem Pocklington3Cert.of_zero (r s : Nat) (h : s.beq 0) : Pocklington3Cert r s := by
  unfold Pocklington3Cert; rw [Nat.beq_eq] at h; tauto

theorem Pocklington3Cert.of_prime (r s p : Nat) (hp : Nat.Prime p) (h2p : Nat.blt 2 p)
    (cond : powModTR (r.pow 2 |>.sub (s.mul 8)) (p.div 2) p |>.beq p.pred) :
    Pocklington3Cert r s := by
  refine .inr <| .inl fun h ↦ ?_
  simp only [Nat.pow_eq, Nat.mul_eq, Nat.sub_eq, Nat.div_eq_div, Nat.pred_eq_sub_one,
    Nat.beq_eq, powModTR_eq, mul_comm s] at cond
  rw [Nat.blt_eq] at h2p
  have p_odd : p % 2 = 1 := by rw [← Nat.not_even_iff, Nat.Prime.even_iff hp]; grind
  obtain ⟨a, ha⟩ := h
  rw [ha, powMod, ← sq, ← pow_mul, Nat.two_mul_odd_div_two p_odd] at cond
  replace cond := congr(($cond : ZMod p))
  have := Fact.mk hp
  rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_sub hp.one_le, ZMod.natCast_self, zero_sub,
    Nat.cast_one] at cond
  have ha : (a : ZMod p) ≠ 0 := by
    rintro ha; rw [ha, zero_pow (by grind), eq_comm, neg_eq_zero] at cond; grind
  rw [ZMod.pow_card_sub_one_eq_one ha, eq_neg_iff_add_eq_zero, one_add_one_eq_two, ← Nat.cast_two,
    ZMod.natCast_eq_zero_iff] at cond
  exact not_lt_of_ge (Nat.le_of_dvd (by grind) cond) h2p

theorem Pocklington3Cert.of_lt (r s : Nat) (h : r.pow 2 |>.blt (s.mul 8)) : Pocklington3Cert r s :=
  .inr <| .inr <| by simpa [mul_comm s] using h

namespace Meta

open Lean Meta Qq

syntax pock3_mode := num <|> "<"

inductive Pock3Mode
  | zero | prime (p : ℕ) | lt

def parsePock3Mode (stx : TSyntax ``pock3_mode) : Pock3Mode := match stx with
  | `(pock3_mode| $n:num) => have n := n.getNat; if n = 0 then .zero else .prime n
  | `(pock3_mode| <) => .lt
  | _ => .zero

def Pock3Mode.mkCert (mode : Pock3Mode) (r s : ℕ) (rE sE : Q(ℕ)) (dict : PrimeDict) :
    MetaM Q(Pocklington3Cert $r $s) := match mode with
  | .zero => return mkAppN (mkConst ``Pocklington3Cert.of_zero) #[rE, sE, eagerReflBoolTrue]
  | .prime p => do
    have pE : Q(ℕ) := mkNatLit p
    return mkAppN (mkConst ``Pocklington3Cert.of_prime)
      #[rE, sE, pE, (← dict.getM p).pf, eagerReflBoolTrue, eagerReflBoolTrue]
  | .lt => return mkAppN (mkConst ``Pocklington3Cert.of_lt) #[rE, sE, eagerReflBoolTrue]

/-- `(N, root, m, mode, F₁)` where `mode` is:
* `0` for `s = 0`;
* `p` for a small prime witnessing `r^2-8s` is not square;
* `<` for `r^2 < 8s`.
-/
syntax pock3_spec := "(" num "," num "," num "," pock3_mode "," prime_pow "*" factored")"

def PrimePow.base : PrimePow → ℕ
| .prime p => p
| .pow p _ => p

-- TODO: special case for `F = 2 ^ e`

def parsePock3Spec : PrimeCertMethod ``pock3_spec := fun stx dict ↦ match stx with
  | `(pock3_spec| ($N:num, $root:num, $m:num, $mode:pock3_mode,
      $head:prime_pow * $F:factored)) => do
    have (headE, headF) := parsePrimePow head
    unless headF.base == 2 do throwError "the first prime in the factorization must be 2"
    have (F'E, factors) := parseFactored F
    have N := N.getNat
    have NE : Q(ℕ) := mkNatLit N
    let .some F ← evalNat q($headE * $F'E) | throwError "failed to evaluate F"
    have FE : Q(ℕ) := mkNatLit F
    have e := match headF with | .prime _ => 1 | .pow _ e => e
    have eE : Q(ℕ) := mkNatLit e
    let .some R ← evalNat q($NE / $FE) | throwError "failed to evaluate R"
    have RE : Q(ℕ) := mkNatLit R
    have root := root.getNat
    have rootE : Q(ℕ) := mkNatLit root
    have m := m.getNat
    have mE : Q(ℕ) := mkNatLit m
    let .some s ← evalNat q($RE / ($FE * 2)) | throwError "failed to evaluate s"
    have sE : Q(ℕ) := mkNatLit s
    let .some r ← evalNat q($RE % ($FE * 2)) | throwError "failed to evaluate r"
    have rE : Q(ℕ) := mkNatLit r
    let pred ← mkPockPred NE rootE q(($F'E).mul (Nat.pow 2 $eE)) (factors.push <| .pow 2 e) dict
    have mode := parsePock3Mode mode
    let cert ← mode.mkCert r s rE sE dict
    have pf : Q(Nat.Prime $NE) := mkAppN (mkConst ``pocklington3_certKR)
      #[NE, FE, F'E, eE, RE, rootE, mE, rE, sE, pred, cert,
      eagerReflBoolTrue, eagerReflBoolTrue, eagerReflBoolTrue, eagerReflBoolTrue,
      eagerReflBoolTrue, eagerReflBoolTrue, eagerReflBoolTrue, eagerReflBoolTrue,
      eagerReflBoolTrue, eagerReflBoolTrue]
    return ⟨N, NE, pf⟩
  | _ => Elab.throwUnsupportedSyntax

@[prime_cert pock3] def pock3 : PrimeCertExt where
  syntaxName := ``pock3_spec
  methodName := ``parsePock3Spec

end PrimeCert.Meta
