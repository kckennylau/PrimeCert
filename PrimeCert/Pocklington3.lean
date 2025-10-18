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

def Pocklington3Cert (r s : ℕ) : Prop :=
  s = 0 ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s

theorem pocklington3_test (N F R m r s : ℕ)
    (R_def : F * R + 1 = N) (r_def : R % (2 * F) = r) (s_def : R / (2 * F) = s)
    (h2n : 2 ≤ N) (odd_n : Odd N) (odd_R : Odd R)
    (primitive : ∀ p ∈ F.primeFactors, ∃ a, a ^ (N - 1) ≡ 1 [MOD N] ∧
      (a ^ ((N - 1) / p) - 1).gcd N = 1)
    (divisors : ∀ l, 1 ≤ l → l < m → ¬ l * F + 1 ∣ N)
    (bound : N + (m * F + 1) * (m * F) < (m * F + 1) * (2 * F ^ 2 + r * F + 1))
    (cert : s = 0 ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s) :
    Nat.Prime N := by
  simp_rw [Nat.prime_iff_not_exists_mul_eq', not_exists, not_and]
  refine ⟨by grind, fun p q h2p hpn h2q hqn hpq ↦ ?_⟩
  have := pocklington_test N F (by grind)
    (by rw [← R_def, Nat.add_sub_cancel_right]; exact dvd_mul_right _ _) primitive
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
  have hf₀ : F ≠ 0 := by rintro rfl; rw [zero_mul] at R_def; grind
  have hR₂ := Nat.div_add_mod R (2 * F)
  rw [r_def, s_def] at hR₂
  rw [show (c * F + 1) * (d * F + 1) = F * ((c * d) * F + (c + d)) + 1 by ring,
    ← R_def, add_left_inj, Nat.mul_right_inj hf₀] at hpq
  have even_F : Even F := by
    rw [← R_def, Nat.odd_add_one, Nat.not_odd_iff_even, Nat.even_mul,
      ← Nat.not_odd_iff_even (n := R)] at odd_n; tauto
  have odd_cd : Odd (c + d) := by
    rw [← hpq] at odd_R
    refine (Nat.odd_add'.mp odd_R).mpr <| Even.mul_left even_F _
  have even_cd : Even (c * d) := by
    rw [Nat.odd_add, ← Nat.not_even_iff_odd] at odd_cd
    rw [Nat.even_mul]; tauto
  have hcdr : (c + d) % (2 * F) = r := by
    obtain ⟨q, hq⟩ := even_iff_exists_two_mul.mp even_cd
    replace hpq := congr($hpq % (2 * F))
    rwa [hq, mul_right_comm, Nat.mul_add_mod, r_def] at hpq
  have hcdm : (c + d) * m ≤ c * d + m ^ 2 := by
    rw [add_mul]
    obtain ⟨c, hc⟩ := le_iff_exists_add.mp hmc
    obtain ⟨d, hd⟩ := le_iff_exists_add.mp hmd
    rw [hc, hd]
    grind
  have hcdr₁ : c + d < 2 * F + r := by
    rw [← R_def, ← hpq] at bound
    conv_lhs at bound => exact
      show _ = (c * d + m ^ 2) * F ^ 2 + (c + d) * F + (m * F + 1) by ring
    grw [← hcdm] at bound
    conv_lhs at bound => exact show _ = (m * F + 1) * ((c + d) * F + 1) by ring
    rw [mul_lt_mul_iff_right₀ (by grind), add_lt_add_iff_right] at bound
    conv_rhs at bound => exact show _ = (2 * F + r) * F by ring
    rwa [mul_lt_mul_iff_left₀ (by grind)] at bound
  have hcdr₂ := Nat.div_add_mod (c + d) (2 * F)
  rw [hcdr] at hcdr₂
  rw [← hcdr₂, add_lt_add_iff_right, mul_lt_iff_lt_one_right (by grind), Nat.lt_one_iff] at hcdr₁
  rw [hcdr₁, mul_zero, zero_add] at hcdr₂
  have hscd := hR₂.trans hpq.symm
  rw [← hcdr₂, add_left_inj, mul_right_comm, mul_left_inj' (by grind)] at hscd
  obtain cert | cert := cert
  · -- first case: s = 0
    rw [cert, mul_zero, eq_comm, mul_eq_zero] at hscd
    grind
  · -- second case: r^2-8s is not square
    have square : r ^ 2 = 8 * s + (max c d - min c d) ^ 2 := by
      rw [hcdr₂, show 8 = 4 * 2 by rfl, mul_assoc, hscd, Nat.add_sq_eq_dist_sq_add_four_mul,
        add_comm]
    rw [square, Nat.add_sub_cancel_left] at cert
    obtain cert | cert := cert
    · exact cert ⟨_, sq _⟩
    · grind

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
-- END MOVE

theorem Pocklington3Cert.of_prime (r s p : Nat) (hp : Nat.Prime p) (h2p : 2 < p)
    (cond : powMod (r ^ 2 - 8 * s) (p / 2) p = p - 1) :
    Pocklington3Cert r s := by
  refine .inr <| .inl fun h ↦ ?_
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

inductive Pocklington3CertMode : Type
  | zero | prime (p : ℕ) (hp : Nat.Prime p) | lt

noncomputable def Pocklington3CertMode.calculate (m : Pocklington3CertMode) (r s : ℕ) : Bool :=
  m.rec (s.beq 0) (fun p _ ↦ (2).blt p && (powModTR (r.pow 2 |>.sub <| s.mul 8) (p.div 2) p).beq
    p.pred) (r.pow 2 |>.blt <| s.mul 8)

theorem Pocklington3CertMode.to_cert (m : Pocklington3CertMode) (r s : ℕ) (h : m.calculate r s) :
    Pocklington3Cert r s := by
  cases m with
  | zero => exact .inl <| Nat.beq_eq.to_iff.mp h
  | prime p hp =>
    simp only [calculate, Nat.pow_eq, Nat.mul_eq, Nat.sub_eq, Nat.div_eq_div, Nat.pred_eq_sub_one,
      Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, mul_comm s, powModTR_eq] at h
    exact .of_prime _ _ p hp h.1 h.2
  | lt => exact .inr <| .inr <| Nat.blt_eq.to_iff.mp <| mul_comm 8 s ▸ h

structure PrimePow : Type where
  (prime : ℕ) (pow : ℕ) (pf : prime.Prime) (pow_ne_zero : (0).blt pow)

noncomputable def PrimePow.toNat (pp : PrimePow) : ℕ :=
  pp.rec fun p v _ _ ↦ p.pow v

@[simp] theorem PrimePow.toNat_def (pp : PrimePow) : pp.toNat = pp.prime ^ pp.pow := rfl

theorem PrimePow.prime_dvd_toNat (pp : PrimePow) : pp.prime ∣ pp.toNat :=
  dvd_pow_self _ <| ne_of_gt <| Nat.blt_eq.to_iff.mp pp.pow_ne_zero

noncomputable def pocklington3_calculate (N e root m : ℕ) (F' : List PrimePow)
    (mode : Pocklington3CertMode) : Bool :=
  let F := Nat.mul (F'.rec 1 fun pp _ ih ↦ pp.rec fun p vp _ _ ↦ ih.mul <| p.pow vp) <| (2).pow e
  let two_F := F.mul 2
  let R := N.div F
  let r := R.mod two_F
  let s := R.div two_F
  F'.rec (powModTR root (N.div 2) N |>.pred.gcd N |>.beq 1)
    (fun pp _ ih ↦ pp.rec fun p _ _ _ ↦ powModTR root (N.div p) N |>.pred.gcd N |>.beq 1 && ih) &&
  (0).blt e &&
  (mode.calculate r s) &&
  (N.mod F |>.beq 1) &&
  (R.mod 2 |>.beq 1) &&
  (powModTR root N.pred N |>.beq 1) &&
  (forallB (fun l ↦ Nat.blt 0 (N.mod l)) F.succ m.pred F) &&
  (s.mul 2 |>.add (m.pow 2) |>.blt (two_F.add r |>.mul m |>.add 2))

-- MOVE
theorem _root_.List.rec_and {α : Type*} (f : α → Bool) (b : Bool) (l : List α) :
    (List.rec b (fun hd _ ih ↦ f hd && ih) l : Bool) = true ↔
    b = true ∧ ∀ x ∈ l, f x := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp only [Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]; tauto

theorem mem_primeFactors_prod_toNat (L : List PrimePow) (p : ℕ) :
    p ∈ (L.map PrimePow.toNat |>.prod |>.primeFactors) → ∃ pp ∈ L, pp.prime = p := by
  induction L with
  | nil => simp
  | cons pp _ ih =>
    rw [List.map_cons, List.prod_cons, Nat.primeFactors_mul, List.exists_mem_cons_iff,
      Finset.mem_union, pp.toNat_def]
    · refine Or.imp ?_ ih
      · by_cases h0 : pp.pow = 0
        · rw [h0, pow_zero, Nat.primeFactors_one]; grind
        · rw [Nat.primeFactors_prime_pow h0 pp.pf]; grind
    · exact pow_ne_zero _ pp.pf.ne_zero
    · refine List.prod_ne_zero ?_
      rw [List.mem_map, not_exists]
      exact fun pp h ↦ absurd h.2 <| pow_ne_zero _ pp.pf.ne_zero

theorem of_gcd_pred_mod_eq_one (a b : ℕ) (h : (a % b - 1).gcd b = 1)
    (hb : 2 ≤ b) : (a - 1).gcd b = 1 := by
  rwa [Nat.gcd_comm, Nat.gcd_def, if_neg (by grind), ← Nat.mod_sub_of_le]
  · by_cases h₀ : a % b = 0
    · rw [h₀, Nat.zero_sub, Nat.gcd_zero_left] at h; grind
    · grind

/--
Inputs (not all needed):
* `N`: the number to be certified as prime
* `F`: an even divisor of `N-1`, fully factored, to be given as a literal
* `F'`: the odd part of `F`, given in factorised form
* `e`: the exponent of `2` in `F`, so that `F = 2^e * F'`
* `R`: the quotient `(N-1)/F`, odd, given as a literal.
* `root`: a pseudo-primitive root (for `F`)
* `m`: an arbitrary number (`> 0`), which should be small for better performance.
* `s, r := divmod(R, 2*F)`, given as literals
-/
theorem pocklington3_certKR (N root m e : ℕ) (F' : List PrimePow) (mode : Pocklington3CertMode)
    (cert : pocklington3_calculate N e root m F' mode) :
    Nat.Prime N := by
  unfold pocklington3_calculate at cert
  extract_lets F two_F R r s at cert
  simp only [Nat.div_eq_div, powModTR_eq, Nat.pred_eq_sub_one, Nat.mod_eq_mod, Nat.succ_eq_add_one,
    Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at cert
  obtain ⟨⟨⟨⟨⟨⟨⟨primitive, e_pos⟩, cert⟩, hnf⟩, odd_R⟩, psp⟩, divisors⟩, bound⟩ := cert
  have R_def : F * R + 1 = N := by
    rw [← Nat.div_add_mod N F, hnf]; rfl
  have even_F : Even F :=
    (Nat.even_pow.mpr ⟨even_two, e_pos.ne'⟩).mul_left _
  have odd_N : Odd N := by
    rw [← R_def, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact even_F.mul_right _
  have F_def : F = (F'.map PrimePow.toNat).prod * 2 ^ e := by
    simp only [F, Nat.mul_eq, Nat.pow_eq]
    congr 1
    clear * - F'
    induction F' with
    | nil => rfl
    | cons h _ ih => simp only [ih, List.map_cons, List.prod_cons, mul_comm h.toNat]; rfl
  have hf₀ : F ≠ 0 := by
    rw [F_def]
    refine mul_ne_zero (List.prod_ne_zero ?_) (pow_ne_zero _ <| by decide)
    rw [List.mem_map, not_exists]
    exact fun pp h ↦ absurd (h.2) <| pow_ne_zero _ pp.pf.ne_zero
  have hf₂ : 2 ≤ F := by grind
  have hn₁ : N ≠ 1 := by
    rintro rfl
    rw [add_eq_right, mul_eq_zero] at R_def
    rw [R_def.resolve_left hf₀] at odd_R
    grind
  have hn₃ : 3 ≤ N := by grind
  have dvd_F_of_mem_F' (pp) (h : pp ∈ F') : pp.prime ∣ F := by
    rw [F_def]
    exact dvd_mul_of_dvd_left (dvd_trans pp.prime_dvd_toNat <| List.dvd_prod <|
      List.mem_map_of_mem h) _
  have h_two_F : two_F = 2 * F := mul_comm F 2
  have hrs : 2 * F * s + r = R := by
    rw [← Nat.div_add_mod R (2 * F), ← h_two_F]; rfl
  refine pocklington3_test N F R m r s R_def (mul_comm 2 F ▸ rfl) (mul_comm 2 F ▸ rfl)
    (by grind) odd_N (Nat.odd_iff.mpr odd_R) ?_ ?_ ?_ ?_
  · simp only [List.rec_and, Nat.beq_eq, powMod] at primitive
    rw [F_def, ← PrimePow.toNat_def ⟨2, e, Nat.prime_two, by simpa⟩, mul_comm, ← List.prod_cons,
      ← List.map_cons]
    refine fun p hp ↦ ⟨root, ?_, ?_⟩
    · rw [Nat.ModEq, Nat.one_mod_eq_one.mpr hn₁, ← powMod, psp]
    · obtain ⟨pp, hpp, rfl⟩ := mem_primeFactors_prod_toNat _ _ hp
      rw [List.mem_cons] at hpp
      refine of_gcd_pred_mod_eq_one _ _ ?_ (by grind)
      obtain rfl | hpp := hpp
      · convert primitive.1 using 5
        convert Nat.div_eq_sub_mod_div.symm
        exact (Nat.odd_iff.mp odd_N).symm
      · convert primitive.2 pp hpp using 5
        convert Nat.div_eq_sub_mod_div.symm
        rw [eq_comm, ← Nat.one_mod_eq_one.mpr pp.pf.ne_one, ← Nat.ModEq]
        refine Nat.ModEq.of_dvd (dvd_F_of_mem_F' _ hpp) ?_
        rw [Nat.ModEq, Nat.one_mod_eq_one.mpr (by grind), hnf]
  · rw [show F + 1 = 1 * F + 1 by simp, forallB_iff'] at divisors
    simp only [Nat.blt_eq, Nat.pos_iff_ne_zero, ne_eq, ← Nat.dvd_iff_mod_eq_zero] at divisors
    exact fun l hl₁ hl₂ ↦ divisors l hl₁ (by grind)
  · rw [← R_def, ← hrs]
    conv_lhs => exact show _ = ((s * 2 + m ^ 2) * F + r + m) * F + 1 by ring
    conv_rhs => exact show _ = (((F * 2 + r) * m + 2) * F + r + m) * F + 1 by ring
    gcongr 5
    exact bound
  · exact mode.to_cert _ _ cert

namespace Meta

open Lean Meta Qq

syntax pock3_mode := num <|> "<"

def parsePock3Mode (stx : TSyntax ``pock3_mode) (dict : PrimeDict) :
    MetaM Q(Pocklington3CertMode) := match stx with
  | `(pock3_mode| $n:num) =>
    have n := n.getNat
    if n = 0 then return q(.zero) else do
      have nE : Q(ℕ) := mkNatLit n
      let pf : Q(($nE).Prime) ← dict.getM n
      return q(.prime $nE $pf)
  | `(pock3_mode| <) => return q(.lt)
  | _ => Elab.throwUnsupportedSyntax

/-- `(N, root, m, mode, F)` where `mode` is:
* `0` for `s = 0`;
* `p` for a small prime witnessing `r^2-8s` is not square;
* `<` for `r^2 < 8s`.
-/
syntax pock3_spec := "(" num "," num "," num "," pock3_mode "," prime_pow "*" factored")"

def PrimePow.base : PrimePow → ℕ
| .prime p => p
| .pow p _ => p

def parsePrimePow' (stx : TSyntax ``prime_pow) (dict : PrimeDict) :
    MetaM Q(PrimeCert.PrimePow) := match stx with
  | `(prime_pow| $p ^ $e) => do
    have p := p.getNat; have pE := mkNatLit p
    have e := e.getNat; have eE := mkNatLit e
    let pf ← dict.getM p
    return mkApp4 (mkConst ``PrimeCert.PrimePow.mk) pE eE pf eagerReflBoolTrue
  | `(prime_pow| $p:num) => do
    have p := p.getNat; have pE := mkNatLit p
    let pf ← dict.getM p
    return mkApp4 (mkConst ``PrimeCert.PrimePow.mk) pE (mkNatLit 1) pf eagerReflBoolTrue
  | _ => Elab.throwUnsupportedSyntax

def parseFactored' (stx : TSyntax ``factored) (dict : PrimeDict) :
    MetaM Q(List PrimeCert.PrimePow) := do
  match stx with
  | `(factored| $pps:prime_pow**) =>
    pps.getElems.foldlM (fun ih pp ↦ return q($(← parsePrimePow' pp dict) :: $ih)) q([])
  | _ => Elab.throwUnsupportedSyntax

-- TODO: special case for `F = 2 ^ e`

def parsePock3Spec : PrimeCertMethod ``pock3_spec := fun stx dict ↦ match stx with
  | `(pock3_spec| ($N:num, $root:num, $m:num, $mode:pock3_mode,
      $head:prime_pow * $F:factored)) => do
    have (_, headF) := parsePrimePow head
    unless headF.base == 2 do throwError "the first prime in the factorization must be 2"
    let F'E ← parseFactored' F dict
    have N := N.getNat
    have NE : Q(ℕ) := mkNatLit N
    have e := match headF with | .prime _ => 1 | .pow _ e => e
    have eE : Q(ℕ) := mkNatLit e
    have root := root.getNat
    have rootE : Q(ℕ) := mkNatLit root
    have m := m.getNat
    have mE : Q(ℕ) := mkNatLit m
    let mode ← parsePock3Mode mode dict
    have pf : Q(Nat.Prime $NE) := mkAppN (mkConst ``pocklington3_certKR)
      #[NE, rootE, mE, eE, F'E, mode, eagerReflBoolTrue]
    return ⟨N, NE, pf⟩
  | _ => Elab.throwUnsupportedSyntax

@[prime_cert pock3] def pock3 : PrimeCertExt where
  syntaxName := ``pock3_spec
  methodName := ``parsePock3Spec

end PrimeCert.Meta
