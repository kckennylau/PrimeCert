/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.PredMod
import PrimeCert.PowMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime

/-! # Pocklington's primality certificate

To use this certificate for primality of `N`, factorise `N - 1` completely.
1. If the largest factor `p` is `> √N`, then set `F₁ = p`.
2. Otherwise, set `F₁` to be the product of enough prime factors to be `> √N`.
3. Then, find a primitive root `a` of `N`.
4. Then `a` will satisfy the conditions required, which are:
  - `a ^ (N - 1) ≡ 1 (mod N)`
  - For each prime factor `p` of `F₁`, `gcd(a ^ ((N - 1) / p) - 1, N) = 1`.
-/

theorem List.pairwise_iff_toFinset {α β : Type*} (l : List α) (hl : l.Nodup)
    (P : β → β → Prop) (hp : Symmetric P) (e : α → β) [DecidableEq α] :
    l.Pairwise (P.onFun e) ↔ _root_.Pairwise (P.onFun fun i : l.toFinset ↦ e i) := by
  rw [Finset.pairwise_subtype_iff_pairwise_finset',
    List.pairwise_iff_coe_toFinset_pairwise hl (hp.comap _)]

theorem Nat.modEq_finset_prod_iff {a b : ℕ} {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (co : Pairwise (Coprime.onFun fun i : s ↦ e i)) :
    a ≡ b [MOD s.prod e] ↔ ∀ i ∈ s, a ≡ b [MOD e i] := by
  classical
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  rw [List.prod_toFinset e hl, Nat.modEq_list_map_prod_iff]
  · simp_rw [List.mem_toFinset]
  · rwa [List.pairwise_iff_toFinset _ hl _ Coprime.symmetric]

theorem multiplicity_zero_right {α : Type*} [MonoidWithZero α] (x : α) : multiplicity x 0 = 1 :=
  multiplicity_eq_one_of_not_finiteMultiplicity fun h ↦ h.ne_zero rfl

theorem Nat.modEq_iff_forall_prime_dvd {a b n : ℕ} :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] := by
  by_cases hn₀ : n = 0
  · subst hn₀
    simp_rw [modEq_zero_iff, dvd_zero, true_imp_iff]
    constructor
    · rintro rfl; exact fun _ _ ↦ by rfl
    · intro h
      obtain ⟨p, hbp, hp⟩ := exists_infinite_primes (a + b + 1)
      specialize h p hp
      rw [multiplicity_zero_right, pow_one] at h
      exact h.eq_of_lt_of_lt (by linarith) (by linarith)
  · conv_lhs => rw [← factorization_prod_pow_eq_self hn₀]
    rw [Finsupp.prod, modEq_finset_prod_iff]
    · simp_rw [support_factorization, mem_primeFactors_of_ne_zero hn₀, and_comm, and_imp]
      refine forall_congr' fun p ↦ imp_congr_right fun hpn ↦ imp_congr_right fun hp ↦ ?_
      rw [multiplicity_eq_factorization hp hn₀]
    · refine fun p q hp ↦ coprime_pow_primes _ _ ?_ ?_ <| by grind
      · exact ((mem_primeFactors_of_ne_zero hn₀).mp p.2).1
      · exact ((mem_primeFactors_of_ne_zero hn₀).mp q.2).1

theorem Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div
    {q n x : ℕ} (hq : q.Prime) (hxn : x ∣ n) (hxnq : ¬ x ∣ n / q) :
    q ^ multiplicity q n ∣ x := by
  by_cases hqn : q ∣ n
  · obtain ⟨n, rfl⟩ := hqn
    rw [Nat.mul_div_cancel_left _ hq.pos] at hxnq
    by_cases hn₀ : n = 0
    · subst hn₀; exact (hxnq <| dvd_zero _).elim
    have hqn₀ : q * n ≠ 0 := mul_ne_zero hq.ne_zero hn₀
    have hx₀ : x ≠ 0 := by rintro rfl; exact hqn₀ <| zero_dvd_iff.mp hxn
    rw [← Nat.factorization_le_iff_dvd hx₀ hn₀] at hxnq
    rw [← Nat.factorization_le_iff_dvd hx₀ hqn₀] at hxn
    rw [Nat.factorization_mul hq.ne_zero hn₀, hq.factorization, add_comm] at hxn
    refine pow_dvd_of_le_multiplicity ?_
    rw [multiplicity_eq_factorization hq hqn₀, multiplicity_eq_factorization hq hx₀,
      Nat.factorization_mul hq.ne_zero hn₀, Finsupp.add_apply, hq.factorization,
      Finsupp.single_apply, if_pos rfl, add_comm]
    refine le_of_not_gt fun h ↦ hxnq fun p ↦ ?_
    by_cases hpq : p = q
    · subst hpq; exact lt_succ.mp h
    convert hxn p using 1
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hpq), add_zero]
  · rw [multiplicity_eq_zero.mpr hqn, pow_zero]
    exact one_dvd _

/-- Let `N` be a natural number whose primality we want to certify.
Assume we have a partial factorisation `N - 1 = F₁ * R₁`, where `F₁` is fully factorised with
prime factors `pᵢ`.
Now for each `pᵢ` find a pseudo-primitive root `aᵢ` such that `aᵢ ^ (N - 1) ≡ 1 (mod N)` and
`gcd(aᵢ ^ ((N - 1) / pᵢ) - 1, N) = 1`.
Then any prime factor `n` of `N` satisfies `n ≡ 1 (mod F₁)`. -/
theorem pocklington_test (N F₁ : ℕ) (hn₀ : 0 < N) (hf₁ : F₁ ∣ N - 1)
    (primitive : ∀ p ∈ F₁.primeFactors, ∃ a : ℕ, a ^ (N - 1) ≡ 1 [MOD N] ∧
      Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1)
    (p : ℕ) (hp : p.Prime) (hpn : p ∣ N) : p ≡ 1 [MOD F₁] := by
  by_cases hn₁ : N = 1
  · rw [hn₁, Nat.dvd_one] at hpn
    exact absurd (hpn ▸ hp) Nat.not_prime_one
  replace hn₁ : 1 < N := by grind
  have hf₀ : F₁ ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hf₁
    grind
  rw [Nat.modEq_iff_forall_prime_dvd]
  intro q hqf hq
  have := Fact.mk hp
  have := (Nat.prime_iff_card_units _).mp hp
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hp.one_le, ← this]
  obtain ⟨a, han, hanq⟩ := primitive q (Nat.mem_primeFactors.mpr ⟨hq, hqf, hf₀⟩)
  have hanp := han.of_dvd hpn
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at hanp
  let a' : (ZMod p)ˣ := Units.ofPowEqOne _ _ hanp (by grind)
  refine dvd_trans ?_ (orderOf_dvd_card (x := a'))
  have : multiplicity q F₁ ≤ multiplicity q (N - 1) := by
    rw [Nat.multiplicity_eq_factorization hq hf₀, Nat.multiplicity_eq_factorization hq (by grind)]
    exact (Nat.factorization_le_iff_dvd hf₀ (by grind)).mpr hf₁ _
  refine dvd_trans (pow_dvd_pow _ this) ?_
  refine Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div hq ?_ ?_
  · rwa [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val]
  · rw [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val]
    unfold a'
    have : 1 ≤ a ^ ((N - 1) / q) := Nat.one_le_pow _ _ <| pos_of_ne_zero fun ha₀ ↦ by
      subst ha₀; rw [Nat.cast_zero, zero_pow (by grind)] at hanp; simp at hanp
    rw [Units.val_ofPowEqOne, ← Nat.cast_pow, Units.val_one, ← Nat.cast_one (R := ZMod p),
      ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' this,
      ← hp.coprime_iff_not_dvd]
    rw [← Nat.coprime_iff_gcd_eq_one] at hanq
    exact hanq.symm.coprime_dvd_left hpn

def PocklingtonPred (N root F₁ : ℕ) : Prop :=
  ∀ p ∈ F₁.primeFactors, (root ^ ((N - 1) / p) - 1).gcd N = 1

theorem pocklington_certify (N F₁ : ℕ) (h2n : 2 ≤ N) (hf₁ : F₁ ∣ N - 1) (hf₁' : N.sqrt < F₁)
    (root : ℕ) (psp : root ^ (N - 1) ≡ 1 [MOD N])
    (primitive : PocklingtonPred N root F₁) :
    Nat.Prime N := by
  by_contra hn
  rw [Nat.sqrt_lt, ← sq] at hf₁'
  have := pocklington_test N F₁ (by grind) hf₁ (fun p hp ↦ ⟨root, psp, primitive p hp⟩)
    N.minFac (N.minFac_prime (by grind)) N.minFac_dvd
  have h1p : 2 ≤ N.minFac := (N.minFac_prime (by grind)).two_le
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by grind)] at this
  have := Nat.succ_le.mp <| (Nat.le_sub_iff_add_le (by grind)).mp <| Nat.le_of_dvd (by grind) this
  exact lt_asymm hf₁' <| ((Nat.pow_lt_pow_iff_left (by grind)).mpr this).trans_le <|
    Nat.minFac_sq_le_self (by grind) hn

theorem pocklington_certifyKR (N root F₁ : ℕ)
    (primitive : PocklingtonPred N root F₁)
    (psp : (powModTR root N.pred N).beq 1 := by exact eagerReduce (Eq.refl true))
    (h2n : Nat.ble 2 N := by exact eagerReduce (Eq.refl true))
    (hf₁ : (N.pred.mod F₁).beq 0 := by exact eagerReduce (Eq.refl true))
    (hf₁' : N.blt (F₁.mul F₁) := by exact eagerReduce (Eq.refl true)) : N.Prime := by
  simp_all only [powModTR_eq, Nat.beq_eq, Nat.ble_eq, Nat.mod_eq_mod,
    ← Nat.dvd_iff_mod_eq_zero, Nat.mul_eq, Nat.blt_eq, ← Nat.sqrt_lt]
  rw [← Nat.one_mod_eq_one.mpr (show N ≠ 1 by grind)] at psp
  exact pocklington_certify N F₁ h2n hf₁ hf₁' root psp primitive

@[simp] theorem PocklingtonPred.zero {N root : ℕ} :
    PocklingtonPred N root 0 := by
  simp [PocklingtonPred]

@[simp] theorem PocklingtonPred.one {N root : ℕ} :
    PocklingtonPred N root 1 := by
  simp [PocklingtonPred]

theorem PocklingtonPred.step_pow {N root F₂ p e : ℕ} (hp : p.Prime)
    (ih : PocklingtonPred N root F₂)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root (F₂ * p ^ e) := by
  by_cases hf₂ : F₂ = 0
  · simp [hf₂]
  by_cases he : e = 0
  · simpa [he]
  by_cases hn : N = 0
  · simp [hn, predModKR, powModTR_eq, powMod] at step
  rw [PocklingtonPred] at ih ⊢
  rw [Nat.primeFactors_mul hf₂ (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow he hp]
  simp_rw [Finset.union_singleton, Finset.forall_mem_insert]
  refine ⟨?_, ih⟩
  simp only [Nat.pred_eq_sub_one, Nat.div_eq_div, Nat.beq_eq] at step
  simp only [Nat.blt_eq] at hroot
  rw [predModKR_eq hn (by rw [powModTR_eq]; exact (Nat.mod_lt _ (by grind)).le),
    ← Nat.add_sub_assoc (by grind), powModTR_eq, powMod] at step
  by_cases hp : root ^ ((N - 1) / p) % N = 0
  · rw [← Nat.dvd_iff_mod_eq_zero] at hp
    obtain ⟨r, hr⟩ := hp
    have : r ≠ 0 := by rintro rfl; rw [mul_zero, pow_eq_zero_iff'] at hr; grind
    replace this := mul_ne_zero hn this
    rw [hr, Nat.gcd_mul_left_sub_left (by grind), Nat.gcd_one_left]
  rwa [add_comm, Nat.add_sub_assoc (by grind), Nat.add_mod_left, Nat.mod_sub_of_le (by grind),
    Nat.mod_mod, ← Nat.gcd_rec, Nat.gcd_comm] at step

theorem PocklingtonPred.step {N root F₂ p : ℕ} (hp : p.Prime)
    (ih : PocklingtonPred N root F₂)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root (F₂ * p) := by
  simpa using PocklingtonPred.step_pow (e := 1) hp ih step hroot

theorem PocklingtonPred.base_pow {N root p e : ℕ} (hp : p.Prime)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root (p ^ e) := by
  simpa using PocklingtonPred.step_pow hp .one step hroot

theorem PocklingtonPred.base {N root p : ℕ} (hp : p.Prime)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root p := by
  simpa using PocklingtonPred.base_pow (e := 1) hp step hroot

namespace PrimeCert

theorem prime_339392917 :
    Nat.Prime 339392917 :=
  pocklington_certifyKR _ 2 (3 ^ 4 * 29 * 41) <|
    .step (by norm_num) <| .step (by norm_num) <| .base_pow (by norm_num)

theorem prime_16290860017 : Nat.Prime 16290860017 :=
  pocklington_certifyKR _ 5 339392917 <| .base prime_339392917

end PrimeCert
