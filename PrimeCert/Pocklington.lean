/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import PrimeCert.ForMathlib
import PrimeCert.Meta.SmallPrime
import PrimeCert.PredMod
import PrimeCert.PowMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ScopedNS
import Mathlib.Data.Finset.Pairwise

/-! # Pocklington's primality certificate

To use this certificate for primality of `N`, factorise `N - 1` completely.
1. If the largest factor `p` is `> √N`, then set `F₁ = p`.
2. Otherwise, set `F₁` to be the product of enough prime factors to be `> √N`.
3. Then, find a primitive root `a` of `N`.
4. Then `a` will satisfy the conditions required, which are:
  - `a ^ (N - 1) ≡ 1 (mod N)`
  - For each prime factor `p` of `F₁`, `gcd(a ^ ((N - 1) / p) - 1, N) = 1`.
-/

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
  -- `omega` is >2x faster than `lia` here (56ms vs 144ms median over 5 runs)
  replace hn₁ : 1 < N := by omega
  have hf₀ : F₁ ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hf₁
    omega
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

/-- The Pocklington primitive-root predicate: for each prime factor `p` of `F₁`,
`gcd(root ^ ((N-1)/p) - 1, N) = 1`. Built incrementally by `PocklingtonPred.step`. -/
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
  have := Nat.succ_le_iff.mp <| (Nat.le_sub_iff_add_le (by grind)).mp <|
    Nat.le_of_dvd (by grind) this
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
  rw [← Nat.one_mod_eq_one.mpr (show N ≠ 1 by lia)] at psp
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
    PocklingtonPred N root (F₂.mul (p.pow e)) := by
  by_cases hf₂ : F₂ = 0
  · simp [hf₂]
  by_cases he : e = 0
  · simpa [he]
  by_cases hn : N = 0
  · simp [hn, predModKR, powModTR_eq, powMod] at step
  rw [PocklingtonPred] at ih ⊢
  rw [Nat.mul_eq, Nat.pow_eq]
  rw [Nat.primeFactors_mul hf₂ (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow he hp]
  simp_rw [Finset.union_singleton, Finset.forall_mem_insert]
  refine ⟨?_, ih⟩
  simp only [Nat.pred_eq_sub_one, Nat.div_eq_div, Nat.beq_eq] at step
  simp only [Nat.blt_eq] at hroot
  rw [predModKR_eq hn (by rw [powModTR_eq]; exact (Nat.mod_lt _ (by lia)).le),
    ← Nat.add_sub_assoc (by lia), powModTR_eq, powMod] at step
  by_cases hp : root ^ ((N - 1) / p) % N = 0
  · rw [← Nat.dvd_iff_mod_eq_zero] at hp
    obtain ⟨r, hr⟩ := hp
    have : r ≠ 0 := by rintro rfl; rw [mul_zero, pow_eq_zero_iff'] at hr; lia
    replace this := mul_ne_zero hn this
    rw [hr, Nat.gcd_mul_left_sub_left (by lia), Nat.gcd_one_left]
  rwa [add_comm, Nat.add_sub_assoc (by lia), Nat.add_mod_left, Nat.mod_sub_of_le (by lia),
    Nat.mod_mod, ← Nat.gcd_rec, Nat.gcd_comm] at step

theorem PocklingtonPred.step {N root F₂ p : ℕ} (hp : p.Prime)
    (ih : PocklingtonPred N root F₂)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root (F₂.mul p) := by
  simpa using PocklingtonPred.step_pow (e := 1) hp ih step hroot

theorem PocklingtonPred.base_pow {N root p e : ℕ} (hp : p.Prime)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root (p.pow e) := by
  simpa using PocklingtonPred.step_pow hp .one step hroot

theorem PocklingtonPred.base {N root p : ℕ} (hp : p.Prime)
    (step : ((predModKR (powModTR root (N.pred.div p) N) N).gcd N).beq 1 :=
      by exact eagerReduce (Eq.refl true))
    (hroot : Nat.blt 0 root = true := by exact eagerReduce (Eq.refl true)) :
    PocklingtonPred N root p := by
  simpa using PocklingtonPred.base_pow (e := 1) hp step hroot
