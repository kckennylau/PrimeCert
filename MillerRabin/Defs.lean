/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient
public import PrimeCert.ForallB
import PrimeCert.ForMathlib
public import PrimeCert.SieveBase
meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PowMod

/-! # Wieferich and Mirimanoff primes

A Wieferich prime satisfies `2^(p-1) ≡ 1 [MOD p²]`; a Mirimanoff prime satisfies
`3^(p-1) ≡ 1 [MOD p²]`. As of 2025, the only known Wieferich primes are 1093 and 3511;
the only known Mirimanoff primes are 11 and 1006003.

The main result `wieferich_mirimanoff` shows that no prime below 6000 is simultaneously
Wieferich and Mirimanoff. `miller_rabin_squarefree` applies it to prove that a number below
36 million passing the Fermat test to bases 2 and 3 is squarefree.
-/

def Wieferich (p : ℕ) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p^2]

def Mirimanoff (p : ℕ) : Prop :=
  3 ^ (p - 1) ≡ 1 [MOD p^2]

@[expose] public noncomputable def wieferichK (p : ℕ) : Bool :=
  powModK 2 (p.sub 1) (p.pow 2) |>.beq 1

@[expose] public noncomputable def mirimanoffK (p : ℕ) : Bool :=
  powModK 3 (p.sub 1) (p.pow 2) |>.beq 1

@[simp] theorem wieferichK_eq_true_iff (p : ℕ) (hp : p ≠ 1) : wieferichK p ↔ Wieferich p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Wieferich, wieferichK, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModK_eq, Nat.pow_eq, Nat.sub_eq]

@[simp] theorem wieferichK_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    wieferichK p = false ↔ ¬Wieferich p := by
  rw [← Bool.not_eq_true, wieferichK_eq_true_iff p hp]

@[simp] theorem mirimanoffK_eq_true_iff (p : ℕ) (hp : p ≠ 1) : mirimanoffK p ↔ Mirimanoff p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Mirimanoff, mirimanoffK, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModK_eq, Nat.pow_eq, Nat.sub_eq]

@[simp] theorem mirimanoffK_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    mirimanoffK p = false ↔ ¬Mirimanoff p := by
  rw [← Bool.not_eq_true, mirimanoffK_eq_true_iff p hp]

/-! # We check odd numbers up to 6000 in the classes 1%6 and 5%6 -/

open PrimeCert PrimeCert.Sieve

/-- The check at one sieve index: a clear bit skips the number, a set bit checks both conditions
on it. -/
@[expose] public noncomputable def checkAt (t : ℕ) : Bool :=
  (testBitK sieveBits_1000000 t).not'.or'
    ((wieferichK (numK t)).not'.or' (mirimanoffK (numK t)).not')

theorem wieferich_mirimanoff₁ : ∀ n < 6000, n % 6 = 1 →
    (wieferichK n).not'.or' (mirimanoffK n).not' :=
  forallB_of_mod _ (start := 1) (len := 1000) (step := 6) (by quickRfl)

theorem wieferich₅ : ∀ n < 6000, n % 6 = 5 → !wieferichK n :=
  forallB_of_mod _ (start := 5) (len := 1000) (step := 6) (by quickRfl)

public theorem wieferich_mirimanoff {p : ℕ} (hp : p.Prime) (p_bound : p < 6000) :
    ¬(2 ^ (p - 1) ≡ 1 [MOD p^2]) ∨ ¬(3 ^ (p - 1) ≡ 1 [MOD p^2]) := by
  obtain hp₄ | hp₄ := lt_or_ge p 4
  · clear p_bound
    revert hp
    decide +revert +kernel
  have hp₁ : p ≠ 1 := hp.ne_one
  obtain h₁ | h₅ := hp.mod_six_eq_one_or_five (by lia) (by lia)
  · simpa [hp₁] using! wieferich_mirimanoff₁ p p_bound h₁
  · simpa [hp₁] using! Or.inl <| wieferich₅ p p_bound h₅

public theorem _root_.pow_eq_one_of_dvd {M : Type*} [Monoid M] {x : M} {m n : ℕ}
    (h₁ : x ^ m = 1) (h₂ : m ∣ n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h₂
  rw [pow_mul, h₁, one_pow]

public theorem miller_rabin_squarefree {n : ℕ} (hn₀ : n ≠ 0) (hn : n < 36000000)
    (h₂ : 2 ^ (n - 1) ≡ 1 [MOD n]) (h₃ : 3 ^ (n - 1) ≡ 1 [MOD n]) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpn
  rw [← sq] at hpn
  have hn₁ : n ≠ 1 := by
    rintro rfl
    rw [Nat.dvd_one, sq, mul_eq_one, and_self] at hpn
    subst hpn
    exact absurd hp (by decide)
  have h₁ : _ < 6000 ^ 2 := (Nat.le_of_dvd (pos_of_ne_zero hn₀) hpn).trans_lt hn
  rw [Nat.pow_lt_pow_iff_left (by decide)] at h₁
  have hn₁' : n - 1 ≠ 0 := by lia
  have hp₁ : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  have := NeZero.mk hp₁
  have h₅ : (n - 1).gcd p = 1 := by
    rw [Nat.gcd_sub_left_left_of_dvd _ (by lia)
      (dvd_trans (dvd_pow_self _ (by lia)) hpn), Nat.gcd_one_left]
  have h₄ (a) (ha : a ^ (n - 1) ≡ 1 [MOD n]) : a ^ (p - 1) ≡ 1 [MOD p^2] := by
    replace ha := ha.of_dvd hpn
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at ha ⊢
    let a' := Units.ofPowEqOne _ _ ha hn₁'
    have ha₁ : a' ^ (n - 1) = 1 := Units.pow_ofPowEqOne _ _
    have ha₂ := pow_card_eq_one (x := a')
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp, pow_one] at ha₂
    replace ha₂ := pow_gcd_eq_one.2 ⟨ha₁, ha₂⟩
    rw [Nat.gcd_mul_right_right_of_gcd_eq_one h₅] at ha₂
    replace ha₂ := pow_eq_one_of_dvd ha₂ (Nat.gcd_dvd_right _ _)
    simpa [a'] using congr(($ha₂ : ZMod (p ^ 2)))
  have := wieferich_mirimanoff hp h₁
  tauto
