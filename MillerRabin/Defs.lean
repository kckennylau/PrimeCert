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

/-! # Wieferich primes

A Wieferich prime satisfies `2^(p-1) ≡ 1 [MOD p²]`. As of 2025 the only known ones are 1093
and 3511.

This file holds the condition, its `Bool` form, and `wieferichAtK`, which reads the condition at
one position of the cached sieve. The range results built on it live in `WieferichBound`.
-/

@[expose] public def Wieferich (p : ℕ) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p^2]

@[expose] public noncomputable def wieferichK (p : ℕ) : Bool :=
  powModK 2 (p.sub 1) (p.pow 2) |>.beq 1

@[simp] theorem wieferichK_eq_true_iff (p : ℕ) (hp : p ≠ 1) : wieferichK p ↔ Wieferich p := by
  have hp2 : p ^ 2 ≠ 1 := by rwa [ne_eq, sq, mul_eq_one, and_self]
  rw [Wieferich, wieferichK, Nat.beq_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hp2,
    powModK_eq, Nat.pow_eq, Nat.sub_eq]

@[simp] public theorem wieferichK_eq_false_iff (p : ℕ) (hp : p ≠ 1) :
    wieferichK p = false ↔ ¬Wieferich p := by
  rw [← Bool.not_eq_true, wieferichK_eq_true_iff p hp]

open PrimeCert PrimeCert.Sieve

public theorem _root_.pow_eq_one_of_dvd {M : Type*} [Monoid M] {x : M} {m n : ℕ}
    (h₁ : x ^ m = 1) (h₂ : m ∣ n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h₂
  rw [pow_mul, h₁, one_pow]

/-! ## The condition at one position of the cached sieve -/

/-- The Wieferich check at one sieve index: true when the sieve bit at `t` is clear, or when the
number at `t` fails `2 ^ (n - 1) ≡ 1 [MOD n ^ 2]`. -/
@[expose] public noncomputable def wieferichAtK (t : ℕ) : Bool :=
  (testBitK sieveBits_1000000 t).not'.or' (wieferichK (valueK t)).not'
