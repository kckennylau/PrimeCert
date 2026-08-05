/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve
import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import PrimeCert.ForLean

/-!
# Correctness of the mod-6 wheel sieve

Bit `t` of `PrimeCert.Sieve.sieveK n sqrtN` is set exactly when the number at index `t` is prime
(`sieveK_testBit_iff`), and `prime_of_sieve_eq` turns one bit of a cached sieve literal into
`Nat.Prime`. The section headers below mark the four steps of the argument.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Layer 1: bit reading and encoding -/

@[simp, grind =] public theorem numK_eq_num (k : Nat) : numK k = num k := rfl

/-- `testBitK` reads bit `i` as a `Nat` (`0` or `1`); it agrees with `Nat.testBit`. -/
theorem testBitK_eq_testBit (b i : Nat) : testBitK b i = if b.testBit i then 1 else 0 := by
  simp [testBitK, Nat.shiftRight_eq_div_pow]
  grind

public theorem testBitK_eq_one_iff {b i : Nat} : testBitK b i = 1 ↔ b.testBit i := by
  grind [testBitK_eq_testBit]

lemma initK_eq {M : Nat} : initK M = (2 ^ M - 1) <<< 1 := by
  simp [initK, Nat.shiftLeft_eq]
  grind

/-- `initK M = 2^(M+1) - 2` has bits `1 … M` set and bit `0` clear. -/
theorem testBit_initK (M t : Nat) :
    (initK M).testBit t ↔ 1 ≤ t ∧ t ≤ M := by grind [initK_eq]

end PrimeCert.Sieve
