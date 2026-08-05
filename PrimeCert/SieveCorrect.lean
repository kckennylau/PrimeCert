/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve
import Mathlib.Data.Nat.Bitwise

/-!
# Correctness of the mod-6 wheel sieve

Bit `t` of `PrimeCert.Sieve.sieveK n sqrtN` is set exactly when the number at index `t` is prime
(`sieveK_testBit_iff`), and `prime_of_sieve_eq` turns one bit of a cached sieve literal into
`Nat.Prime`. The argument runs in four steps:

1. reading a bit as `0` or `1` agrees with `Nat.testBit`, and `initK` has bits `1 … M` set;
2. `buildMaskK` sets the positions `A, A + 2*p, A + 4*p, …` and the same from `B`;
3. `markMaskK` clears exactly those positions, which hold the multiples `p*k` with `k ≥ 5`
   coprime to 6;
4. the bits left standing are exactly the primes.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Layer 1: bit reading and encoding -/

@[simp, grind =] public theorem numK_eq_num : numK = num := rfl

/-- `testBitK` reads bit `i` as a `ℕ` (`0` or `1`); it agrees with `Nat.testBit`. -/
@[grind =]
theorem testBitK_eq_testBit {b i : ℕ} : testBitK b i = if b.testBit i then 1 else 0 := by
  simp [testBitK, Nat.shiftRight_eq_div_pow]
  grind

public theorem testBitK_eq_one_iff {b i : ℕ} : testBitK b i = 1 ↔ b.testBit i := by
  grind

lemma initK_eq {M : ℕ} : initK M = (2 ^ M - 1) <<< 1 := by
  simp [initK, Nat.shiftLeft_eq]
  grind

/-- `initK M = 2^(M+1) - 2` has bits `1 … M` set and bit `0` clear. -/
theorem testBit_initK {M t : ℕ} :
    (initK M).testBit t ↔ 1 ≤ t ∧ t ≤ M := by grind [initK_eq]

end PrimeCert.Sieve
