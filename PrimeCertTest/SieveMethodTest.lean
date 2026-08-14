/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import PrimeCert.Meta.SieveLookup
import PrimeCert.Meta.SmallPrime
import PrimeCert.Meta.Pocklington3

/-! # Tests for the `sieve` certificate method -/

open PrimeCert.Sieve

/-! Reading primes off the built-in cache through `prime_cert`. -/

example : Nat.Prime 1999 := by prime_cert [sieve 1999]
example : Nat.Prime 1993 := by prime_cert [sieve {1009; 1993}]

example : Nat.Prime 2 := by prime_cert [sieve {2}]
example : Nat.Prime 5 := by prime_cert [sieve {2; 3; 5}]

/-! Mixing the sieve with another method in one ladder. -/

example : Nat.Prime 1997 := by prime_cert [small {2; 3}, sieve {1993; 1997}]

/-! Feeding sieve lookups to a Pocklington step. -/

example : Nat.Prime 16290860017 := by
  prime_cert [sieve {3; 29},
    pock3 (339392917, 2, 3, 2 ^ 2 * 3 ^ 4 * 29),
    pock3 (16290860017, 5, 0, 2 ^ 4 * 3 * 339392917)]
