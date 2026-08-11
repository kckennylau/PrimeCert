/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.Meta.SieveLookup
import PrimeCert.Meta.SmallPrime
import PrimeCert.Meta.Pocklington3

/-! # Tests for `sieve_lookup` and the `sieve` certificate method

The built-in cache from `PrimeCert.SieveBase` covers numbers up to `1000000`; a larger one is
built here to check that caches coexist.
-/

open PrimeCert.Sieve

/-! Reading primes off the built-in cache, by tactic and through `prime_cert`. -/

example : Nat.Prime 5 := by sieve_lookup
example : Nat.Prime 1009 := by sieve_lookup
example : Nat.Prime 99991 := by sieve_lookup

example : Nat.Prime 1999 := by prime_cert [sieve 1999]
example : Nat.Prime 1993 := by prime_cert [sieve {1009; 1993}]

/-! Mixing the sieve with another method in one ladder. -/

example : Nat.Prime 1997 := by prime_cert [small {2; 3}, sieve {1993; 1997}]

/-! Feeding sieve lookups to a Pocklington step. -/

example : Nat.Prime 16290860017 := by
  prime_cert [sieve {3; 29},
    pock3 (339392917, 2, 3, 2 ^ 2 * 3 ^ 4 * 29),
    pock3 (16290860017, 5, 0, 2 ^ 4 * 3 * 339392917)]

/-! The primes the sieve's numbers skip. -/

example : Nat.Prime 2 := by sieve_lookup
example : Nat.Prime 3 := by sieve_lookup

example : Nat.Prime 2 := by prime_cert [sieve {2}]
example : Nat.Prime 5 := by prime_cert [sieve {2; 3; 5}]

/-! Rejected inputs. -/

/-- error: sieve lookup: 8 must be 2, 3, or coprime to 6 -/
#guard_msgs in
example : Nat.Prime 8 := by sieve_lookup

/-- error: sieve lookup: bit 333 of the sieve is clear, so 1001 is not prime -/
#guard_msgs in
example : Nat.Prime 1001 := by sieve_lookup

/-- error: sieve lookup: no sieve cache covers 1000003; the caches in scope are [(5, 1000000)] -/
#guard_msgs in
example : Nat.Prime 1000003 := by sieve_lookup

/-- error: sieve_lookup: goal is not `Nat.Prime _` -/
#guard_msgs in
example : 2 + 2 = 4 := by sieve_lookup

/-- error: run_sieve: the cache for 5..1000000 already covers 5..1000000 -/
#guard_msgs in
run_sieve 1000000

/-! A second, larger cache coexists, and lookups past the built-in bound use it. -/

run_sieve 2000000

example : Nat.Prime 1000003 := by sieve_lookup
example : Nat.Prime 1009 := by sieve_lookup
