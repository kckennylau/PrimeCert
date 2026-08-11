/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.Meta.SieveLookup

/-! # Tests for `sieve_lookup`

The built-in cache from `PrimeCert.SieveBase` covers numbers up to `1000000`; a larger one is
built here to check that caches coexist.
-/

open PrimeCert.Sieve

/-! Reading primes off the built-in cache. -/

example : Nat.Prime 5 := by sieve_lookup
example : Nat.Prime 1009 := by sieve_lookup
example : Nat.Prime 99991 := by sieve_lookup

/-! The primes the sieve's numbers skip. -/

example : Nat.Prime 2 := by sieve_lookup
example : Nat.Prime 3 := by sieve_lookup

/-! Rejected inputs. -/

/-- error: sieve lookup: 8 is even, so it is not prime -/
#guard_msgs in
example : Nat.Prime 8 := by sieve_lookup

/-- error: sieve lookup: 9 is a multiple of 3, so it is not prime -/
#guard_msgs in
example : Nat.Prime 9 := by sieve_lookup

/-- error: sieve lookup: 1 is not prime -/
#guard_msgs in
example : Nat.Prime 1 := by sieve_lookup

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

/-- info: 1009 uses the cache for 5..1000000 -/
#guard_msgs in
open Lean in
run_cmd do
  let some c ← Elab.Command.liftCoreM <| findSieveCache 1009 | throwError "no cache covers 1009"
  logInfo s!"1009 uses the cache for {c.lo}..{c.hi}"
