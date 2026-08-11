/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.Meta.SieveLookup

/-! # Verifying `sieve_lookup` against a 1e8 cache

Builds the sieve to `100000000` and proves four primes through it, the largest just under the
bound.
-/

open PrimeCert.Sieve

set_option maxRecDepth 100000 in
run_sieve 100000000

example : Nat.Prime 5 := by sieve_lookup
example : Nat.Prime 1009 := by sieve_lookup
example : Nat.Prime 1000003 := by sieve_lookup
example : Nat.Prime 99999989 := by sieve_lookup
