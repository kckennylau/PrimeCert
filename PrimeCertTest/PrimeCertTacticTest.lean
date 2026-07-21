/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import PrimeCert.Meta.Pocklington3
import PrimeCert.SmallPrimes

/-! # Tests for the `prime_cert` tactic

Covers the goal shapes the tactic accepts: a bare `Nat.Prime n`, the general `Prime n`, and
conjunctions of these (including primes certified by different methods in one ladder).
-/

open PrimeCert

-- single `Nat.Prime` goal
example : Nat.Prime 31 := by prime_cert [small {31}]

-- general `Prime` goal (bridged via `Nat.Prime.prime`)
example : Prime 31 := by prime_cert [small {31}]

-- conjunction of two small primes
example : Nat.Prime 31 ∧ Nat.Prime 29 := by prime_cert [small {29; 31}]

-- conjunction mixing methods: 73471 via pock3, 7 via small
example : Nat.Prime 73471 ∧ Nat.Prime 7 := by
  prime_cert [small {2; 7; 31}, pock3 (73471, 3, 1, 7, 2 * 31)]

-- nested/longer conjunction
example : Nat.Prime 2 ∧ Nat.Prime 3 ∧ Prime 31 := by prime_cert [small {2; 3; 31}]
