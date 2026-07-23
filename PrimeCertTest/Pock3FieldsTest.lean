/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import PrimeCert.Meta.Pocklington3
import PrimeCert.SmallPrimes

/-! # Tests for the `pock3` optional sieve bound

`m` is now optional: the 4-field form `(N, root, mode, F)` computes the sieve bound
automatically; the legacy 5-field form `(N, root, m, mode, F)` still parses and proves.
-/

open PrimeCert

-- new 4-field form: `m` computed automatically
theorem pock3_no_m : Nat.Prime 73471 := by prime_cert
  [small {2; 7; 31}, pock3 (73471, 3, 7, 2 * 31)]

-- legacy 5-field form still parses and proves
theorem pock3_legacy_m : Nat.Prime 73471 := by prime_cert
  [small {2; 7; 31}, pock3 (73471, 3, 1, 7, 2 * 31)]
