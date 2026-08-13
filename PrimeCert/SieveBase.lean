/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve

/-! # The built-in sieve cache

A certified sieve for numbers up to `1000000`, built when this module compiles and registered on
import. Larger sieves are added with `run_sieve`.
-/

namespace PrimeCert.Sieve

run_sieve 1000000

end PrimeCert.Sieve
