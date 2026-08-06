/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.Meta.Sieve

/-! # The built-in sieve cache

A certified sieve for numbers up to `100000`, built when this module compiles and available to
`sieve_lookup` and `prime_cert [sieve …]` on import. Larger sieves are added with `run_sieve`.
-/

namespace PrimeCert.Sieve

run_sieve 100000

end PrimeCert.Sieve
