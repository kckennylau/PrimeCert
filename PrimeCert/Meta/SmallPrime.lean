/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import PrimeCert.Meta.PrimeCert
public meta import PrimeCert.Meta.PrimeCert

/-! # The `small` certificate method

Looks up a pre-existing `PrimeCert.prime_<n>` declaration (from `SmallPrimes.lean`),
e.g. `PrimeCert.prime_31`. Used as a base case in certificate ladders.
-/

open Lean Meta Elab Qq

namespace PrimeCert.Meta

public section

/-- Syntax for the `small` method: just a numeric literal `n`.
Looks up the declaration `PrimeCert.prime_<n>` in the environment.

```lean
-- In a prime_cert% call:
prime_cert% [small {2; 3; 5; 7}, ...]
-- Each number must have a corresponding `PrimeCert.prime_<n>` theorem.
```
-/
syntax small_spec := num

meta def mkSmallProof : PrimeCertMethod ``small_spec := fun stx _ ↦ match stx with
  | `(small_spec| $n:num) => do
    have n := n.getNat
    have name : Name := (`PrimeCert).str s!"prime_{n}"
    return ⟨n, mkNatLit n, mkConst name⟩
  | _ => throwUnsupportedSyntax

@[prime_cert small] meta def PrimeCertExt.small : PrimeCertExt where
  syntaxName := ``small_spec
  methodName := ``mkSmallProof

end

end PrimeCert.Meta
