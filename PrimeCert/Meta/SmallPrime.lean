/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.Meta.PrimeCert

/-! # The default extension for small primes

... where "small" means that we have a proof for it in exactly `PrimeCert.prime_$n`.
-/

open Lean Meta Elab Qq

namespace PrimeCert.Meta

syntax small_spec := num

def mkSmallProof : PrimeCertMethod ``small_spec := fun stx _ ↦ match stx with
  | `(small_spec| $n:num) => do
    have n := n.getNat
    have name : Name := (`PrimeCert).str s!"prime_{n}"
    return ⟨n, mkNatLit n, mkConst name⟩
  | _ => throwUnsupportedSyntax

@[prime_cert small] def PrimeCertExt.small : PrimeCertExt where
  syntaxName := ``small_spec
  methodName := ``mkSmallProof

end PrimeCert.Meta
