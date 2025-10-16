/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.Meta.PrimeCert
import PrimeCert.SmallPrimes

/-! # The default extension for small primes

... where "small" means that we have a proof for it in exactly `PrimeCert.prime_$n`.
-/

open Lean Meta Elab Qq

namespace PrimeCert.Tactic

syntax small_spec := num

def mkSmallProof (stx : TSyntax ``small_spec) (_ : Std.HashMap Nat PrimeProofEntry) :
    MetaM (Nat × (N : Q(Nat)) × Q(($N).Prime)) := match stx with
  | `(small_spec| $n:num) => do
    have n := n.getNat
    have name : Name := (`PrimeCert).str s!"prime_{n}"
    return ⟨n, mkNatLit n, mkConst name⟩
  | _ => throwUnsupportedSyntax

@[prime_cert small] def PrimeCertExt.small : PrimeCertExt where
  syntaxName := ``small_spec
  quotedSyntax := .mk <| mkNode `stx #[mkIdent ``small_spec]
  method := mkSmallProof

syntax "small" small_spec : step_group
syntax "small" "{" sepBy1(small_spec,"; ") "}" : step_group

example : Nat.Prime 997 :=
  prime_cert% [small {3; 2; 5; 997}]

example : Nat.Prime 997 :=
  prime_cert% [small 997]

end PrimeCert.Tactic
