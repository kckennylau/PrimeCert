/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.Wieferich
public meta import PrimeCert.ForallB

/-! # The `wieferich_check` command

Emits one fold per residue class of a wheel modulus, each covering the numbers of that class
below the bound and reading the cached sieve bit to skip the composites.
-/

namespace PrimeCert.Wieferich

open Lean Elab Command Meta PrimeCert

/-- The sieve index of `n`, where `num t = 3 * t + 1 + t % 2`. -/
meta def indexOf (n : Nat) : Nat := if n % 6 == 1 then (n - 1) / 3 else (n - 2) / 3

/-- The statement `forallB checkAt start len step = true`. -/
meta def mkClaim (start len step : Nat) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkAppN (mkConst ``PrimeCert.forallB)
      #[mkConst ``checkAt, mkRawNatLit start, mkRawNatLit len, mkRawNatLit step])
    (mkConst ``Bool.true)

meta def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- `wieferich_check m n` emits one theorem per residue class coprime to `m`, covering the
numbers of that class below `n`. -/
syntax (name := wieferichCheck) "wieferich_check " num num : command

@[command_elab wieferichCheck]
public meta def elabWieferichCheck : CommandElab := fun stx => do
  match stx with
  | `(wieferich_check $mStx:num $nStx:num) => do
    let m := mStx.getNat
    let n := nStx.getNat
    liftTermElabM do
      let mut count := 0
      for r in [1:m] do
        if Nat.gcd r m == 1 && r % 2 == 1 && r % 3 == 1 || Nat.gcd r m == 1 && r % 6 == 5 then
          let name := `PrimeCert.Wieferich ++ Name.mkSimple s!"class_{m}_{r}"
          addThm name (mkClaim (indexOf r) ((n - r) / m + 1) (m / 3)) reflBoolTrue
          count := count + 1
      logInfo s!"emitted {count} class lemmas for modulus {m} below {n}"
  | _ => throwUnsupportedSyntax

end PrimeCert.Wieferich
