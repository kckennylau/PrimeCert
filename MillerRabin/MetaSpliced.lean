/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import MillerRabin.Spliced
public meta import PrimeCert.ForallB

/-! # The `wieferich_cover` command

Emits one theorem per residue class coprime to the wheel modulus, then `Cover m len step m`,
whose proof applies each class theorem at its own remainder.
-/

namespace MillerRabin

open Lean Elab Command Meta PrimeCert

/-- The proposition `b = true`, for `b : Bool`. -/
meta def mkEqTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- The scan of the class of `r`, as a statement. -/
meta def mkClaim (r len step : Nat) : Expr :=
  mkEqTrue <| mkAppN (mkConst ``PrimeCert.forallB)
    #[mkConst ``wieferichAtK, mkApp (mkConst ``PrimeCert.Sieve.indexK) (mkRawNatLit r),
      mkRawNatLit len, mkRawNatLit step]

/-- `Cover m len step k`, as a statement. -/
meta def mkCover (m len step k : Nat) : Expr :=
  mkAppN (mkConst ``Cover)
    #[mkRawNatLit m, mkRawNatLit len, mkRawNatLit step, mkRawNatLit k]

/-- Add `name : type := value` to the environment as a theorem. -/
meta def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- `wieferich_cover m n` emits the class theorems for the wheel modulus `m` over the numbers
below `n`, then the cover over every remainder of `m`. -/
syntax (name := wieferichCover) "wieferich_cover " num num : command

@[command_elab wieferichCover]
public meta def elabWieferichCover : CommandElab := fun stx ↦ do
  match stx with
  | `(wieferich_cover $mStx:num $nStx:num) => do
    let m := mStx.getNat
    let n := nStx.getNat
    liftTermElabM do
      let len := n / m + 1
      let step := m / 3
      let exceptions := [1093 % m, 3511 % m]
      let mLit := mkRawNatLit m
      let lenLit := mkRawNatLit len
      let stepLit := mkRawNatLit step
      -- One theorem per class, each its own kernel check.
      let mut covered : List Nat := []
      for r in [0:m] do
        if Nat.gcd r m == 1 && !exceptions.contains r then
          addThm (`MillerRabin ++ Name.mkSimple s!"class_{m}_{r}")
            (mkClaim r len step) reflBoolTrue
          covered := r :: covered
      -- The cover, one step per remainder, each splicing in that class's theorem.
      let mut proof := mkAppN (mkConst ``cover_zero) #[mLit, lenLit, stepLit]
      for r in [0:m] do
        let rLit := mkRawNatLit r
        let name := `MillerRabin ++ Name.mkSimple s!"class_{m}_{r}"
        let stepProof ←
          if covered.contains r then
            pure <| mkAppN (mkConst ``step_of_scan)
              #[mLit, lenLit, stepLit, rLit, mkConst name]
          else if exceptions.contains r then
            pure <| mkAppN (mkConst ``step_of_exception)
              #[mLit, lenLit, stepLit, rLit, reflBoolTrue]
          else
            pure <| mkAppN (mkConst ``step_of_gcd)
              #[mLit, lenLit, stepLit, rLit, reflBoolTrue]
        proof := mkAppN (mkConst ``cover_succ)
          #[mLit, lenLit, stepLit, rLit, proof, stepProof]
      addThm (`MillerRabin ++ Name.mkSimple s!"cover_{m}") (mkCover m len step m) proof
      logInfo s!"emitted {covered.length} class theorems and the cover for modulus {m}"
  | _ => throwUnsupportedSyntax

end MillerRabin
