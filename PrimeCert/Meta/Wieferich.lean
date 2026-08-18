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

/-- The proposition `b = true`, for `b : Bool`. -/
meta def mkEqTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- The `Bool` `forallB wieferichAt start len step`, with `start` an arbitrary expression. -/
meta def mkFold (startE : Expr) (len step : Nat) : Expr :=
  mkAppN (mkConst ``PrimeCert.forallB)
    #[mkConst ``wieferichAt, startE, mkRawNatLit len, mkRawNatLit step]

/-- The sieve index of `n`, as an expression. -/
meta def mkIndex (nE : Expr) : Expr :=
  mkApp (mkConst ``PrimeCert.Sieve.index) nE

/-- The statement that the fold over the class of `r` holds. -/
meta def mkClaim (rE : Expr) (len step : Nat) : Expr :=
  mkEqTrue (mkFold (mkIndex rE) len step)

/-- The statement for a range starting at position `j` of the class of `r`. -/
meta def mkClaimAt (r j len step : Nat) : Expr :=
  let start := mkApp2 (mkConst ``Nat.add) (mkIndex (mkRawNatLit r))
    (mkApp2 (mkConst ``Nat.mul) (mkRawNatLit step) (mkRawNatLit j))
  mkEqTrue (mkFold start len step)

/-- The list literal `[r₁, …, rₖ] : List ℕ`. -/
meta def mkNatList : List Nat → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) Nat.mkType
  | r :: rs => mkApp3 (mkConst ``List.cons [Level.zero]) Nat.mkType (mkRawNatLit r) (mkNatList rs)

/-- Add `name : type := value` to the environment as a theorem. -/
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
      let len := n / m + 1
      let step := m / 3
      -- Each range stops short of the two known Wieferich primes below the bound.
      let exceptions := [1093, 3511]
      let mut acc : List Nat := []
      for r in [1:m] do
        if Nat.gcd r m == 1 && (r % 6 == 1 || r % 6 == 5)
            && exceptions.all (fun e => e % m != r) then
          acc := r :: acc
      let residues := acc.reverse
      -- One theorem per class, each its own kernel check.
      for r in residues do
        let name := `PrimeCert.Wieferich ++ Name.mkSimple s!"class_{m}_{r}"
        addThm name (mkClaim (mkRawNatLit r) len step) reflBoolTrue
      -- Each class holding an exception splits into the runs either side of it.
      for e in exceptions do
        let r := e % m
        let k := (e - r) / m
        if k > 0 then
          addThm (`PrimeCert.Wieferich ++ Name.mkSimple s!"class_{m}_{r}_below_{e}")
            (mkClaim (mkRawNatLit r) k step) reflBoolTrue
        if k + 1 < len then
          addThm (`PrimeCert.Wieferich ++ Name.mkSimple s!"class_{m}_{r}_above_{e}")
            (mkClaimAt r (k + 1) (len - k - 1) step) reflBoolTrue
      -- The list of classes, and the single statement quantified over it.
      let listName := `PrimeCert.Wieferich ++ Name.mkSimple s!"classes_{m}"
      -- `forceExpose` keeps the list readable from a module consumer, which `memB` needs.
      addDecl (forceExpose := true) <| Declaration.defnDecl
        { name := listName, levelParams := [],
          type := mkApp (mkConst ``List [Level.zero]) Nat.mkType,
          value := mkNatList residues, hints := .regular 0, safety := .safe }
      let motive ← withLocalDeclD `r Nat.mkType fun r =>
        mkLambdaFVars #[r] (mkClaim r len step)
      let mut proof := mkApp2 (mkConst ``List.forall_mem_nil [Level.zero]) Nat.mkType motive
      let mut tail : List Nat := []
      for r in residues.reverse do
        let name := `PrimeCert.Wieferich ++ Name.mkSimple s!"class_{m}_{r}"
        proof := mkAppN (mkConst ``forall_mem_cons_of [Level.zero])
          #[Nat.mkType, motive, mkRawNatLit r, mkNatList tail, mkConst name, proof]
        tail := r :: tail
      let allName := `PrimeCert.Wieferich ++ Name.mkSimple s!"all_classes_{m}"
      let allType ← withLocalDeclD `r Nat.mkType fun r => do
        let mem := mkAppN (mkConst ``Membership.mem [Level.zero, Level.zero])
          #[Nat.mkType, mkApp (mkConst ``List [Level.zero]) Nat.mkType,
            mkAppN (mkConst ``List.instMembership [Level.zero]) #[Nat.mkType],
            mkConst listName, r]
        mkForallFVars #[r] (← mkArrow mem (mkClaim r len step))
      addThm allName allType proof
      logInfo s!"emitted {residues.length} class lemmas for modulus {m} below {n}"
  | _ => throwUnsupportedSyntax

end PrimeCert.Wieferich
