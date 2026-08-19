/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Wieferich

/-! # Definitions shared by the packed-list benchmark

`bitOnlyAt` performs the sieve-bit lookup of `wieferichAt` and holds at every position, so a fold
over it measures the lookups alone. `bench_check f m n` emits the same per-class folds as
`wieferich_check`, for the function `f`.
-/

namespace PrimeCert.Wieferich

open Lean Elab Command Meta PrimeCert PrimeCert.Sieve

/-- The sieve-bit lookup at one position, holding whatever the bit reads. -/
@[expose] public noncomputable def bitOnlyAt (t : ℕ) : Bool :=
  (testBitK sieveBits_1000000 t).not'.or' true

/-- `bench_check f m n` emits one fold of `f` per residue class coprime to `m`, covering the
numbers of that class below `n`. -/
syntax (name := benchCheck) "bench_check " ident num num : command

@[command_elab benchCheck]
public meta def elabBenchCheck : CommandElab := fun stx => do
  match stx with
  | `(bench_check $fStx:ident $mStx:num $nStx:num) => do
    let m := mStx.getNat
    let n := nStx.getNat
    liftTermElabM do
      let f ← realizeGlobalConstNoOverload fStx
      let len := n / m + 1
      let step := m / 3
      -- The classes of the two known Wieferich primes stay out of both variants, so that each
      -- covers the same positions.
      let exceptions := [1093, 3511]
      let mut acc : List Nat := []
      for r in [1:m] do
        if Nat.gcd r m == 1 && (r % 6 == 1 || r % 6 == 5)
            && exceptions.all (fun e => e % m != r) then
          acc := r :: acc
      for r in acc.reverse do
        let name := `PrimeCert.Wieferich ++ Name.mkSimple s!"bench_{f.getString!}_{r}"
        addThm name (mkClaim f (mkRawNatLit r) len step) reflBoolTrue
      logInfo s!"emitted {acc.length} folds of {f} for modulus {m} below {n}"
  | _ => throwUnsupportedSyntax

end PrimeCert.Wieferich
