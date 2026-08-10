/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Lean.Elab.Command
public meta import PrimeCert.Meta.SieveCache
public meta import PrimeCert.Sieve
public meta import PrimeCert.SieveCorrect

/-! # The `run_sieve` command

Builds a certified sieve cache and registers it in `sieveCacheExt`.
-/

namespace PrimeCert.Sieve

open Lean Elab Command Meta

/-- The statement `Nat.beq a b = true`. -/
meta def mkBeqTrue (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

meta def mkSieveLoopK (mE bits : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``sieveLoopK) #[mE, bits, mkRawNatLit start, mkRawNatLit len]

meta def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Given the top index `M`, the step count `fuel` and a batch length `len`, outputs the bitset `b`
and a proof of `sieveLoopK M (initK M) 1 fuel = b`. Emits lemmas `parent.init : initK M == b₀` and
`parent.step_i : sieveLoopK M bᵢ (1 + i * len) step == bᵢ₊₁` with `step ≤ len`, chained together by
`sieveLoopK_congr`, `sieveLoopK_chain` and `sieveLoopK_last`. -/
meta def emitChain (parent : Name) (M fuel len : Nat) : MetaM (Nat × Expr) := do
  let mE := mkRawNatLit M
  let initE := mkApp (mkConst ``initK) mE
  let lhsLoop := mkSieveLoopK mE initE 1 fuel
  let mut bits := initK M
  let mut bitsE := initE
  let env ← getEnv
  let mut proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsLoop]
  for i in [0:(fuel + len - 1) / len] do
    let start := 1 + i * len
    let owed := fuel - i * len
    let step := Nat.min len owed
    let next := sieveLoop M bits start step
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    addThm stepName (mkBeqTrue (mkSieveLoopK mE bitsE start step) (mkRawNatLit next))
      Lean.reflBoolTrue
    proof := if owed == step then
        mkAppN (mkConst ``sieveLoopK_last)
          #[lhsLoop, mE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit step,
            proof, mkConst stepName]
      else
        mkAppN (mkConst ``sieveLoopK_chain)
          #[lhsLoop, mE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit step,
            mkRawNatLit (owed - step), proof, mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
  return (bits, proof)

/-- Build the cache for numbers up to `n` and register it. The sieving runs in batches of `len?`
steps, defaulting to 16, each kernel-checked on its own; generated declarations hold the bitset
and its equation. -/
meta def runSieve (n : Nat) (len? : Option Nat := none) : MetaM Unit := do
  if let some c := (← sieveCaches).find? (n ≤ ·.hi) then
    throwError "run_sieve: a sieve cache up to {c.hi} already covers {n}"
  let litName := `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{n}"
  let dataName := `PrimeCert.Sieve ++ Name.mkSimple s!"sieveK_eq_{n}"
  let sq := Nat.sqrt n + 1
  let fuel := (sq - 1) / 3
  let len := Nat.max 1 (len?.getD 16)
  let (lit, proof) ← emitChain dataName ((n - 1) / 3) fuel len
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit lit, hints := .regular 0, safety := .safe }
  -- `proof` ends at a zero-step loop on the final bitset, which is definitionally both the
  -- literal and, on the other side, `sieveK n sq`
  let lhs := mkAppN (mkConst ``sieveK) #[mkRawNatLit n, mkRawNatLit sq]
  addThm dataName (mkNatEq lhs (mkConst litName)) proof
  -- the range bounds hold for this cache alone, so they are discharged here rather than at lookup
  let primeName := `PrimeCert.Sieve ++ Name.mkSimple s!"sievePrime_{n}"
  let primeProof := mkAppN (mkConst ``prime_of_sieve_eq)
    #[mkRawNatLit n, mkRawNatLit sq, mkConst litName, mkConst dataName,
      Lean.reflBoolTrue, Lean.reflBoolTrue]
  addThm primeName (← inferType primeProof) primeProof
  sieveCacheExt.add { lo := 5, hi := n, litName, dataName }

/-- Command wrapper for `runSieve`: `run_sieve n` builds the certified cache for numbers up to
`n`, and `run_sieve n len` sets the batch length to `len` sieving steps. -/
elab "run_sieve" nStx:num lenStx:(num)? : command =>
  liftTermElabM <| runSieve nStx.getNat (lenStx.map (·.getNat))

end PrimeCert.Sieve
