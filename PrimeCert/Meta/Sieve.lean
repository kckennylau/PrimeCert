/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.Meta.SieveCache

/-! # The `run_sieve` command

Builds a certified sieve cache and registers it in `sieveCacheExt`. Split out from
`PrimeCert.Sieve` so the computational core stays free of metaprogramming.
-/

namespace PrimeCert.Sieve

open Lean Elab Command Meta

/-- The statement `Nat.beq a b = true`. -/
private def mkBeqTrue (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

private def mkSieveLoopK (mE bits : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``sieveLoopK) #[mE, bits, mkRawNatLit start, mkRawNatLit len]

private def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Sieving steps per batch, used when `run_sieve` is given no batch count. -/
def defaultBatchLen : Nat := 16

/-- Returns a bitset `b` and a proof of `sieveLoopK M (initK M) 1 fuel = b`, split into batches of
at most `len` steps; `n` only distinguishes the names of the emitted batch lemmas. -/
private def emitChain (n M fuel len : Nat) : MetaM (Nat × Expr) := do
  let mE := mkRawNatLit M
  let initE := mkApp (mkConst ``initK) mE
  -- the fixed left-hand side of the chain: the full loop on the kernel-side initial bitset
  let lhsLoop := mkSieveLoopK mE initE 1 fuel
  let mut bits := initK M
  let mut bitsE := mkRawNatLit bits
  -- enter the chain by replacing `initK M` with its literal: initK M = b_0
  let initName := Name.mkSimple s!"chain_init_{n}"
  addThm initName (mkBeqTrue initE bitsE) Lean.reflBoolTrue
  -- invariant: proof : lhsLoop = sieveLoopK M bits start remaining
  let mut proof := mkAppN (mkConst ``sieveLoopK_congr)
    #[mE, initE, bitsE, mkRawNatLit 1, mkRawNatLit fuel, mkConst initName]
  let mut start := 1
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := sieveLoop M bits start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"chain_step_{n}_{i}"
    addThm stepName (mkBeqTrue (mkSieveLoopK mE bitsE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``sieveLoopK_chain)
      #[lhsLoop, mE, bitsE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest,
        proof, mkConst stepName]
    bits := next
    bitsE := nextE
    start := start + step
    remaining := rest
  -- the chain ends at a zero-step loop on `bits`, which is definitionally `bits` itself
  return (bits, ← mkExpectedTypeHint proof (mkNatEq lhsLoop bitsE))

/-- Build the cache for numbers up to `n` and register it. The sieving is split into batches of
`len?` steps, defaulting to `defaultBatchLen`, and each batch is kernel-checked separately. The
bitset and its equation are held by generated declarations; `sieve_lookup` finds them through the
registry. -/
def runSieve (n : Nat) (len? : Option Nat := none) : MetaM Unit := do
  if (← sieveCaches).any (·.hi == n) then
    throwError "run_sieve: a sieve cache up to {n} already exists"
  let idx := (← sieveCaches).size
  let litName := Name.mkNum `PrimeCert.Sieve.sieveLit idx
  let dataName := Name.mkNum `PrimeCert.Sieve.sieveData idx
  let sq := Nat.sqrt n + 1
  let fuel := (sq - 1) / 3
  let len := Nat.max 1 (len?.getD defaultBatchLen)
  let (lit, proof) ← emitChain n ((n - 1) / 3) fuel len
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit lit, hints := .regular 0, safety := .safe }
  -- `proof` ends at a zero-step loop on the final bitset, which is definitionally both the
  -- literal and, on the other side, `sieveK n sq`
  let lhs := mkAppN (mkConst ``sieveK) #[mkRawNatLit n, mkRawNatLit sq]
  addThm dataName (mkNatEq lhs (mkConst litName)) proof
  sieveCacheExt.add { lo := 5, hi := n, litName, dataName }

/-- Command wrapper for `runSieve`: `run_sieve n` builds the certified cache for numbers up to
`n`, and `run_sieve n len` sets the batch length to `len` sieving steps. -/
elab "run_sieve" nStx:num lenStx:(num)? : command =>
  liftTermElabM <| runSieve nStx.getNat (lenStx.map (·.getNat))

end PrimeCert.Sieve
