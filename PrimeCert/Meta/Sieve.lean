/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import Lean.Elab.Command
public meta import PrimeCert.Meta.SieveCache
public meta import PrimeCert.Sieve

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

/-- Returns a bitset `b` and a proof of `sieveLoopK M (initK M) 1 fuel = b`, split into batches of
at most `len` steps; `n` only distinguishes the names of the emitted batch lemmas. -/
meta def emitChain (n M fuel len : Nat) : MetaM (Nat × Expr) := do
  let mE := mkRawNatLit M
  let initE := mkApp (mkConst ``initK) mE
  -- the fixed left-hand side of the chain: the full loop on the kernel-side initial bitset
  let lhsLoop := mkSieveLoopK mE initE 1 fuel
  let mut bits := initK M
  -- the run starts at the expression `initK M`, the batches at numerals, so the kernel is asked
  -- once to agree that the two coincide
  let initName := Name.mkSimple s!"chain_init_{n}"
  addThm initName (mkBeqTrue initE (mkRawNatLit bits)) Lean.reflBoolTrue
  -- what is proved so far: the target run equals one that begins at `bits` and still owes
  -- `fuel - i * len` steps, which each iteration lowers by `step`
  let mut proof := mkAppN (mkConst ``sieveLoopK_congr)
    #[mE, initE, mkRawNatLit bits, mkRawNatLit 1, mkRawNatLit fuel, mkConst initName]
  for i in [0:(fuel + len - 1) / len] do
    let start := 1 + i * len
    let owed := fuel - i * len
    let step := Nat.min len owed
    -- run this batch to find where it lands; `next` is what the theorem below claims
    let next := sieveLoop M bits start step
    let stepName := Name.mkSimple s!"chain_step_{n}_{i}"
    -- one kernel check per batch, sized by `len`: `step` steps from one numeral reach another
    addThm stepName (mkBeqTrue (mkSieveLoopK mE (mkRawNatLit bits) start step) (mkRawNatLit next))
      Lean.reflBoolTrue
    -- the last batch leaves nothing owed, so it yields the value of the whole run
    proof := if owed == step then
        mkAppN (mkConst ``sieveLoopK_last)
          #[lhsLoop, mE, mkRawNatLit bits, mkRawNatLit next, mkRawNatLit start, mkRawNatLit step,
            proof, mkConst stepName]
      else
        mkAppN (mkConst ``sieveLoopK_chain)
          #[lhsLoop, mE, mkRawNatLit bits, mkRawNatLit next, mkRawNatLit start, mkRawNatLit step,
            mkRawNatLit (owed - step), proof, mkConst stepName]
    bits := next
  return (bits, proof)

/-- Build the cache for numbers up to `n` and register it. The sieving runs in batches of `len?`
steps, defaulting to 16, each kernel-checked on its own; generated declarations hold the bitset
and its equation. -/
meta def runSieve (n : Nat) (len? : Option Nat := none) : MetaM Unit := do
  if let some c := (← sieveCaches).find? (n ≤ ·.hi) then
    throwError "run_sieve: a sieve cache up to {c.hi} already covers {n}"
  let idx := (← sieveCaches).size
  let litName := Name.mkNum `PrimeCert.Sieve.sieveLit idx
  let dataName := Name.mkNum `PrimeCert.Sieve.sieveData idx
  let sq := Nat.sqrt n + 1
  let fuel := (sq - 1) / 3
  let len := Nat.max 1 (len?.getD 16)
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
