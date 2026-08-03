/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Lean
import PrimeCert.Polya

/-! # The `run_lam` command

Builds a certified parity table for the Liouville function up to `n`. Split out from
`PrimeCert.Polya` so the computational core stays free of metaprogramming.

The prime powers are supplied to the table builder as a bitset computed here. The emitted equation
holds for that bitset whatever it contains; tying it to the prime powers is `PolyaCorrect`.
-/

namespace PrimeCert.Polya

open Lean Elab Command Meta

/-- The statement `Nat.beq a b = true`. -/
private def mkBeqTrue (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

/-- The statement `a = b` for naturals. -/
private def mkNatEqual (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) a b

private def mkLamLoopK (ppE mE lamE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``lamLoopK) #[ppE, mE, lamE, mkRawNatLit start, mkRawNatLit len]

private def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Strides per batch, used when `run_lam` is given no batch count. -/
def defaultBatchLen : Nat := 16

/-- Bit `q` set exactly for the prime powers `q ≤ M`, computed natively. -/
def primePowerBits (M : Nat) : Nat := Id.run do
  let mut composite : Array Bool := Array.replicate (M + 1) false
  let mut bits := 0
  for p in [2:M + 1] do
    if !composite[p]! then
      let mut q := p
      while q ≤ M do
        bits := bits ||| (1 <<< q)
        q := q * p
      let mut j := p * p
      while j ≤ M do
        composite := composite.set! j true
        j := j + p
  return bits

/-- Returns a table `lam` and a proof of `lamLoopK pp M 0 2 fuel = lam`, split into batches of at
most `len` strides; `n` only distinguishes the names of the emitted batch lemmas. -/
private def emitChain (n M fuel len : Nat) (pp : Nat) : MetaM (Nat × Expr) := do
  let ppE := mkRawNatLit pp
  let mE := mkRawNatLit M
  -- the fixed left-hand side of the chain: the full loop on the empty table
  let lhsLoop := mkLamLoopK ppE mE (mkRawNatLit 0) 2 fuel
  let mut lam := 0
  let mut lamE := mkRawNatLit 0
  -- invariant: proof : lhsLoop = lamLoopK pp M lam start remaining, and the empty table needs no
  -- step to enter the chain
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut start := 2
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := lamLoop pp M lam start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"lam_step_{n}_{i}"
    addThm stepName (mkBeqTrue (mkLamLoopK ppE mE lamE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``lamLoopK_chain)
      #[lhsLoop, ppE, mE, lamE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest,
        proof, mkConst stepName]
    lam := next
    lamE := nextE
    start := start + step
    remaining := rest
  -- the chain ends at a zero-step loop on `lam`, which is definitionally `lam` itself
  return (lam, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop lamE))

/-- Build the parity table for numbers up to `n`. The strides are split into batches of
`defaultBatchLen`, or into `K` batches when `K?` is given, and each batch is kernel-checked
separately. The table and its equation are held by generated declarations. -/
def runLam (n : Nat) (K? : Option Nat := none) : MetaM Unit := do
  let ppName := `PrimeCert.Polya.lamPP
  let litName := `PrimeCert.Polya.lamLit
  let dataName := `PrimeCert.Polya.lamData
  if (← getEnv).contains litName then
    throwError "run_lam: a parity table already exists"
  let pp := primePowerBits n
  let fuel := n - 1
  let len := match K? with
    | some K => Nat.max 1 ((fuel + K - 1) / K)
    | none => defaultBatchLen
  addDecl <| Declaration.defnDecl
    { name := ppName, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit pp, hints := .regular 0, safety := .safe }
  let (lit, proof) ← emitChain n n fuel len pp
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit lit, hints := .regular 0, safety := .safe }
  -- `proof` ends at a zero-step loop on the final table, which is definitionally both the literal
  -- and, on the other side, `lamK pp n`
  let lhs := mkAppN (mkConst ``lamK) #[mkRawNatLit pp, mkRawNatLit n]
  addThm dataName (mkNatEqual lhs (mkConst litName)) proof

/-- Command wrapper for `runLam`: `run_lam n` builds the certified parity table for numbers up to
`n`, and `run_lam n K` forces `K` batches. -/
elab "run_lam" nStx:num kStx:(num)? : command =>
  liftTermElabM <| runLam nStx.getNat (kStx.map (·.getNat))

end PrimeCert.Polya
