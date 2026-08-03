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

The prime powers are packed here into `w`-bit fields and handed to the table builder. The emitted
equation holds for that packing whatever it contains; tying its fields to the prime powers is
`PolyaCorrect`.
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

private def mkLamLoopK (qsE wE mE lamE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``lamLoopK) #[qsE, wE, mE, lamE, mkRawNatLit start, mkRawNatLit len]

private def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Prime powers per batch, used when `run_lam` is given no batch count. -/
def defaultBatchLen : Nat := 256

/-- The prime powers `q ≤ M` in increasing order, computed natively. -/
def primePowers (M : Nat) : Array Nat := Id.run do
  let mut composite : Array Bool := Array.replicate (M + 1) false
  let mut out : Array Nat := #[]
  for p in [2:M + 1] do
    if !composite[p]! then
      let mut q := p
      while q ≤ M do
        out := out.push q
        q := q * p
      let mut j := p * p
      while j ≤ M do
        composite := composite.set! j true
        j := j + p
  return out.qsort (· < ·)

/-- Pack `qs` into one natural number as `w`-bit fields, lowest first. -/
def packFields (qs : Array Nat) (w : Nat) : Nat := Id.run do
  let mut out := 0
  for h : i in [0:qs.size] do
    out := out ||| (qs[i] <<< (w * i))
  return out

/-- Returns a table `lam` and a proof of `lamLoopK qs w M 0 0 fuel = lam`, split into batches of at
most `len` steps; `n` only distinguishes the names of the emitted batch lemmas. -/
private def emitChain (n M fuel len w qs : Nat) : MetaM (Nat × Expr) := do
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mE := mkRawNatLit M
  -- the fixed left-hand side of the chain: the full loop on the empty table
  let lhsLoop := mkLamLoopK qsE wE mE (mkRawNatLit 0) 0 fuel
  let mut lam := 0
  let mut lamE := mkRawNatLit 0
  -- invariant: proof : lhsLoop = lamLoopK qs w M lam start remaining, and the empty table needs no
  -- step to enter the chain
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut start := 0
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := lamLoop qs w M lam start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"lam_step_{n}_{i}"
    addThm stepName (mkBeqTrue (mkLamLoopK qsE wE mE lamE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``lamLoopK_chain)
      #[lhsLoop, qsE, wE, mE, lamE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest,
        proof, mkConst stepName]
    lam := next
    lamE := nextE
    start := start + step
    remaining := rest
  -- the chain ends at a zero-step loop on `lam`, which is definitionally `lam` itself
  return (lam, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop lamE))

private def mkOnesLoopK (lamE wE tblE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``onesLoopK) #[lamE, wE, tblE, mkRawNatLit start, mkRawNatLit len]

/-- Returns the running counts `tbl` and a proof of `onesLoopK lam w 0 0 fuel = tbl`, split into
batches of at most `len` steps. -/
private def emitOnesChain (n fuel len w lam : Nat) : MetaM (Nat × Expr) := do
  let lamE := mkRawNatLit lam
  let wE := mkRawNatLit w
  let lhsLoop := mkOnesLoopK lamE wE (mkRawNatLit 0) 0 fuel
  let mut tbl := 0
  let mut tblE := mkRawNatLit 0
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut start := 0
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := onesLoop lam w tbl start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"ones_step_{n}_{i}"
    addThm stepName (mkBeqTrue (mkOnesLoopK lamE wE tblE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``onesLoopK_chain)
      #[lhsLoop, lamE, wE, tblE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest,
        proof, mkConst stepName]
    tbl := next
    tblE := nextE
    start := start + step
    remaining := rest
  return (tbl, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop tblE))

/-- Build the parity table for numbers up to `n`. The prime powers are split into batches of
`defaultBatchLen`, or into `K` batches when `K?` is given, and each batch is kernel-checked
separately. The table and its equation are held by generated declarations. -/
def runLam (n : Nat) (K? : Option Nat := none) : MetaM Unit := do
  let qsName := `PrimeCert.Polya.lamQs
  let litName := `PrimeCert.Polya.lamLit
  let dataName := `PrimeCert.Polya.lamData
  if (← getEnv).contains litName then
    throwError "run_lam: a parity table already exists"
  let powers := primePowers n
  let w := Nat.log2 n + 1
  let qs := packFields powers w
  let fuel := powers.size
  let len := match K? with
    | some K => Nat.max 1 ((fuel + K - 1) / K)
    | none => defaultBatchLen
  addDecl <| Declaration.defnDecl
    { name := qsName, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit qs, hints := .regular 0, safety := .safe }
  let (lit, proof) ← emitChain n n fuel len w qs
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit lit, hints := .regular 0, safety := .safe }
  -- `proof` ends at a zero-step loop on the final table, which is definitionally both the literal
  -- and, on the other side, `lamK qs w n fuel`
  let lhs := mkAppN (mkConst ``lamK)
    #[mkRawNatLit qs, mkRawNatLit w, mkRawNatLit n, mkRawNatLit fuel]
  addThm dataName (mkNatEqual lhs (mkConst litName)) proof
  -- the running counts of set bits, one field per 32 positions
  let chunks := n / 32 + 1
  let (ones, onesProof) ← emitOnesChain n chunks len w lit
  addDecl <| Declaration.defnDecl
    { name := `PrimeCert.Polya.onesLit, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit ones, hints := .regular 0, safety := .safe }
  let onesLhs := mkAppN (mkConst ``onesK)
    #[mkRawNatLit lit, mkRawNatLit w, mkRawNatLit chunks]
  addThm `PrimeCert.Polya.onesData
    (mkNatEqual onesLhs (mkConst `PrimeCert.Polya.onesLit)) onesProof

/-- Command wrapper for `runLam`: `run_lam n` builds the certified parity table for numbers up to
`n`, and `run_lam n K` forces `K` batches. -/
elab "run_lam" nStx:num kStx:(num)? : command =>
  liftTermElabM <| runLam nStx.getNat (kStx.map (·.getNat))

end PrimeCert.Polya
