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

/-- Build the parity table and the running counts for numbers up to `n`, in batches of `len` steps,
each kernel-checked separately. The tables and their equations are held by generated declarations;
the two literals and the field width are returned. -/
def buildTables (n len : Nat) : MetaM (Nat × Nat × Nat) := do
  let qsName := `PrimeCert.Polya.lamQs
  let litName := `PrimeCert.Polya.lamLit
  let dataName := `PrimeCert.Polya.lamData
  if (← getEnv).contains litName then
    throwError "run_lam: a parity table already exists"
  let powers := primePowers n
  let w := Nat.log2 n + 1
  let qs := packFields powers w
  let fuel := powers.size
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
  return (lit, ones, w)

/-- Build the tables for numbers up to `n`, in batches of `defaultBatchLen` steps, or in `K`
batches when `K?` is given. -/
def runLam (n : Nat) (K? : Option Nat := none) : MetaM Unit := do
  let len := match K? with
    | some K => Nat.max 1 ((primePowers n).size + K - 1) / K
    | none => defaultBatchLen
  discard <| buildTables n len

/-- Command wrapper for `runLam`: `run_lam n` builds the certified parity table for numbers up to
`n`, and `run_lam n K` forces `K` batches. -/
elab "run_lam" nStx:num kStx:(num)? : command =>
  liftTermElabM <| runLam nStx.getNat (kStx.map (·.getNat))

/-- Width of a field of the certificate, and the offset that keeps each field positive. -/
def bigWidth : Nat := 21
def bigOffset : Nat := 1 <<< 20

private def mkBlockLoopK (xE vE cE lamE onesE wcE bigE stE : Expr) (len : Nat) : Expr :=
  mkAppN (mkConst ``blockLoopK)
    #[xE, vE, cE, lamE, onesE, wcE, bigE, mkRawNatLit bigWidth, mkRawNatLit bigOffset, stE,
      mkRawNatLit len]

/-- The number of runs of equal quotients in the recurrence for `L v`. -/
def blockCount (v : Nat) : Nat := Id.run do
  let mut fuel := 0
  let mut k := 2
  while k ≤ v do
    k := v / (v / k) + 1
    fuel := fuel + 1
  return fuel

/-- Returns the final state and a proof of `blockLoopK … 2 fuel = st`, split into batches of at most
`len` blocks; `v` distinguishes the names of the emitted batch lemmas. -/
private def emitBlockChain (x v cutoff lam ones wc big fuel len : Nat) : MetaM (Nat × Expr) := do
  let xE := mkRawNatLit x
  let vE := mkRawNatLit v
  let cE := mkRawNatLit cutoff
  let lamE := mkRawNatLit lam
  let onesE := mkRawNatLit ones
  let wcE := mkRawNatLit wc
  let bigE := mkRawNatLit big
  -- the loop starts at index 2 with both halves of the sum empty
  let lhsLoop := mkBlockLoopK xE vE cE lamE onesE wcE bigE (mkRawNatLit 2) fuel
  let mut st := 2
  let mut stE := mkRawNatLit 2
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := blockLoop x v cutoff lam ones wc big bigWidth bigOffset st step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"block_step_{v}_{i}"
    addThm stepName (mkBeqTrue (mkBlockLoopK xE vE cE lamE onesE wcE bigE stE step) nextE)
      Lean.reflBoolTrue
    proof := mkAppN (mkConst ``blockLoopK_chain)
      #[lhsLoop, xE, vE, cE, lamE, onesE, wcE, bigE, mkRawNatLit bigWidth,
        mkRawNatLit bigOffset, stE, nextE, mkRawNatLit step, mkRawNatLit rest, proof,
        mkConst stepName]
    st := next
    stE := nextE
    remaining := rest
  return (st, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop stE))

/-- The largest `r` with `r ^ 3 ≤ n`, by bisection. -/
def cbrt (n : Nat) : Nat := Id.run do
  let mut hi := 1
  while hi * hi * hi ≤ n do
    hi := hi * 2
  let mut lo := 0
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if mid * mid * mid ≤ n then lo := mid else hi := mid
  return lo

/-- Where to stop recursing and read from the table, when no cutoff is given: `x ^ (2/3)`, which at
`x = 906150257` is 943436, inside the band that measured fastest. -/
def defaultCutoff (x : Nat) : Nat := cbrt (x * x)

/-- Compute the running total of the Liouville values at `x`, from the tables below `cutoff` and
the recurrence at each larger argument `x / j`, taken in increasing order. -/
def runPolya (x cutoff : Nat) (K? : Option Nat := none) : MetaM Unit := do
  let len := match K? with
    | some K => Nat.max 1 K
    | none => defaultBatchLen
  let (lam, ones, w) ← buildTables cutoff len
  let top := x / cutoff
  let mut big := 0
  let mut last : Int := 0
  for jj in [0:top] do
    let j := top - jj
    let v := x / j
    let fuel := blockCount v
    let (st, proof) ← emitBlockChain x v cutoff lam ones w big fuel len
    let dataName := Name.mkSimple s!"block_data_{v}"
    addThm dataName
      (mkNatEqual (mkBlockLoopK (mkRawNatLit x) (mkRawNatLit v) (mkRawNatLit cutoff)
        (mkRawNatLit lam) (mkRawNatLit ones) (mkRawNatLit w) (mkRawNatLit big)
        (mkRawNatLit 2) fuel) (mkRawNatLit st)) proof
    -- L v is the whole part of the square root of v, minus the two halves of the sum
    last := (Nat.sqrt v : Int) - (stFieldC st 1 : Int) + (stFieldC st 2 : Int)
    big := big ||| ((last + bigOffset).toNat <<< (bigWidth * j))
  logInfo m!"L({x}) = {last}"

/-- Command wrapper for `runPolya`: `run_polya x` computes the running total at `x`, `run_polya x c`
sets the cutoff, and `run_polya x c K` also sets the batch length. -/
elab "run_polya" xStx:num cStx:(num)? kStx:(num)? : command => do
  let x := xStx.getNat
  liftTermElabM <| runPolya x ((cStx.map (·.getNat)).getD (defaultCutoff x)) (kStx.map (·.getNat))

end PrimeCert.Polya
