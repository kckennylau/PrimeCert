/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Lean.Elab.Command
import Polya.Main
import Polya.PowerDefs
import PrimeCert.Meta.Sieve

/-! # The commands that drive a run

`run_lam n` builds a certified parity table for the Liouville function up to `n`, and
`run_polya x cutoff` builds the two tables of `L` and the block recursion reaching `L x`.

The prime powers are packed here into `w`-bit entries and handed to the table builder. The emitted
equation holds for that packing whatever it contains; tying its entries to the prime powers is
`Polya.Correct.TableSpec`.
-/

namespace PrimeCert.Polya

open Lean Elab Command Meta

/-- The statement `b = true`. -/
private def mkBoolTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- The statement `Nat.beq a b = true`. -/
private def mkBeqTrue (a b : Expr) : Expr :=
  mkBoolTrue (mkApp2 (mkConst ``Nat.beq) a b)

/-- The statement `a = b` for naturals. -/
private def mkNatEqual (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) a b

private def mkLamLoopK (qsE wE mE rE lamE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``lamLoopK) #[qsE, wE, mE, rE, lamE, mkRawNatLit start, mkRawNatLit len]

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

/-- `flags[n]` is true when `n` is prime, for `n ≤ M`. -/
def primeFlags (M : Nat) : Array Bool := Id.run do
  let mut flags : Array Bool := Array.replicate (M + 1) true
  if M ≥ 1 then
    flags := flags.set! 0 false
    flags := flags.set! 1 false
  let mut p := 2
  while p * p ≤ M do
    if flags[p]! then
      let mut j := p * p
      while j ≤ M do
        flags := flags.set! j false
        j := j + p
    p := p + 1
  return flags

/-- The primes `5 ≤ q ≤ M` in increasing order, which `bitCheckLoopK` checks against the sieve. -/
def sievedPrimes (M : Nat) : Array Nat := Id.run do
  let flags := primeFlags M
  let mut out : Array Nat := #[]
  for q in [5:M + 1] do
    if flags[q]! then out := out.push q
  return out

/-- 2, 3 and the prime powers of exponent at least two, in the order `hpLoopK` produces them: the
powers of 2, then of 3, then those of each base from 5 upward. -/
def collectedPowers (M : Nat) : Array Nat := Id.run do
  let flags := primeFlags M
  let mut out : Array Nat := #[]
  for q in [2:4] do
    let mut v := q
    while v ≤ M do
      out := out.push v
      v := v * q
  let mut t := 1
  while PrimeCert.Sieve.num t ≤ Nat.sqrt M do
    let p := PrimeCert.Sieve.num t
    if p ≤ M && flags[p]! then
      let mut v := p * p
      while v ≤ M do
        out := out.push v
        v := v * p
    t := t + 1
  return out

/-- Pack `qs` into one natural number as `w`-bit entries, lowest first. -/
def packEntries (qs : Array Nat) (w : Nat) : Nat := Id.run do
  let mut out := 0
  for h : i in [0:qs.size] do
    out := out ||| (qs[i] <<< (w * i))
  return out

/-- Emit `fuel` steps of one loop in batches of `len`, each batch kernel-checked. `mk st start len`
builds the loop's application, `run st start len` is its compiled twin, and `chain` with `chainArgs`
glues consecutive batches. Returns the final state and the glued proof. -/
private def emitLoopChain (tag : String) (fuel len st0 start0 : Nat)
    (mk : Expr → Nat → Nat → Expr) (run : Nat → Nat → Nat → Nat)
    (chain : Name) (chainArgs : Expr → Expr → Nat → Nat → Nat → Array Expr) :
    MetaM (Nat × Expr) := do
  -- the fixed left-hand side of the chain: the full loop on the starting state
  let lhsLoop := mk (mkRawNatLit st0) start0 fuel
  let mut st := st0
  let mut stE := mkRawNatLit st0
  -- invariant: proof : lhsLoop = <loop> st start remaining, and the starting state enters the chain
  -- in no steps
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut start := start0
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := run st start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"{tag}_step_{i}"
    addThm stepName (mkBeqTrue (mk stE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst chain)
      (#[lhsLoop] ++ chainArgs stE nextE start step rest ++ #[proof, mkConst stepName])
    st := next
    stE := nextE
    start := start + step
    remaining := rest
  -- the chain ends at a zero-step loop on `st`, which is definitionally `st` itself
  return (st, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop stE))

/-- Returns a table `lam` and a proof of `lamLoopK qs w M 0 0 fuel = lam`, split into batches of at
most `len` steps; `n` only distinguishes the names of the emitted batch lemmas. -/
private def emitChain (n M fuel len w rounds qs : Nat) : MetaM (Nat × Expr) := do
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mE := mkRawNatLit M
  let rE := mkRawNatLit rounds
  emitLoopChain s!"lam_{n}" fuel len 0 0 (mkLamLoopK qsE wE mE rE)
    (fun lam start step => lamLoop qs w M rounds lam start step)
    ``lamLoopK_chain
    (fun lamE nextE start step rest =>
      #[qsE, wE, mE, rE, lamE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])

/-- The certified sieve covering exactly `n`. Returns the declarations holding its bitset and its
`IsSieve` statement, with that bitset's value. -/
private def sieveFor (n : Nat) : MetaM (Name × Name × Nat) := do
  let entry ← match (← PrimeCert.Sieve.sieveCaches).find? (·.hi == n) with
    | some c => pure c
    | none => throwError "run_lam: no sieve at {n}, put `run_sieve {n}` above this command"
  let T := (n - 1) / 3
  return (entry.litName, entry.isSieveName,
    PrimeCert.Sieve.sieveLoop T (PrimeCert.Sieve.initK T) 1 ((Nat.sqrt n + 1 - 1) / 3))

/-- What the checks against the sieve leave for the assembly. -/
structure PowerData where
  /-- The packed prime powers. -/
  qs : Nat
  /-- Entries in the first block, the primes from 5 upward. -/
  np : Nat
  /-- Final state of the bit checks: the top sieve position and the flag. -/
  st : Nat
  /-- Final state of the power collection: its count, its running power and its entries. -/
  hpSt : Nat
  /-- Blocks of 32 sieve positions counted. -/
  chunks : Nat
  /-- Entries the collection may append at one sieve position. -/
  e : Nat
  /-- Sieve positions the collection walks. -/
  fuel : Nat
  /-- Declaration holding the sieve bitset. -/
  litName : Name
  /-- Declaration holding `IsSieve` for that bitset. -/
  isSieveName : Name

/-- Check the packed primes against the sieve and collect the remaining prime powers from it, both
in kernel-checked batches. Returns the packed prime powers, in the order the checks certify, with
what the assembly reads off the checks. -/
private def emitPowerChecks (n len : Nat) : MetaM PowerData := do
  let (litName, isSieveName, lit) ← sieveFor n
  let litE := mkConst litName
  let w := Nat.log2 n + 1
  let e := Nat.log2 n + 1
  let primes := sievedPrimes n
  let others := collectedPowers n
  let qs := packEntries (primes ++ others) w
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mE := mkRawNatLit n
  let eE := mkRawNatLit e
  -- every packed prime sits at a set sieve bit, at a rising position
  let mkBit := fun stE start len =>
    mkAppN (mkConst ``bitCheckLoopK) #[qsE, wE, litE, stE, mkRawNatLit start, mkRawNatLit len]
  let (st, bitProof) ← emitLoopChain "bit" primes.size len 1 0 mkBit
    (fun st start step => bitCheckLoop qs w lit st start step)
    ``bitCheckLoopK_chain
    (fun stE nextE start step rest =>
      #[qsE, wE, litE, stE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.bitData
    (mkNatEqual (mkBit (mkRawNatLit 1) 0 primes.size) (mkRawNatLit st)) bitProof
  if st % 2 != 1 then throwError "run_lam: a packed prime failed its sieve test"
  -- the sieve holds as many set bits as there are packed primes, so none is missing
  let chunks := (n - 1) / 3 / 32 + 1
  let mkPopc := fun accE start len =>
    mkAppN (mkConst ``popcLoopK) #[litE, accE, mkRawNatLit start, mkRawNatLit len]
  let (cnt, cntProof) ← emitLoopChain "popc" chunks len 0 0 mkPopc
    (fun acc start step => popcLoop lit acc start step)
    ``popcLoopK_chain
    (fun accE nextE start step rest =>
      #[litE, accE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.popcData
    (mkNatEqual (mkPopc (mkRawNatLit 0) 0 chunks) (mkRawNatLit cnt)) cntProof
  if cnt != primes.size then
    throwError "run_lam: {cnt} primes in the sieve against {primes.size} packed"
  -- 2, 3 and the powers of exponent at least two, collected from the sieve
  let hpFuel := (Nat.sqrt n - 1) / 3
  let mkPow := fun (q seed : Nat) (stE : Expr) =>
    mkAppN (mkConst ``powLoopK) #[mE, wE, mkRawNatLit q, mkRawNatLit seed, stE, eE]
  let seedE := mkPow 3 1 (mkPow 2 1 (mkRawNatLit 0))
  let seed := powLoop n w 3 1 (powLoop n w 2 1 0 e) e
  addThm `PrimeCert.Polya.hpSeed (mkBeqTrue seedE (mkRawNatLit seed)) Lean.reflBoolTrue
  let mkHp := fun stE start len =>
    mkAppN (mkConst ``hpLoopK) #[litE, mE, wE, eE, stE, mkRawNatLit start, mkRawNatLit len]
  let (hpSt, hpProof) ← emitLoopChain "hp" hpFuel len seed 1 mkHp
    (fun st start step => hpLoop lit n w e st start step)
    ``hpLoopK_chain
    (fun stE nextE start step rest =>
      #[litE, mE, wE, eE, stE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  let full := mkAppN (mkConst ``hpLoopK_entry)
    #[litE, mE, wE, eE, seedE, mkRawNatLit seed, mkRawNatLit 1, mkRawNatLit hpFuel,
      mkRawNatLit hpSt, mkConst `PrimeCert.Polya.hpSeed, hpProof]
  addThm `PrimeCert.Polya.hpData (mkNatEqual (mkHp seedE 1 hpFuel) (mkRawNatLit hpSt)) full
  if hpSt >>> 128 != packEntries others w || hpSt &&& ((1 <<< 64) - 1) != others.size then
    throwError "run_lam: the collected powers differ from the packed ones"
  return { qs, np := primes.size, st, hpSt, chunks, e, fuel := hpFuel, litName, isSieveName }

private def mkOnesLoopK (lamE wE tblE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``onesLoopK) #[lamE, wE, tblE, mkRawNatLit start, mkRawNatLit len]

/-- Returns the running counts `tbl` and a proof of `onesLoopK lam w 0 0 fuel = tbl`, split into
batches of at most `len` steps. -/
private def emitOnesChain (n fuel len w lam : Nat) : MetaM (Nat × Expr) := do
  let lamE := mkRawNatLit lam
  let wE := mkRawNatLit w
  emitLoopChain s!"ones_{n}" fuel len 0 0 (mkOnesLoopK lamE wE)
    (fun tbl start step => onesLoop lam w tbl start step)
    ``onesLoopK_chain
    (fun tblE nextE start step rest =>
      #[lamE, wE, tblE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])

/-- What the parity table and the running counts leave for the assembly. -/
structure TableData where
  /-- The parity table. -/
  lam : Nat
  /-- The running counts of its set bits. -/
  ones : Nat
  /-- Width of a packed prime power and of a count. -/
  w : Nat
  /-- Doubling rounds in a stride mask. -/
  rounds : Nat
  /-- Entries in the packed prime powers. -/
  cnt : Nat
  /-- Blocks of 32 positions the counts cover. -/
  chunks : Nat
  /-- What the checks against the sieve left. -/
  powers : PowerData

/-- Build the parity table and the running counts for numbers up to `n`, in batches of `len` steps,
each kernel-checked separately. The tables and their equations are held by generated declarations;
their literals and the arguments the assembly needs are returned. -/
def buildTables (n len : Nat) : MetaM TableData := do
  let qsName := `PrimeCert.Polya.lamQs
  let litName := `PrimeCert.Polya.lamLit
  let dataName := `PrimeCert.Polya.lamData
  if (← getEnv).contains litName then
    throwError "run_lam: a parity table already exists"
  let w := Nat.log2 n + 1
  let powers ← emitPowerChecks n len
  let qs := powers.qs
  let fuel := (sievedPrimes n).size + (collectedPowers n).size
  addDecl <| Declaration.defnDecl
    { name := qsName, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit qs, hints := .regular 0, safety := .safe }
  -- doubling rounds needed for a stride mask to cover the table: `2 ^ rounds > n`
  let rounds := Nat.log2 n + 1
  let (lit, proof) ← emitChain n n fuel len w rounds qs
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit lit, hints := .regular 0, safety := .safe }
  -- `proof` ends at a zero-step loop on the final table, which is definitionally both the literal
  -- and, on the other side, `lamK qs w n rounds fuel`
  let lhs := mkAppN (mkConst ``lamK)
    #[mkRawNatLit qs, mkRawNatLit w, mkRawNatLit n, mkRawNatLit rounds, mkRawNatLit fuel]
  addThm dataName (mkNatEqual lhs (mkConst litName)) proof
  -- the running counts of set bits, one entry per 32 positions
  let chunks := n / 32 + 1
  let (ones, onesProof) ← emitOnesChain n chunks len w lit
  addDecl <| Declaration.defnDecl
    { name := `PrimeCert.Polya.onesLit, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit ones, hints := .regular 0, safety := .safe }
  let onesLhs := mkAppN (mkConst ``onesK)
    #[mkRawNatLit lit, mkRawNatLit w, mkRawNatLit chunks]
  addThm `PrimeCert.Polya.onesData
    (mkNatEqual onesLhs (mkConst `PrimeCert.Polya.onesLit)) onesProof
  return { lam := lit, ones, w, rounds, cnt := fuel, chunks, powers }

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

/-- Width of a entry of the certificate, and the offset that keeps each entry positive. -/
def bigWidth : Nat := 21
def bigOffset : Nat := 1 <<< 20

private def mkBlockLoopK (xE vE rE lowE hiE stE : Expr) (len : Nat) : Expr :=
  mkAppN (mkConst ``blockLoopK)
    #[xE, vE, rE, lowE, hiE, mkRawNatLit bigWidth, mkRawNatLit bigOffset, stE, mkRawNatLit len]

private def mkLowLoopK (lamE onesE wcE tblE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``lowLoopK)
    #[lamE, onesE, wcE, mkRawNatLit bigOffset, mkRawNatLit bigWidth, tblE, mkRawNatLit start,
      mkRawNatLit len]

private def mkHiLoopK (xE lamE onesE wcE tblE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``hiLoopK)
    #[xE, lamE, onesE, wcE, mkRawNatLit bigOffset, mkRawNatLit bigWidth, tblE,
      mkRawNatLit start, mkRawNatLit len]

/-- Builds the table of `L q + bigOffset` for `q = 0 … stop`, in batches of `len`, each
kernel-checked, and returns it with a proof. -/
private def emitLowChain (lam ones wc stop len : Nat) : MetaM (Nat × Expr) := do
  let lamE := mkRawNatLit lam
  let onesE := mkRawNatLit ones
  let wcE := mkRawNatLit wc
  emitLoopChain "low" (stop + 1) len 0 0 (mkLowLoopK lamE onesE wcE)
    (fun tbl start step => lowLoop lam ones wc bigOffset bigWidth tbl start step)
    ``lowLoopK_chain
    (fun tblE nextE start step rest =>
      #[lamE, onesE, wcE, mkRawNatLit bigOffset, mkRawNatLit bigWidth, tblE, nextE,
        mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])

/-- Builds the table of `L (x / m) + bigOffset` for `m = from … stop`, in batches of `len`, each
kernel-checked, and returns it with a proof. -/
private def emitHiChain (x lam ones wc from_ stop len : Nat) : MetaM (Nat × Expr) := do
  let xE := mkRawNatLit x
  let lamE := mkRawNatLit lam
  let onesE := mkRawNatLit ones
  let wcE := mkRawNatLit wc
  emitLoopChain "hi" (stop + 1 - from_) len 0 from_ (mkHiLoopK xE lamE onesE wcE)
    (fun tbl start step => hiLoop x lam ones wc bigOffset bigWidth tbl start step)
    ``hiLoopK_chain
    (fun tblE nextE start step rest =>
      #[xE, lamE, onesE, wcE, mkRawNatLit bigOffset, mkRawNatLit bigWidth, tblE, nextE,
        mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])

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
private def emitBlockChain (x v rootx low hi fuel len : Nat) : MetaM (Nat × Expr) := do
  let xE := mkRawNatLit x
  let vE := mkRawNatLit v
  let rE := mkRawNatLit rootx
  let lowE := mkRawNatLit low
  let hiE := mkRawNatLit hi
  -- the loop starts at index 2 with both halves of the sum empty, and each block reads its index
  -- out of the state, so the chain's running start is idle here
  emitLoopChain s!"block_{v}" fuel len 2 0
    (fun stE _ step => mkBlockLoopK xE vE rE lowE hiE stE step)
    (fun st _ step => blockLoop x v rootx low hi bigWidth bigOffset st step)
    ``blockLoopK_chain
    (fun stE nextE _ step rest =>
      #[xE, vE, rE, lowE, hiE, mkRawNatLit bigWidth, mkRawNatLit bigOffset, stE, nextE,
        mkRawNatLit step, mkRawNatLit rest])

/-! ### The assembly

Each of the three lemmas below takes its numeric side conditions as one decidable predicate over
the emitted literals, so one kernel-checked theorem carries them all. -/

/-- Emit the checks of the setup and the two table invariants they give. Returns the declarations
holding `IsLowTable` and `IsHiTable`. -/
private def emitTables (x cutoff rootx top low hi : Nat) (d : TableData) (p : PowerData) :
    MetaM (Name × Name) := do
  let nats := (#[x, cutoff, rootx, top, d.w, d.rounds, d.w, d.chunks, bigOffset, bigWidth, p.qs,
    p.np, d.cnt, p.chunks, p.e, p.fuel, p.st, p.hpSt]).map mkRawNatLit
  let okName := `PrimeCert.Polya.setupCheck
  addThm okName (mkBoolTrue (mkAppN (mkConst ``setupOK) nats)) Lean.reflBoolTrue
  let proof := mkAppN (mkConst ``tables_of_data)
    (nats ++ #[mkConst p.litName, mkRawNatLit d.lam, mkRawNatLit d.ones, mkRawNatLit low,
      mkRawNatLit hi, mkConst p.isSieveName, mkConst `PrimeCert.Polya.bitData,
      mkConst `PrimeCert.Polya.popcData, mkConst `PrimeCert.Polya.hpData,
      mkConst `PrimeCert.Polya.lamData, mkConst `PrimeCert.Polya.onesData,
      mkConst `PrimeCert.Polya.lowData, mkConst `PrimeCert.Polya.hiData, mkConst okName])
  let bothName := `PrimeCert.Polya.tablesData
  let ty ← inferType proof
  addThm bothName ty proof
  let parts := ty.getAppArgs
  let lowName := `PrimeCert.Polya.lowTable
  let hiName := Name.mkSimple s!"hi_table_{top + 1}"
  addThm lowName parts[0]! (mkAppN (mkConst ``And.left) #[parts[0]!, parts[1]!, mkConst bothName])
  addThm hiName parts[1]! (mkAppN (mkConst ``And.right) #[parts[0]!, parts[1]!, mkConst bothName])
  return (lowName, hiName)

/-- Emit the checks of one index and the high table extended to it. Returns the declaration holding
the extended table. -/
private def emitStep (x rootx low hi hiNext j v s A B S val fuel : Nat)
    (lowName hiName blockName : Name) : MetaM Name := do
  let okName := Name.mkSimple s!"step_ok_{j}"
  addThm okName
    (mkBoolTrue (mkAppN (mkConst ``stepOK)
      ((#[x, rootx, bigOffset, bigWidth, j, v, s, A, B, S, val, hi, hiNext]).map mkRawNatLit)))
    Lean.reflBoolTrue
  let proof := mkAppN (mkConst ``isHiTable_step)
    (((#[x, rootx, bigOffset, bigWidth, low, hi, hiNext, j, v, s, A, B, S, val,
        fuel]).map mkRawNatLit) ++
      #[mkConst lowName, mkConst hiName, mkConst blockName, mkConst okName])
  let out := Name.mkSimple s!"hi_table_{j}"
  addThm out (← inferType proof) proof
  return out

/-- Emit the checks of the last index and the value of `L x` they give. -/
private def emitFinal (x rootx low hi s A B S p q fuel : Nat)
    (lowName hiName blockName : Name) : MetaM Unit := do
  let okName := `PrimeCert.Polya.finalCheck
  addThm okName
    (mkBoolTrue (mkAppN (mkConst ``finalOK)
      ((#[x, rootx, bigOffset, bigWidth, s, A, B, S, p, q]).map mkRawNatLit)))
    Lean.reflBoolTrue
  let proof := mkAppN (mkConst ``L_eq_of_final)
    (((#[x, rootx, bigOffset, bigWidth, low, hi, s, A, B, S, p, q, fuel]).map mkRawNatLit) ++
      #[mkConst lowName, mkConst hiName, mkConst blockName, mkConst okName])
  addThm `PrimeCert.Polya.polyaValue (← inferType proof) proof

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
the recurrence at each larger argument `x / j`, taken in increasing order. The run emits
`polyaValue : L x = p - q`. -/
def runPolya (x cutoff : Nat) (K? : Option Nat := none) : MetaM Unit := do
  let len := match K? with
    | some K => Nat.max 1 K
    | none => defaultBatchLen
  let d ← buildTables cutoff len
  let lam := d.lam
  let ones := d.ones
  let w := d.w
  let top := x / cutoff
  if top == 0 then throwError "run_polya: the cutoff must be below the target"
  let rootx := Nat.sqrt x
  -- `L q` for every `q ≤ √x`, and `L (x / m)` for the `m ≤ √x` whose quotient is below the cutoff:
  -- together these cover every argument the recurrence reads other than the ones it computes itself
  let (low, lowProof) ← emitLowChain lam ones w rootx len
  addDecl <| Declaration.defnDecl
    { name := `PrimeCert.Polya.lowLit, levelParams := [], type := mkConst ``Nat,
      value := mkRawNatLit low, hints := .regular 0, safety := .safe }
  addThm `PrimeCert.Polya.lowData
    (mkNatEqual (mkLowLoopK (mkRawNatLit lam) (mkRawNatLit ones) (mkRawNatLit w)
      (mkRawNatLit 0) 0 (rootx + 1)) (mkConst `PrimeCert.Polya.lowLit)) lowProof
  let (hi0, hiProof) ← emitHiChain x lam ones w (top + 1) rootx len
  addThm `PrimeCert.Polya.hiData
    (mkNatEqual (mkHiLoopK (mkRawNatLit x) (mkRawNatLit lam) (mkRawNatLit ones) (mkRawNatLit w)
      (mkRawNatLit 0) (top + 1) (rootx - top)) (mkRawNatLit hi0)) hiProof
  let (lowName, hiName0) ← emitTables x cutoff rootx top low hi0 d d.powers
  let mut hiName := hiName0
  let mut hi := hi0
  let mut last : Int := 0
  for jj in [0:top] do
    let j := top - jj
    let v := x / j
    let fuel := blockCount v
    let (st, proof) ← emitBlockChain x v rootx low hi fuel len
    let dataName := Name.mkSimple s!"block_data_{v}"
    addThm dataName
      (mkNatEqual (mkBlockLoopK (mkRawNatLit x) (mkRawNatLit v) (mkRawNatLit rootx)
        (mkRawNatLit low) (mkRawNatLit hi) (mkRawNatLit 2) fuel) (mkRawNatLit st)) proof
    -- L v is the whole part of the square root of v, minus the two halves of the sum
    let s := Nat.sqrt v
    let A := stEntry st 1
    let B := stEntry st 2
    last := (s : Int) - A + B
    if j == 1 then
      let p := if last ≥ 0 then last.toNat else 0
      let q := if last ≥ 0 then 0 else (-last).toNat
      emitFinal x rootx low hi s A B st p q fuel lowName hiName dataName
    else
      let val := (last + bigOffset).toNat
      let next := hi ||| (val <<< (bigWidth * j))
      hiName ← emitStep x rootx low hi next j v s A B st val fuel lowName hiName dataName
      hi := next
  logInfo m!"L({x}) = {last}"

/-- Command wrapper for `runPolya`: `run_polya x` computes the running total at `x`, `run_polya x c`
sets the cutoff, and `run_polya x c K` also sets the batch length. -/
elab "run_polya" xStx:num cStx:(num)? kStx:(num)? : command => do
  let x := xStx.getNat
  liftTermElabM <| runPolya x ((cStx.map (·.getNat)).getD (defaultCutoff x)) (kStx.map (·.getNat))

end PrimeCert.Polya
