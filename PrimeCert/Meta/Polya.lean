/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Lean
import PrimeCert.Polya
import PrimeCert.Polya.PrimePowers
import PrimeCert.Meta.Sieve

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

/-- Pack `qs` into one natural number as `w`-bit fields, lowest first. -/
def packFields (qs : Array Nat) (w : Nat) : Nat := Id.run do
  let mut out := 0
  for h : i in [0:qs.size] do
    out := out ||| (qs[i] <<< (w * i))
  return out

/-- Returns a table `lam` and a proof of `lamLoopK qs w M 0 0 fuel = lam`, split into batches of at
most `len` steps; `n` only distinguishes the names of the emitted batch lemmas. -/
private def emitChain (n M fuel len w rounds qs : Nat) : MetaM (Nat × Expr) := do
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mE := mkRawNatLit M
  let rE := mkRawNatLit rounds
  -- the fixed left-hand side of the chain: the full loop on the empty table
  let lhsLoop := mkLamLoopK qsE wE mE rE (mkRawNatLit 0) 0 fuel
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
    let next := lamLoop qs w M rounds lam start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"lam_step_{n}_{i}"
    addThm stepName (mkBeqTrue (mkLamLoopK qsE wE mE rE lamE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``lamLoopK_chain)
      #[lhsLoop, qsE, wE, mE, rE, lamE, nextE, mkRawNatLit start, mkRawNatLit step,
        mkRawNatLit rest, proof, mkConst stepName]
    lam := next
    lamE := nextE
    start := start + step
    remaining := rest
  -- the chain ends at a zero-step loop on `lam`, which is definitionally `lam` itself
  return (lam, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop lamE))

/-- Emit `fuel` steps of one loop in batches of `len`, each batch kernel-checked. `mk st start len`
builds the loop's application, `run st start len` is its compiled twin, and `chain` with `chainArgs`
glues consecutive batches. Returns the final state and the glued proof. -/
private def emitLoopChain (tag : String) (fuel len st0 start0 : Nat)
    (mk : Expr → Nat → Nat → Expr) (run : Nat → Nat → Nat → Nat)
    (chain : Name) (chainArgs : Expr → Expr → Nat → Nat → Nat → Array Expr) :
    MetaM (Nat × Expr) := do
  let lhsLoop := mk (mkRawNatLit st0) start0 fuel
  let mut st := st0
  let mut stE := mkRawNatLit st0
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
  return (st, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop stE))

/-- The certified sieve covering exactly `n`, building one when the registry holds none. Returns the
declaration holding its bitset and that bitset's value. -/
private def sieveFor (n len : Nat) : MetaM (Name × Nat) := do
  let entry ← match (← PrimeCert.Sieve.sieveCaches).find? (·.hi == n) with
    | some c => pure c
    | none => do
        PrimeCert.Sieve.runSieve n len
        match (← PrimeCert.Sieve.sieveCaches).find? (·.hi == n) with
        | some c => pure c
        | none => throwError "run_lam: no sieve covering {n}"
  let T := (n - 1) / 3
  return (entry.litName,
    PrimeCert.Sieve.sieveLoop T (PrimeCert.Sieve.initK T) 1 ((Nat.sqrt n + 1 - 1) / 3))

/-- Check the packed primes against the sieve and collect the remaining prime powers from it, both
in kernel-checked batches. Returns the packed prime powers, in the order the checks certify. -/
private def emitPowerChecks (n len : Nat) : MetaM Nat := do
  let (litName, lit) ← sieveFor n len
  let litE := mkConst litName
  let w := Nat.log2 n + 1
  let e := Nat.log2 n + 1
  let primes := sievedPrimes n
  let others := collectedPowers n
  let qs := packFields (primes ++ others) w
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
  let entry := mkAppN (mkConst ``hpLoopK_congr)
    #[litE, mE, wE, eE, seedE, mkRawNatLit seed, mkRawNatLit 1, mkRawNatLit hpFuel,
      mkConst `PrimeCert.Polya.hpSeed]
  let full ← mkExpectedTypeHint
    (mkAppN (mkConst ``Eq.trans [Level.succ Level.zero])
      #[mkConst ``Nat, mkHp seedE 1 hpFuel, mkHp (mkRawNatLit seed) 1 hpFuel, mkRawNatLit hpSt,
        entry, hpProof])
    (mkNatEqual (mkHp seedE 1 hpFuel) (mkRawNatLit hpSt))
  addThm `PrimeCert.Polya.hpData (mkNatEqual (mkHp seedE 1 hpFuel) (mkRawNatLit hpSt)) full
  if hpSt >>> 128 != packFields others w || hpSt &&& ((1 <<< 64) - 1) != others.size then
    throwError "run_lam: the collected powers differ from the packed ones"
  return qs

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
def buildTables (n len : Nat) (check : Bool := true) : MetaM (Nat × Nat × Nat) := do
  let qsName := `PrimeCert.Polya.lamQs
  let litName := `PrimeCert.Polya.lamLit
  let dataName := `PrimeCert.Polya.lamData
  if (← getEnv).contains litName then
    throwError "run_lam: a parity table already exists"
  let w := Nat.log2 n + 1
  let qs ← if check then emitPowerChecks n len
    else pure (packFields (sievedPrimes n ++ collectedPowers n) w)
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
  let fuel := stop + 1
  let lhsLoop := mkLowLoopK lamE onesE wcE (mkRawNatLit 0) 0 fuel
  let mut tbl := 0
  let mut tblE := mkRawNatLit 0
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut start := 0
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := lowLoop lam ones wc bigOffset bigWidth tbl start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"low_step_{i}"
    addThm stepName (mkBeqTrue (mkLowLoopK lamE onesE wcE tblE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``lowLoopK_chain)
      #[lhsLoop, lamE, onesE, wcE, mkRawNatLit bigOffset, mkRawNatLit bigWidth, tblE, nextE,
        mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest, proof, mkConst stepName]
    tbl := next
    tblE := nextE
    start := start + step
    remaining := rest
  return (tbl, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop tblE))

/-- Builds the table of `L (x / m) + bigOffset` for `m = from … stop`, in batches of `len`, each
kernel-checked, and returns it with a proof. -/
private def emitHiChain (x lam ones wc from_ stop len : Nat) : MetaM (Nat × Expr) := do
  let xE := mkRawNatLit x
  let lamE := mkRawNatLit lam
  let onesE := mkRawNatLit ones
  let wcE := mkRawNatLit wc
  let fuel := stop + 1 - from_
  let lhsLoop := mkHiLoopK xE lamE onesE wcE (mkRawNatLit 0) from_ fuel
  let mut tbl := 0
  let mut tblE := mkRawNatLit 0
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut start := from_
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := hiLoop x lam ones wc bigOffset bigWidth tbl start step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"hi_step_{i}"
    addThm stepName (mkBeqTrue (mkHiLoopK xE lamE onesE wcE tblE start step) nextE)
      Lean.reflBoolTrue
    proof := mkAppN (mkConst ``hiLoopK_chain)
      #[lhsLoop, xE, lamE, onesE, wcE, mkRawNatLit bigOffset, mkRawNatLit bigWidth, tblE, nextE,
        mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest, proof, mkConst stepName]
    tbl := next
    tblE := nextE
    start := start + step
    remaining := rest
  return (tbl, ← mkExpectedTypeHint proof (mkNatEqual lhsLoop tblE))

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
  -- the loop starts at index 2 with both halves of the sum empty
  let lhsLoop := mkBlockLoopK xE vE rE lowE hiE (mkRawNatLit 2) fuel
  let mut st := 2
  let mut stE := mkRawNatLit 2
  let mut proof := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) lhsLoop
  let mut remaining := fuel
  for i in [0:(fuel + len - 1) / len] do
    let step := Nat.min len remaining
    let rest := remaining - step
    let next := blockLoop x v rootx low hi bigWidth bigOffset st step
    let nextE := mkRawNatLit next
    let stepName := Name.mkSimple s!"block_step_{v}_{i}"
    addThm stepName (mkBeqTrue (mkBlockLoopK xE vE rE lowE hiE stE step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst ``blockLoopK_chain)
      #[lhsLoop, xE, vE, rE, lowE, hiE, mkRawNatLit bigWidth, mkRawNatLit bigOffset, stE, nextE,
        mkRawNatLit step, mkRawNatLit rest, proof, mkConst stepName]
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
def runPolya (x cutoff : Nat) (K? : Option Nat := none) (check : Bool := true) : MetaM Unit := do
  let len := match K? with
    | some K => Nat.max 1 K
    | none => defaultBatchLen
  let (lam, ones, w) ← buildTables cutoff len check
  let top := x / cutoff
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
    last := (Nat.sqrt v : Int) - (stField st 1 : Int) + (stField st 2 : Int)
    hi := hi ||| ((last + bigOffset).toNat <<< (bigWidth * j))
  logInfo m!"L({x}) = {last}"

/-- Command wrapper for `runPolya`: `run_polya x` computes the running total at `x`, `run_polya x c`
sets the cutoff, and `run_polya x c K` also sets the batch length. -/
elab "run_polya" xStx:num cStx:(num)? kStx:(num)? : command => do
  let x := xStx.getNat
  liftTermElabM <| runPolya x ((cStx.map (·.getNat)).getD (defaultCutoff x)) (kStx.map (·.getNat))

/-- As `run_polya`, taking the prime powers as given, for measuring what the checks against the
sieve cost. -/
elab "run_polya_unchecked" xStx:num cStx:(num)? kStx:(num)? : command => do
  let x := xStx.getNat
  liftTermElabM <|
    runPolya x ((cStx.map (·.getNat)).getD (defaultCutoff x)) (kStx.map (·.getNat)) false

end PrimeCert.Polya
