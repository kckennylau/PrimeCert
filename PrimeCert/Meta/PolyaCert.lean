/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.PolyaCert
import PrimeCert.Meta.Polya
import PrimeCert.Meta.Sieve

/-! # Commands driving the prototype certification loops

One command per loop in `PrimeCert.PolyaCert`, each emitting its batch equations for the kernel to
check and reporting what the loop computed. The sieve bitset enters as a literal computed here, so
each command measures its own loop alone.
-/

namespace PrimeCert.Polya

open Lean Elab Command Meta PrimeCert.Sieve

/-- The statement `Nat.beq a b = true`. -/
private def mkBeqT (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

/-- The statement `a = b` for naturals. -/
private def mkNatEq (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) a b

private def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Steps per emitted theorem, matching the parity table's own default. -/
def certBatchLen : Nat := 256

/-- The sieve bitset for numbers up to `M`, computed with the compiled twins: bit `t` is set when
`num t` is prime. -/
def sieveBits (M : Nat) : Nat :=
  let T := (M - 1) / 3
  sieveLoop T (initK T) 1 ((Nat.sqrt M + 1 - 1) / 3)

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

/-- The prime powers `q ≤ M`, split into the primes from 5 upward and the rest, which is 2, 3 and
the powers whose exponent is at least 2. -/
def primeBlocks (M : Nat) : Array Nat × Array Nat := Id.run do
  let flags := primeFlags M
  let mut hi : Array Nat := #[]
  let mut lo : Array Nat := #[]
  for q in primePowers M do
    if 5 ≤ q && flags[q]! then hi := hi.push q else lo := lo.push q
  return (hi, lo)

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
    addThm stepName (mkBeqT (mk stE start step) nextE) Lean.reflBoolTrue
    proof := mkAppN (mkConst chain)
      (#[lhsLoop] ++ chainArgs stE nextE start step rest ++ #[proof, mkConst stepName])
    st := next
    stE := nextE
    start := start + step
    remaining := rest
  return (st, ← mkExpectedTypeHint proof (mkNatEq lhsLoop stE))

/-- Check the packed primes against the sieve, testing each one's bit and the emptiness of the sieve
between consecutive ones. -/
def runCertGap (M len : Nat) : MetaM Unit := do
  let lit := sieveBits M
  let (primes, _) := primeBlocks M
  let w := Nat.log2 M + 1
  let qs := packFields primes w
  let litE := mkRawNatLit lit
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mk := fun stE start len =>
    mkAppN (mkConst ``gapCheckLoopK) #[qsE, wE, litE, stE, mkRawNatLit start, mkRawNatLit len]
  let (st, proof) ← emitLoopChain "gap" primes.size len 1 0 mk
    (fun st start step => gapCheckLoop qs w lit st start step)
    ``gapCheckLoopK_chain
    (fun stE nextE start step rest =>
      #[qsE, wE, litE, stE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.gapData
    (mkNatEq (mk (mkRawNatLit 1) 0 primes.size) (mkRawNatLit st)) proof
  let T := (M - 1) / 3
  let tailClear := (lit >>> (st / 2 + 1)) &&& ((1 <<< (T - st / 2)) - 1) == 0
  logInfo m!"gap check at {M}: {primes.size} primes, flag {st % 2}, last index {st / 2}, tail clear {tailClear}"

/-- Check the packed primes against the sieve by testing each one's bit, and count the sieve's set
bits. -/
def runCertCount (M len : Nat) : MetaM Unit := do
  let lit := sieveBits M
  let (primes, _) := primeBlocks M
  let w := Nat.log2 M + 1
  let qs := packFields primes w
  let litE := mkRawNatLit lit
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mkBit := fun stE start len =>
    mkAppN (mkConst ``bitCheckLoopK) #[qsE, wE, litE, stE, mkRawNatLit start, mkRawNatLit len]
  let (st, proof) ← emitLoopChain "bit" primes.size len 1 0 mkBit
    (fun st start step => bitCheckLoop qs w lit st start step)
    ``bitCheckLoopK_chain
    (fun stE nextE start step rest =>
      #[qsE, wE, litE, stE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.bitData
    (mkNatEq (mkBit (mkRawNatLit 1) 0 primes.size) (mkRawNatLit st)) proof
  let chunks := (M - 1) / 3 / 32 + 1
  let mkPopc := fun accE start len =>
    mkAppN (mkConst ``popcLoopK) #[litE, accE, mkRawNatLit start, mkRawNatLit len]
  let (cnt, cntProof) ← emitLoopChain "popc" chunks len 0 0 mkPopc
    (fun acc start step => popcLoop lit acc start step)
    ``popcLoopK_chain
    (fun accE nextE start step rest =>
      #[litE, accE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.popcData (mkNatEq (mkPopc (mkRawNatLit 0) 0 chunks) (mkRawNatLit cnt))
    cntProof
  logInfo m!"count check at {M}: {primes.size} primes, flag {st % 2}, set bits {cnt}, agree {cnt == primes.size}"

/-- Build the parity table for the primes by reading the sieve bits. -/
def runCertLamSieve (M len : Nat) : MetaM Unit := do
  let lit := sieveBits M
  let T := (M - 1) / 3
  let rounds := Nat.log2 M + 1
  let litE := mkRawNatLit lit
  let mE := mkRawNatLit M
  let rE := mkRawNatLit rounds
  let mk := fun lamE start len =>
    mkAppN (mkConst ``lamSieveLoopK) #[litE, mE, rE, lamE, mkRawNatLit start, mkRawNatLit len]
  let (tbl, proof) ← emitLoopChain "lamsieve" T len 0 1 mk
    (fun lam start step => lamSieveLoop lit M rounds lam start step)
    ``lamSieveLoopK_chain
    (fun lamE nextE start step rest =>
      #[litE, mE, rE, lamE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.lamSieveData (mkNatEq (mk (mkRawNatLit 0) 1 T) (mkRawNatLit tbl)) proof
  let (primes, _) := primeBlocks M
  let w := Nat.log2 M + 1
  let viaFields := lamLoop (packFields primes w) w M rounds 0 0 primes.size
  logInfo m!"table from the sieve at {M}: matches the table from the packed primes {tbl == viaFields}"

/-- Build the parity table by walking every integer and testing its bit in a number holding one bit
per integer, set at the prime powers. -/
def runCertLamBits (M len : Nat) : MetaM Unit := do
  let mut bits := 0
  for q in primePowers M do
    bits := bits ||| (1 <<< q)
  let rounds := Nat.log2 M + 1
  let bitsE := mkRawNatLit bits
  let mE := mkRawNatLit M
  let rE := mkRawNatLit rounds
  let mk := fun lamE start len =>
    mkAppN (mkConst ``lamBitsLoopK) #[bitsE, mE, rE, lamE, mkRawNatLit start, mkRawNatLit len]
  let (tbl, proof) ← emitLoopChain "lambits" (M - 1) len 0 2 mk
    (fun lam start step => lamBitsLoop bits M rounds lam start step)
    ``lamBitsLoopK_chain
    (fun lamE nextE start step rest =>
      #[bitsE, mE, rE, lamE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.lamBitsData (mkNatEq (mk (mkRawNatLit 0) 2 (M - 1)) (mkRawNatLit tbl))
    proof
  let all := primePowers M
  let w := Nat.log2 M + 1
  let viaFields := lamLoop (packFields all w) w M rounds 0 0 all.size
  logInfo m!"table from one bit per integer at {M}: matches the table from the packed prime powers {tbl == viaFields}"

elab "run_cert_lambits" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertLamBits mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

/-- Build the parity table together with a composite marker, reading neither. -/
def runCertSelf (M len : Nat) : MetaM Unit := do
  let rounds := Nat.log2 M + 1
  let B := M + 2
  let mE := mkRawNatLit M
  let rE := mkRawNatLit rounds
  let bE := mkRawNatLit B
  let mk := fun stE start len =>
    mkAppN (mkConst ``selfLoopK) #[mE, rE, bE, stE, mkRawNatLit start, mkRawNatLit len]
  let (st, proof) ← emitLoopChain "self" (M - 1) len 0 2 mk
    (fun st start step => selfLoop M rounds B st start step)
    ``selfLoopK_chain
    (fun stE nextE start step rest =>
      #[mE, rE, bE, stE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.selfData (mkNatEq (mk (mkRawNatLit 0) 2 (M - 1)) (mkRawNatLit st)) proof
  let lam := st &&& ((1 <<< B) - 1)
  let (primes, _) := primeBlocks M
  let w := Nat.log2 M + 1
  let viaFields := lamLoop (packFields primes w) w M rounds 0 0 primes.size
  -- the joint loop also covers 2 and 3, which the packed primes leave out
  let full := markStride (markStride viaFields 2 M rounds) 3 M rounds
  logInfo m!"marker and table together at {M}: matches the table from every prime {lam == full}"

/-- Build the parity table from the packed prime powers, which is what the table stage does today,
for comparison with the loops above. -/
def runCertBase (M len : Nat) : MetaM Unit := do
  let all := primePowers M
  let w := Nat.log2 M + 1
  let rounds := Nat.log2 M + 1
  let qs := packFields all w
  let qsE := mkRawNatLit qs
  let wE := mkRawNatLit w
  let mE := mkRawNatLit M
  let rE := mkRawNatLit rounds
  let mk := fun lamE start len =>
    mkAppN (mkConst ``lamLoopK) #[qsE, wE, mE, rE, lamE, mkRawNatLit start, mkRawNatLit len]
  let (tbl, proof) ← emitLoopChain "base" all.size len 0 0 mk
    (fun lam start step => lamLoop qs w M rounds lam start step)
    ``lamLoopK_chain
    (fun lamE nextE start step rest =>
      #[qsE, wE, mE, rE, lamE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
  addThm `PrimeCert.Polya.baseData (mkNatEq (mk (mkRawNatLit 0) 0 all.size) (mkRawNatLit tbl)) proof
  logInfo m!"table from the packed prime powers at {M}: {all.size} strides, {tbl % 2} at bit 0"

elab "run_cert_base" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertBase mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

/-- Move each sieve bit to three times its position, turning the sieve's numbering of the integers
coprime to 6 into one bit per integer. -/
def runCertSpread (M len : Nat) : MetaM Unit := do
  let lit := sieveBits M
  let T := (M - 1) / 3
  let rounds := Nat.log2 T + 1
  let mrounds := Nat.log2 (3 * M) + 2
  let width := 3 * T + 8
  let mEven := repMask 1 2 T mrounds
  let mOdd := repMask 2 2 T mrounds
  let wE := mkRawNatLit width
  let rE := mkRawNatLit rounds
  let mrE := mkRawNatLit mrounds
  let mk := fun xE start len =>
    mkAppN (mkConst ``spreadLoopK) #[wE, rE, mrE, xE, mkRawNatLit start, mkRawNatLit len]
  let mut parts : Array Nat := #[]
  for (tag, part) in [("even", lit &&& mEven), ("odd", lit &&& mOdd)] do
    let (out, proof) ← emitLoopChain s!"spread_{tag}" rounds len part 0 mk
      (fun x start step => spreadLoop width rounds mrounds x start step)
      ``spreadLoopK_chain
      (fun xE nextE start step rest =>
        #[wE, rE, mrE, xE, nextE, mkRawNatLit start, mkRawNatLit step, mkRawNatLit rest])
    addThm (Name.mkSimple s!"spread_data_{tag}")
      (mkNatEq (mk (mkRawNatLit part) 0 rounds) (mkRawNatLit out)) proof
    parts := parts.push out
  let primeBits := (1 <<< 2) ||| (1 <<< 3) ||| (parts[0]! <<< 1) ||| (parts[1]! <<< 2)
  let flags := primeFlags M
  let mut want := 0
  for n in [0:M + 1] do
    if flags[n]! then want := want ||| (1 <<< n)
  logInfo m!"spread at {M}: one bit per integer matches the primes {primeBits == want}"

elab "run_cert_spread" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertSpread mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

elab "run_cert_gap" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertGap mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

elab "run_cert_count" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertCount mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

elab "run_cert_lamsieve" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertLamSieve mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

elab "run_cert_self" mStx:num lenStx:(num)? : command =>
  liftTermElabM <| runCertSelf mStx.getNat ((lenStx.map (·.getNat)).getD certBatchLen)

end PrimeCert.Polya
