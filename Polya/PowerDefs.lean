/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Defs
public import PrimeCert.Sieve

/-!
# The loops checking the packed prime powers against the sieve

Kernel definitions for the three loops the run drives, each with its peel, additivity and chain
lemmas and a compiled twin: `bitCheckLoopK` tests a entry's residue, its rising sieve index and its
sieve bit, `popcLoopK` adds up the sieve's set bits, and `hpLoopK` collects the powers with exponent
at least two through `powLoopK`. What surviving these forces is `Polya.Correct.TableSpec`.
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (num numK)

/-! ### Collecting the powers with exponent at least two

Every prime power `q ≤ M` with exponent at least two has base at most `√M`, so the bases come from
the sieve positions below `(√M - 1) / 3`. The state holds a count of collected values in its low 64
bits, the base's running power in the next 64, and the values in `w`-bit entries above bit 128. -/

/-- Multiply the running power by `q` and, while the result is at most `M`, append it. -/
@[expose] public noncomputable def powStepK (M w q st : Nat) : Nat :=
  let mask := ((nat_lit 1).shiftLeft (nat_lit 64)).sub (nat_lit 1)
  let cnt := st.land mask
  let pow := (st.shiftRight (nat_lit 64)).land mask
  let next := pow.mul q
  (next.ble M).rec st
    (((st.add (nat_lit 1)).add ((next.sub pow).shiftLeft (nat_lit 64))).add
      (next.shiftLeft ((nat_lit 128).add (w.mul cnt))))

/-- Perform `fuel` power steps for the base `q`, starting from the running power `seed`. -/
@[expose] public noncomputable def powLoopK (M w q seed st fuel : Nat) : Nat :=
  fuel.rec
    ((st.sub (((st.shiftRight (nat_lit 64)).land
      (((nat_lit 1).shiftLeft (nat_lit 64)).sub (nat_lit 1))).shiftLeft (nat_lit 64))).add
      (seed.shiftLeft (nat_lit 64)))
    fun _ s => powStepK M w q s

/-- Perform `fuel` steps from sieve position `start`, collecting the powers of each position whose
sieve bit is set. -/
@[expose] public noncomputable def hpLoopK (lit M w e st start fuel : Nat) : Nat :=
  fuel.rec st fun i s =>
    (Nat.ble (nat_lit 1) ((lit.shiftRight (start.add i)).land (nat_lit 1))).rec s
      (powLoopK M w (numK (start.add i)) (numK (start.add i)) s e)

/-! ### Loop recurrences -/

/-- Peel the top base, in the exact form the def uses. -/
public theorem hpLoopK_succ (lit M w e st start fuel : Nat) :
    hpLoopK lit M w e st start (fuel + 1)
      = (Nat.ble 1 ((lit.shiftRight (start + fuel)).land 1)).rec
          (hpLoopK lit M w e st start fuel)
          (powLoopK M w (numK (start + fuel)) (numK (start + fuel))
            (hpLoopK lit M w e st start fuel) e) := rfl

/-! ### Fuel additivity and chaining -/

/-- Replace the starting state by a kernel-checked equal literal, the way the chain is entered from
the state holding the powers of 2 and 3. -/
public theorem hpLoopK_congr (lit M w e s s' start fuel : Nat) (h : s.beq s') :
    hpLoopK lit M w e s start fuel = hpLoopK lit M w e s' start fuel := by
  rw [Nat.eq_of_beq_eq_true h]

/-- The chain read from the seed state: its value from the equal literal `s'` is its value from
`s`. -/
public theorem hpLoopK_entry (lit M w e s s' start fuel v : Nat) (h : s.beq s')
    (hv : hpLoopK lit M w e s' start fuel = v) : hpLoopK lit M w e s start fuel = v := by
  rw [hpLoopK_congr lit M w e s s' start fuel h, hv]

/-- Fuel additivity for the collection of higher powers. -/
public theorem hpLoopK_add (lit M w e st start a b : Nat) :
    hpLoopK lit M w e st start (a + b)
      = hpLoopK lit M w e (hpLoopK lit M w e st start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [hpLoopK_succ]

/-- One chain step for the collection of higher powers. -/
public theorem hpLoopK_chain (L lit M w e st st' start len rest : Nat)
    (hP : L = hpLoopK lit M w e st start (len.add rest))
    (h : (hpLoopK lit M w e st start len).beq st') :
    L = hpLoopK lit M w e st' (start.add len) rest := by
  grind [hpLoopK_add, Nat.beq_eq]

/-! ### Compiled twins

Executable copies used to compute the batch literals; a twin disagreeing with its kernel definition
would produce a batch equation that fails its kernel check. -/

public def powStep (M w q st : Nat) : Nat :=
  let mask := (1 <<< 64) - 1
  let cnt := st &&& mask
  let pow := (st >>> 64) &&& mask
  let next := pow * q
  if next ≤ M then st + 1 + ((next - pow) <<< 64) + (next <<< (128 + w * cnt)) else st

public def powLoop (M w q seed st fuel : Nat) : Nat := Id.run do
  let mask := (1 <<< 64) - 1
  let mut s := st - (((st >>> 64) &&& mask) <<< 64) + (seed <<< 64)
  for _ in [0:fuel] do
    s := powStep M w q s
  return s

public def hpLoop (lit M w e st start fuel : Nat) : Nat := Id.run do
  let mut s := st
  for i in [0:fuel] do
    let t := start + i
    if (lit >>> t) &&& 1 ≠ 0 then
      s := powLoop M w (num t) (num t) s e
  return s

end PrimeCert.Polya
