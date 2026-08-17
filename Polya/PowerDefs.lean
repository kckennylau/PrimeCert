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
lemmas and a compiled twin: `bitCheckLoopK` tests a field's residue, its rising sieve index and its
sieve bit, `popcLoopK` adds up the sieve's set bits, and `hpLoopK` collects the powers with exponent
at least two through `powLoopK`. What surviving these forces is `Polya.Correct.TableSpec`.
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (num numK)

/-! ### Checking the packed primes against the sieve

The state holds the previous field's sieve index above bit 0 and a flag in bit 0, which stays at 1
while every test has passed. The sieve index of a number `q` coprime to 6 is `(q - 1) / 3`,
inverting `numK`. -/

/-- Test field `i`: its value is 1 or 5 modulo 6, its sieve index exceeds the previous one, and its
sieve bit is set. -/
@[expose] public noncomputable def bitCheckStepK (qs w lit st i : Nat) : Nat :=
  let q := fieldK qs w i
  let t := (q.sub (nat_lit 1)).div (nat_lit 3)
  let prev := st.shiftRight (nat_lit 1)
  let ok := st.land (nat_lit 1)
  let okMod :=
    (Nat.beq ((q.mod (nat_lit 6)).mod (nat_lit 4)) (nat_lit 1)).rec (nat_lit 0) (nat_lit 1)
  let okRise := (Nat.ble prev.succ t).rec (nat_lit 0) (nat_lit 1)
  let okSet := (lit.shiftRight t).land (nat_lit 1)
  (t.shiftLeft (nat_lit 1)).add (((ok.mul okMod).mul okRise).mul okSet)

/-- Perform `fuel` field tests, from field `start`. -/
@[expose] public noncomputable def bitCheckLoopK (qs w lit st start fuel : Nat) : Nat :=
  fuel.rec st fun i s => bitCheckStepK qs w lit s (start.add i)

/-- Add to `acc` the set bits of `b` in the 32-position blocks `start, start+1, …`. -/
@[expose] public noncomputable def popcLoopK (b acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    a.add
      (popc32K
        ((b.shiftRight ((start.add i).mul (nat_lit 32))).land
          (((nat_lit 1).shiftLeft (nat_lit 32)).sub (nat_lit 1))))

/-! ### Collecting the powers with exponent at least two

Every prime power `q ≤ M` with exponent at least two has base at most `√M`, so the bases come from
the sieve positions below `(√M - 1) / 3`. The state holds a count of collected values in its low 64
bits, the base's running power in the next 64, and the values in `w`-bit fields above bit 128. -/

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

/-- Peel the top test, in the exact form the def uses. -/
public theorem bitCheckLoopK_succ (qs w lit st start fuel : Nat) :
    bitCheckLoopK qs w lit st start (fuel + 1)
      = bitCheckStepK qs w lit (bitCheckLoopK qs w lit st start fuel) (start + fuel) := rfl

/-- Peel the top block, in the exact form the def uses. -/
public theorem popcLoopK_succ (b acc start fuel : Nat) :
    popcLoopK b acc start (fuel + 1)
      = (popcLoopK b acc start fuel).add
          (popc32K
            ((b.shiftRight ((start + fuel).mul 32)).land ((Nat.shiftLeft 1 32).sub 1))) := rfl

/-- Peel the top base, in the exact form the def uses. -/
public theorem hpLoopK_succ (lit M w e st start fuel : Nat) :
    hpLoopK lit M w e st start (fuel + 1)
      = (Nat.ble 1 ((lit.shiftRight (start + fuel)).land 1)).rec
          (hpLoopK lit M w e st start fuel)
          (powLoopK M w (numK (start + fuel)) (numK (start + fuel))
            (hpLoopK lit M w e st start fuel) e) := rfl

/-! ### Fuel additivity and chaining -/

/-- Fuel additivity: `a + b` tests are `a` tests, then `b` more from where they stopped. -/
public theorem bitCheckLoopK_add (qs w lit st start a b : Nat) :
    bitCheckLoopK qs w lit st start (a + b)
      = bitCheckLoopK qs w lit (bitCheckLoopK qs w lit st start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [bitCheckLoopK_succ]

/-- One chain step, matching `lamLoopK_chain`. -/
public theorem bitCheckLoopK_chain (L qs w lit st st' start len rest : Nat)
    (hP : L = bitCheckLoopK qs w lit st start (len.add rest))
    (h : (bitCheckLoopK qs w lit st start len).beq st') :
    L = bitCheckLoopK qs w lit st' (start.add len) rest := by
  grind [bitCheckLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the set-bit count. -/
public theorem popcLoopK_add (b acc start x y : Nat) :
    popcLoopK b acc start (x + y) = popcLoopK b (popcLoopK b acc start x) (start + x) y := by
  induction y with
  | zero => rfl
  | succ y ih => grind [popcLoopK_succ]

/-- One chain step for the set-bit count. -/
public theorem popcLoopK_chain (L b acc acc' start len rest : Nat)
    (hP : L = popcLoopK b acc start (len.add rest))
    (h : (popcLoopK b acc start len).beq acc') :
    L = popcLoopK b acc' (start.add len) rest := by
  grind [popcLoopK_add, Nat.beq_eq]

/-- Replace the starting state by a kernel-checked equal literal, the way the chain is entered from
the state holding the powers of 2 and 3. -/
public theorem hpLoopK_congr (lit M w e s s' start fuel : Nat) (h : s.beq s') :
    hpLoopK lit M w e s start fuel = hpLoopK lit M w e s' start fuel := by
  rw [Nat.eq_of_beq_eq_true h]

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

public def bitCheckStep (qs w lit st i : Nat) : Nat :=
  let q := field qs w i
  let t := (q - 1) / 3
  let prev := st >>> 1
  let ok := st &&& 1
  let okMod := if q % 6 % 4 == 1 then 1 else 0
  let okRise := if prev + 1 ≤ t then 1 else 0
  let okSet := (lit >>> t) &&& 1
  (t <<< 1) + ok * okMod * okRise * okSet

public def bitCheckLoop (qs w lit st start fuel : Nat) : Nat := Id.run do
  let mut s := st
  for i in [0:fuel] do
    s := bitCheckStep qs w lit s (start + i)
  return s

public def popcLoop (b acc start fuel : Nat) : Nat := Id.run do
  let mut a := acc
  for i in [0:fuel] do
    a := a + popc32 ((b >>> ((start + i) * 32)) &&& ((1 <<< 32) - 1))
  return a

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
