/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Polya
public import PrimeCert.Sieve

/-!
# Prototype loops tying the prime powers to the sieve

Four ways for the kernel to establish that the strides driving `lamK` are the prime powers `q ≤ M`,
written to be measured against each other. No correctness proof accompanies them yet.

* `gapCheckLoopK` reads the packed strides and, per stride, tests its sieve bit and the emptiness of
  the sieve between it and the previous stride.
* `bitCheckLoopK` tests only the sieve bit of each stride; `popcLoopK` counts the sieve's set bits,
  and the two counts agreeing leaves no stride out.
* `lamSieveLoopK` builds the parity table from the sieve bits directly.
* `selfLoopK` builds the parity table and its own composite marker together, from neither.
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (num numK)

/-! ### Checking the packed strides against the sieve

The check state holds the previous stride's sieve index above bit 0 and a flag in bit 0, which stays
at 1 while every test has passed. The index of a number `q` coprime to 6 is `(q - 1) / 3`, inverting
`numK`. -/

/-- Test stride `i`: its value is 1 or 5 modulo 6, its sieve index exceeds the previous one, its
sieve bit is set, and the sieve bits between the two indices are clear. -/
@[expose] public noncomputable def gapCheckStepK (qs w lit st i : Nat) : Nat :=
  let q := fieldK qs w i
  let t := (q.sub (nat_lit 1)).div (nat_lit 3)
  let prev := st.shiftRight (nat_lit 1)
  let ok := st.land (nat_lit 1)
  let okMod :=
    (Nat.beq ((q.mod (nat_lit 6)).mod (nat_lit 4)) (nat_lit 1)).rec (nat_lit 0) (nat_lit 1)
  let okRise := (Nat.ble prev.succ t).rec (nat_lit 0) (nat_lit 1)
  let okSet := (lit.shiftRight t).land (nat_lit 1)
  let okGap :=
    (Nat.beq
      ((lit.shiftRight prev.succ).land
        (((nat_lit 1).shiftLeft (t.sub prev.succ)).sub (nat_lit 1)))
      (nat_lit 0)).rec (nat_lit 0) (nat_lit 1)
  (t.shiftLeft (nat_lit 1)).add ((((ok.mul okMod).mul okRise).mul okSet).mul okGap)

/-- Perform `fuel` stride tests, from stride `start`. -/
@[expose] public noncomputable def gapCheckLoopK (qs w lit st start fuel : Nat) : Nat :=
  fuel.rec st fun i s => gapCheckStepK qs w lit s (start.add i)

/-- Test stride `i`: its value is 1 or 5 modulo 6, its sieve index exceeds the previous one, and its
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

/-- Perform `fuel` stride tests, from stride `start`. -/
@[expose] public noncomputable def bitCheckLoopK (qs w lit st start fuel : Nat) : Nat :=
  fuel.rec st fun i s => bitCheckStepK qs w lit s (start.add i)

/-- Add to `acc` the set bits of `b` in the 32-position blocks `start, start+1, …`. -/
@[expose] public noncomputable def popcLoopK (b acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    a.add
      (popc32K
        ((b.shiftRight ((start.add i).mul (nat_lit 32))).land
          (((nat_lit 1).shiftLeft (nat_lit 32)).sub (nat_lit 1))))

/-! ### Building the parity table from the sieve

`numK t = 3t + 1 + t % 2` is the number at sieve index `t`, and its bit in the sieve is set when that
number is prime. -/

/-- Perform `fuel` steps from sieve index `start`, flipping the parity of the multiples of `numK i`
at each index whose sieve bit is set. -/
@[expose] public noncomputable def lamSieveLoopK (lit M rounds lam start fuel : Nat) : Nat :=
  fuel.rec lam fun i l =>
    (Nat.ble (nat_lit 1) ((lit.shiftRight (start.add i)).land (nat_lit 1))).rec l
      (markStrideK l (numK (start.add i)) M rounds)

/-- Perform `fuel` steps from `start`, flipping the parity of the multiples of every position whose
bit in `bits` is set. `bits` marks the prime powers, one bit per integer. -/
@[expose] public noncomputable def lamBitsLoopK (bits M rounds lam start fuel : Nat) : Nat :=
  fuel.rec lam fun i l =>
    (Nat.ble (nat_lit 1) ((bits.shiftRight (start.add i)).land (nat_lit 1))).rec l
      (markStrideK l (start.add i) M rounds)

/-! ### Building the parity table and a composite marker together

The state holds the marker above bit `B` and the parity table below it. At a number whose marker bit
is clear, one mask of that number's multiples both marks them composite and flips their parity. -/

/-- Step at `q`: on a clear marker bit, mask the multiples of `q` into the marker and flip their
parity in the table. -/
@[expose] public noncomputable def selfStepK (M rounds B st q : Nat) : Nat :=
  let comp := st.shiftRight B
  let lam := st.land (((nat_lit 1).shiftLeft B).sub (nat_lit 1))
  (Nat.ble (nat_lit 1) ((comp.shiftRight q).land (nat_lit 1))).rec
    (let mk := strideMaskK q M rounds;
      ((comp.lor mk).shiftLeft B).add
        ((lam.xor mk).land (((nat_lit 1).shiftLeft (Nat.succ M)).sub (nat_lit 1))))
    st

/-- Perform `fuel` steps from `start`. -/
@[expose] public noncomputable def selfLoopK (M rounds B st start fuel : Nat) : Nat :=
  fuel.rec st fun i s => selfStepK M rounds B s (start.add i)

/-! ### Moving each sieve bit to three times its position

`repMaskK` repeats `seed` at every multiple of `stride` up to `M`, by doubling; `strideMaskK` is the
case `seed = 1 <<< q`, `stride = q`. Round `k` of `spreadLoopK` doubles the gap between the bits it
has separated so far, keeping runs of `2 ^ k` bits at every multiple of `3 * 2 ^ k`. After the last
round bit `t` sits at `3 * t`. -/

/-- `seed` repeated at every multiple of `stride` up to `M`, over `rounds` doublings. -/
@[expose] public noncomputable def repMaskK (seed stride M rounds : Nat) : Nat :=
  Nat.rec seed
    (fun i m => ((stride.shiftLeft i).ble M).rec m (m.lor (m.shiftLeft (stride.shiftLeft i))))
    rounds

/-- Perform `fuel` spreading rounds, counting down from round `rounds - 1 - start`. -/
@[expose] public noncomputable def spreadLoopK (width rounds mrounds x start fuel : Nat) : Nat :=
  fuel.rec x fun i y =>
    let k := (rounds.sub (nat_lit 1)).sub (start.add i)
    (y.lor (y.shiftLeft ((nat_lit 2).shiftLeft k))).land
      (repMaskK (((nat_lit 1).shiftLeft ((nat_lit 1).shiftLeft k)).sub (nat_lit 1))
        ((nat_lit 3).shiftLeft k) width mrounds)

/-! ### Loop recurrences -/

/-- Peel the top test, in the exact form the def uses. -/
public theorem gapCheckLoopK_succ (qs w lit st start fuel : Nat) :
    gapCheckLoopK qs w lit st start (fuel + 1)
      = gapCheckStepK qs w lit (gapCheckLoopK qs w lit st start fuel) (start + fuel) := rfl

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

/-- Peel the top step, in the exact form the def uses. -/
public theorem lamSieveLoopK_succ (lit M rounds lam start fuel : Nat) :
    lamSieveLoopK lit M rounds lam start (fuel + 1)
      = (Nat.ble 1 ((lit.shiftRight (start + fuel)).land 1)).rec
          (lamSieveLoopK lit M rounds lam start fuel)
          (markStrideK (lamSieveLoopK lit M rounds lam start fuel) (numK (start + fuel)) M
            rounds) := rfl

/-- Peel the top step, in the exact form the def uses. -/
public theorem lamBitsLoopK_succ (bits M rounds lam start fuel : Nat) :
    lamBitsLoopK bits M rounds lam start (fuel + 1)
      = (Nat.ble 1 ((bits.shiftRight (start + fuel)).land 1)).rec
          (lamBitsLoopK bits M rounds lam start fuel)
          (markStrideK (lamBitsLoopK bits M rounds lam start fuel) (start + fuel) M rounds) := rfl

/-- Fuel additivity for the table built from one bit per integer. -/
public theorem lamBitsLoopK_add (bits M rounds lam start a b : Nat) :
    lamBitsLoopK bits M rounds lam start (a + b)
      = lamBitsLoopK bits M rounds (lamBitsLoopK bits M rounds lam start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [lamBitsLoopK_succ]

/-- One chain step for the table built from one bit per integer. -/
public theorem lamBitsLoopK_chain (L bits M rounds lam lam' start len rest : Nat)
    (hP : L = lamBitsLoopK bits M rounds lam start (len.add rest))
    (h : (lamBitsLoopK bits M rounds lam start len).beq lam') :
    L = lamBitsLoopK bits M rounds lam' (start.add len) rest := by
  grind [lamBitsLoopK_add, Nat.beq_eq]

/-- Peel the top round, in the exact form the def uses. -/
public theorem spreadLoopK_succ (width rounds mrounds x start fuel : Nat) :
    spreadLoopK width rounds mrounds x start (fuel + 1)
      = (let y := spreadLoopK width rounds mrounds x start fuel
        let k := (rounds.sub 1).sub (start + fuel)
        (y.lor (y.shiftLeft (Nat.shiftLeft 2 k))).land
          (repMaskK ((Nat.shiftLeft 1 (Nat.shiftLeft 1 k)).sub 1) (Nat.shiftLeft 3 k) width
            mrounds)) := rfl

/-- Peel the top step, in the exact form the def uses. -/
public theorem selfLoopK_succ (M rounds B st start fuel : Nat) :
    selfLoopK M rounds B st start (fuel + 1)
      = selfStepK M rounds B (selfLoopK M rounds B st start fuel) (start + fuel) := rfl

/-! ### Fuel additivity and chaining -/

/-- Fuel additivity: `a + b` tests are `a` tests, then `b` more from where they stopped. -/
public theorem gapCheckLoopK_add (qs w lit st start a b : Nat) :
    gapCheckLoopK qs w lit st start (a + b)
      = gapCheckLoopK qs w lit (gapCheckLoopK qs w lit st start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [gapCheckLoopK_succ]

/-- One chain step, matching `lamLoopK_chain`. -/
public theorem gapCheckLoopK_chain (L qs w lit st st' start len rest : Nat)
    (hP : L = gapCheckLoopK qs w lit st start (len.add rest))
    (h : (gapCheckLoopK qs w lit st start len).beq st') :
    L = gapCheckLoopK qs w lit st' (start.add len) rest := by
  grind [gapCheckLoopK_add, Nat.beq_eq]

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

/-- Fuel additivity for the table built from the sieve. -/
public theorem lamSieveLoopK_add (lit M rounds lam start a b : Nat) :
    lamSieveLoopK lit M rounds lam start (a + b)
      = lamSieveLoopK lit M rounds (lamSieveLoopK lit M rounds lam start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [lamSieveLoopK_succ]

/-- One chain step for the table built from the sieve. -/
public theorem lamSieveLoopK_chain (L lit M rounds lam lam' start len rest : Nat)
    (hP : L = lamSieveLoopK lit M rounds lam start (len.add rest))
    (h : (lamSieveLoopK lit M rounds lam start len).beq lam') :
    L = lamSieveLoopK lit M rounds lam' (start.add len) rest := by
  grind [lamSieveLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the spreading rounds. -/
public theorem spreadLoopK_add (width rounds mrounds x start a b : Nat) :
    spreadLoopK width rounds mrounds x start (a + b)
      = spreadLoopK width rounds mrounds (spreadLoopK width rounds mrounds x start a)
          (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [spreadLoopK_succ]

/-- One chain step for the spreading rounds. -/
public theorem spreadLoopK_chain (L width rounds mrounds x x' start len rest : Nat)
    (hP : L = spreadLoopK width rounds mrounds x start (len.add rest))
    (h : (spreadLoopK width rounds mrounds x start len).beq x') :
    L = spreadLoopK width rounds mrounds x' (start.add len) rest := by
  grind [spreadLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the joint marker and table. -/
public theorem selfLoopK_add (M rounds B st start a b : Nat) :
    selfLoopK M rounds B st start (a + b)
      = selfLoopK M rounds B (selfLoopK M rounds B st start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [selfLoopK_succ]

/-- One chain step for the joint marker and table. -/
public theorem selfLoopK_chain (L M rounds B st st' start len rest : Nat)
    (hP : L = selfLoopK M rounds B st start (len.add rest))
    (h : (selfLoopK M rounds B st start len).beq st') :
    L = selfLoopK M rounds B st' (start.add len) rest := by
  grind [selfLoopK_add, Nat.beq_eq]

/-! ### Compiled twins

Executable copies used to compute the batch literals; a twin disagreeing with its kernel definition
would produce a batch equation that fails its kernel check. -/

public def gapCheckStep (qs w lit st i : Nat) : Nat :=
  let q := field qs w i
  let t := (q - 1) / 3
  let prev := st >>> 1
  let ok := st &&& 1
  let okMod := if q % 6 % 4 == 1 then 1 else 0
  let okRise := if prev + 1 ≤ t then 1 else 0
  let okSet := (lit >>> t) &&& 1
  let okGap := if (lit >>> (prev + 1)) &&& ((1 <<< (t - (prev + 1))) - 1) == 0 then 1 else 0
  (t <<< 1) + ok * okMod * okRise * okSet * okGap

public def gapCheckLoop (qs w lit st start fuel : Nat) : Nat := Id.run do
  let mut s := st
  for i in [0:fuel] do
    s := gapCheckStep qs w lit s (start + i)
  return s

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

public def lamSieveLoop (lit M rounds lam start fuel : Nat) : Nat := Id.run do
  let mut l := lam
  for i in [0:fuel] do
    let t := start + i
    if (lit >>> t) &&& 1 ≠ 0 then
      l := markStride l (num t) M rounds
  return l

public def repMask (seed stride M rounds : Nat) : Nat := Id.run do
  let mut m := seed
  for i in [0:rounds] do
    let s := stride <<< i
    if s ≤ M then
      m := m ||| (m <<< s)
  return m

public def spreadLoop (width rounds mrounds x start fuel : Nat) : Nat := Id.run do
  let mut y := x
  for i in [0:fuel] do
    let k := rounds - 1 - (start + i)
    y := (y ||| (y <<< (2 <<< k))) &&& repMask ((1 <<< (1 <<< k)) - 1) (3 <<< k) width mrounds
  return y

public def lamBitsLoop (bits M rounds lam start fuel : Nat) : Nat := Id.run do
  let mut l := lam
  for i in [0:fuel] do
    let n := start + i
    if (bits >>> n) &&& 1 ≠ 0 then
      l := markStride l n M rounds
  return l

public def selfStep (M rounds B st q : Nat) : Nat :=
  let comp := st >>> B
  let lam := st &&& ((1 <<< B) - 1)
  if (comp >>> q) &&& 1 ≠ 0 then st
  else
    let mk := strideMask q M rounds
    ((comp ||| mk) <<< B) + ((lam ^^^ mk) &&& ((1 <<< (M + 1)) - 1))

public def selfLoop (M rounds B st start fuel : Nat) : Nat := Id.run do
  let mut s := st
  for i in [0:fuel] do
    s := selfStep M rounds B s (start + i)
  return s

end PrimeCert.Polya
