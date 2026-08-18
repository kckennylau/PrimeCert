/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# Bitset arithmetic for kernel-checked certificates

A table is one natural number holding `w`-bit fields, lowest first, read by `fieldK`. `popc32K`
counts the set bits of a 32-bit word, `onesK` records those counts every 32 positions, from which
`onesBelowK` answers a count below an arbitrary position, and `popcLoopK` totals them over a range
of blocks. `bitCheckLoopK` tests packed values against a sieve, one field per step.

Each loop carries a peel lemma by `rfl`, fuel additivity by induction, and a chain lemma, which
together let an emitter split a run into kernel-checked batches. The compiled twins at the end
compute the batch literals.
-/

namespace PrimeCert

/-- Field `i` of `qs`, reading `w` bits from position `w * i`. -/
@[expose] public def fieldK (qs w i : Nat) : Nat :=
  (qs.shiftRight (w.mul i)).land ((Nat.shiftLeft (nat_lit 1) w).sub (nat_lit 1))

/-- The number of set bits of `v`, for `v < 2 ^ 32`, summing bit counts within fields of 2, 4, 8 and
then 32 bits (`popc32K_eq_bitSum` in `PrimeCert.PopCount`). The constants are the repeating masks
`0101…`, `00110011…` and `00001111…`, and `0x01010101`, whose product with a byte-per-field value
places the sum of the four bytes in the top byte. -/
@[expose] public def popc32K (v : Nat) : Nat :=
  let a := v.sub ((v.shiftRight (nat_lit 1)).land (nat_lit 1431655765))
  let b := (a.land (nat_lit 858993459)).add ((a.shiftRight (nat_lit 2)).land (nat_lit 858993459))
  let c := (b.add (b.shiftRight (nat_lit 4))).land (nat_lit 252645135)
  ((c.mul (nat_lit 16843009)).shiftRight (nat_lit 24)).land (nat_lit 255)

/-- Perform `fuel` steps, appending to `tbl` the running count of set bits of `lam`: field `i` holds
the number of set bits below position `32 * i`, in `w`-bit fields. `onesK` runs this from a table
holding the single field `0`. -/
@[expose] public noncomputable def onesLoopK (lam w tbl start fuel : Nat) : Nat :=
  fuel.rec tbl fun i t =>
    t.lor
      (((fieldK t w (start.add i)).add
          (popc32K ((lam.shiftRight (Nat.mul (nat_lit 32) (start.add i))).land
            ((Nat.shiftLeft (nat_lit 1) (nat_lit 32)).sub (nat_lit 1))))).shiftLeft
        (w.mul (start.add i).succ))

/-- Running counts of the set bits of `lam` at every multiple of 32, covering positions below
`32 * cnt` (`fieldK_onesK` in `PrimeCert.Ones`). -/
@[expose] public noncomputable def onesK (lam w cnt : Nat) : Nat :=
  onesLoopK lam w (nat_lit 0) (nat_lit 0) cnt

/-- Set bits of `lam` below position `p`, from the recorded count at the nearest lower multiple of
32 plus the bits of the partial chunk. -/
@[expose] public noncomputable def onesBelowK (lam ones wc p : Nat) : Nat :=
  ((ones.land
        ((((nat_lit 1).shiftLeft wc).sub (nat_lit 1)).shiftLeft
          (wc.mul (p.div (nat_lit 32))))).shiftRight
      (wc.mul (p.div (nat_lit 32)))).add
    (popc32K
      ((lam.land
          ((((nat_lit 1).shiftLeft (p.mod (nat_lit 32))).sub (nat_lit 1)).shiftLeft
            ((p.div (nat_lit 32)).mul (nat_lit 32)))).shiftRight
        ((p.div (nat_lit 32)).mul (nat_lit 32))))

/-- Add to `acc` the set bits of `b` in the 32-position blocks `start, start+1, …`. -/
@[expose] public noncomputable def popcLoopK (b acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    a.add
      (popc32K
        ((b.shiftRight ((start.add i).mul (nat_lit 32))).land
          (((nat_lit 1).shiftLeft (nat_lit 32)).sub (nat_lit 1))))

/-- Test field `i`: its value is 1 or 5 modulo 6, its sieve index exceeds the previous one, and its
sieve bit is set. -/
@[expose] public noncomputable def bitCheckStepK (qs w lit st i : Nat) : Nat :=
  let q := fieldK qs w i
  let t := (q.sub (nat_lit 1)).div (nat_lit 3)
  let prev := st.shiftRight (nat_lit 1)
  let ok := st.land (nat_lit 1)
  let okMod :=
    (((q.mod (nat_lit 6)).mod (nat_lit 4)).beq (nat_lit 1)).rec (nat_lit 0) (nat_lit 1)
  let okRise := (prev.succ.ble t).rec (nat_lit 0) (nat_lit 1)
  let okSet := (lit.shiftRight t).land (nat_lit 1)
  (t.shiftLeft (nat_lit 1)).add (((ok.mul okMod).mul okRise).mul okSet)

/-- Perform `fuel` field tests, from field `start`. -/
@[expose] public noncomputable def bitCheckLoopK (qs w lit st start fuel : Nat) : Nat :=
  fuel.rec st fun i s => bitCheckStepK qs w lit s (start.add i)

/-! ### Loop recurrences -/

/-- Loop recurrence: peel the top step, in the exact form the def uses. -/
public theorem onesLoopK_succ (lam w tbl start fuel : Nat) :
    onesLoopK lam w tbl start (fuel + 1)
      = (onesLoopK lam w tbl start fuel).lor
          (((fieldK (onesLoopK lam w tbl start fuel) w (start + fuel)).add
              (popc32K ((lam.shiftRight (32 * (start + fuel))).land
                ((Nat.shiftLeft 1 32).sub 1)))).shiftLeft
            (w * (start + fuel).succ)) := rfl

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

/-! ### Fuel additivity and chaining -/

/-- Fuel additivity for the running counts, the glue joining consecutive batches. -/
public theorem onesLoopK_add (lam w tbl start a b : Nat) :
    onesLoopK lam w tbl start (a + b)
      = onesLoopK lam w (onesLoopK lam w tbl start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [onesLoopK_succ]

/-- One chain step: given `L` as a loop of `len + rest` steps and a kernel-checked batch equation
saying `len` steps reach `tbl'`, restate `L` as a loop from `tbl'` with `rest` steps left. -/
public theorem onesLoopK_chain (L lam w tbl tbl' start len rest : Nat)
    (hP : L = onesLoopK lam w tbl start (len.add rest))
    (h : (onesLoopK lam w tbl start len).beq tbl') :
    L = onesLoopK lam w tbl' (start.add len) rest := by
  grind [onesLoopK_add, Nat.beq_eq]

/-- Fuel additivity: `a + b` tests are `a` tests, then `b` more from where they stopped. -/
public theorem bitCheckLoopK_add (qs w lit st start a b : Nat) :
    bitCheckLoopK qs w lit st start (a + b)
      = bitCheckLoopK qs w lit (bitCheckLoopK qs w lit st start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [bitCheckLoopK_succ]

/-- One chain step, matching `onesLoopK_chain`. -/
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

/-! ### Compiled twins

Executable copies of the definitions above, used to compute the batch literals. They appear in no
proof: a twin that disagreed with its kernel definition would produce a batch equation that fails
its kernel check. -/

public def field (qs w i : Nat) : Nat := (qs >>> (w * i)) &&& ((1 <<< w) - 1)

public def popc32 (v : Nat) : Nat :=
  let a := v - ((v >>> 1) &&& 1431655765)
  let b := (a &&& 858993459) + ((a >>> 2) &&& 858993459)
  let c := (b + (b >>> 4)) &&& 252645135
  ((c * 16843009) >>> 24) &&& 255

public def onesBelow (lam ones wc p : Nat) : Nat :=
  ((ones &&& (((1 <<< wc) - 1) <<< (wc * (p / 32)))) >>> (wc * (p / 32)))
    + popc32 ((lam &&& (((1 <<< (p % 32)) - 1) <<< ((p / 32) * 32))) >>> ((p / 32) * 32))

public def onesLoop (lam w tbl start fuel : Nat) : Nat := Id.run do
  let mut t := tbl
  for i in [0:fuel] do
    let j := start + i
    t := t ||| (((field t w j) + popc32 ((lam >>> (32 * j)) &&& ((1 <<< 32) - 1))) <<< (w * (j + 1)))
  return t

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

end PrimeCert
