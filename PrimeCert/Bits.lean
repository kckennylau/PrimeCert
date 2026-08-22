/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# Bitset arithmetic for kernel-checked certificates

Definitions the Lean kernel evaluates by reduction, each with a compiled copy that a command runs
natively to compute the literals it emits.
-/

namespace PrimeCert

/-- Entry `i` of `qs`, the `w` bits at position `w * i` (`entryK_eq_div_mod` in
`PrimeCert.Entry`). -/
@[expose] public def entryK (qs w i : Nat) : Nat :=
  (qs.shiftRight (w.mul i)).land ((Nat.shiftLeft (nat_lit 1) w).sub (nat_lit 1))

/-- The number of set bits of `v`, for `v < 2 ^ 64` (`popc64K_eq_bitSum` in
`PrimeCert.PopCount`). -/
@[expose] public def popc64K (v : Nat) : Nat :=
  let a := v.sub ((v.shiftRight (nat_lit 1)).land (nat_lit 0x5555555555555555))
  let b := (a.land (nat_lit 0x3333333333333333)).add
    ((a.shiftRight (nat_lit 2)).land (nat_lit 0x3333333333333333))
  let c := (b.add (b.shiftRight (nat_lit 4))).land (nat_lit 0x0f0f0f0f0f0f0f0f)
  ((c.mul (nat_lit 0x0101010101010101)).shiftRight (nat_lit 56)).land (nat_lit 0xff)

/-- Test entry `i`: its value is 1 or 5 modulo 6, its sieve index exceeds the previous one, and its
sieve bit is set. The result carries that index above bit 0 and the running flag in bit 0
(`bitCheckStepK_eq` in `PrimeCert.BitCheck`). -/
@[expose] public noncomputable def bitCheckStepK (qs w lit st i : Nat) : Nat :=
  let q := entryK qs w i
  let t := (q.sub (nat_lit 1)).div (nat_lit 3)
  let prev := st.shiftRight (nat_lit 1)
  let ok := st.land (nat_lit 1)
  let okMod :=
    (((q.mod (nat_lit 6)).mod (nat_lit 4)).beq (nat_lit 1)).rec (nat_lit 0) (nat_lit 1)
  let okRise := (prev.succ.ble t).rec (nat_lit 0) (nat_lit 1)
  let okSet := (lit.shiftRight t).land (nat_lit 1)
  (t.shiftLeft (nat_lit 1)).add (((ok.mul okMod).mul okRise).mul okSet)

/-- Perform `fuel` entry tests, from entry `start`. -/
@[expose] public noncomputable def bitCheckLoopK (qs w lit st start fuel : Nat) : Nat :=
  fuel.rec st fun i s ↦ bitCheckStepK qs w lit s (start.add i)

/-! ### Loop recurrences -/

/-- Peel the top test, in the form the definition uses. -/
public theorem bitCheckLoopK_succ (qs w lit st start fuel : Nat) :
    bitCheckLoopK qs w lit st start (fuel + 1)
      = bitCheckStepK qs w lit (bitCheckLoopK qs w lit st start fuel) (start + fuel) := rfl

/-- Fuel additivity: `a + b` tests are `a` tests, then `b` more from where they stopped. -/
public theorem bitCheckLoopK_add (qs w lit st start a b : Nat) :
    bitCheckLoopK qs w lit st start (a + b)
      = bitCheckLoopK qs w lit (bitCheckLoopK qs w lit st start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [bitCheckLoopK_succ]

/-- One chain step: with `L` a loop of `len + rest` tests and a kernel-checked equation saying
`len` tests reach `st'`, restate `L` as a loop from `st'` with `rest` tests left. -/
public theorem bitCheckLoopK_chain (L qs w lit st st' start len rest : Nat)
    (hP : L = bitCheckLoopK qs w lit st start (len.add rest))
    (h : (bitCheckLoopK qs w lit st start len).beq st') :
    L = bitCheckLoopK qs w lit st' (start.add len) rest := by
  grind [bitCheckLoopK_add, Nat.beq_eq]

/-! ### Compiled twins

Executable copies of the definitions above, run by a command to compute the literals it emits. The
kernel check on each emitted equation holds a copy to its kernel definition. -/

/-- Entry `i` of `qs`, the `w` bits at position `w * i`. -/
public def entry (qs w i : Nat) : Nat := (qs >>> (w * i)) &&& ((1 <<< w) - 1)

/-- The number of set bits of `v`, for `v < 2 ^ 64`. -/
public def popc64 (v : Nat) : Nat :=
  let a := v - ((v >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c * 0x0101010101010101) >>> 56) &&& 0xff

/-- Test entry `i`, carrying its sieve index above bit 0 and the running flag in bit 0. -/
public def bitCheckStep (qs w lit st i : Nat) : Nat :=
  let q := entry qs w i
  let t := (q - 1) / 3
  let prev := st >>> 1
  let ok := st &&& 1
  let okMod := if q % 6 % 4 == 1 then 1 else 0
  let okRise := if prev + 1 ≤ t then 1 else 0
  let okSet := (lit >>> t) &&& 1
  (t <<< 1) + ok * okMod * okRise * okSet

/-- Perform `fuel` entry tests, from entry `start`. -/
public def bitCheckLoop (qs w lit st start fuel : Nat) : Nat := Id.run do
  let mut s := st
  for i in [0:fuel] do
    s := bitCheckStep qs w lit s (start + i)
  return s

end PrimeCert
