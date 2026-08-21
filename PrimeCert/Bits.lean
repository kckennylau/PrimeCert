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

/-- The number of set bits of `v`, for `v < 2 ^ 32` (`popc32K_eq_bitSum` in
`PrimeCert.PopCount`). -/
@[expose] public def popc32K (v : Nat) : Nat :=
  let a := v.sub ((v.shiftRight (nat_lit 1)).land (nat_lit 0x55555555))
  let b := (a.land (nat_lit 0x33333333)).add ((a.shiftRight (nat_lit 2)).land (nat_lit 0x33333333))
  let c := (b.add (b.shiftRight (nat_lit 4))).land (nat_lit 0x0f0f0f0f)
  ((c.mul (nat_lit 0x01010101)).shiftRight (nat_lit 24)).land (nat_lit 0xff)

/-! ### Compiled twins

Executable copies of the definitions above, run by a command to compute the literals it emits. The
kernel check on each emitted equation holds a copy to its kernel definition. -/

/-- The number of set bits of `v`, for `v < 2 ^ 32`. -/
public def popc32 (v : Nat) : Nat :=
  let a := v - ((v >>> 1) &&& 0x55555555)
  let b := (a &&& 0x33333333) + ((a >>> 2) &&& 0x33333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f
  ((c * 0x01010101) >>> 24) &&& 0xff

end PrimeCert
