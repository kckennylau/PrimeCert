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

end PrimeCert
