/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# Bitset arithmetic for kernel-checked certificates

Definitions written for the Lean kernel to evaluate by reduction, each with a compiled copy that a
command runs natively to compute the literals it emits. `popc32K` counts the set bits of a 32-bit
word (`popc32K_eq_bitSum` in `PrimeCert.PopCount`).
-/

namespace PrimeCert

/-- The number of set bits of `v`, for `v < 2 ^ 32`, summing bit counts within groups of 2, 4, 8
and then 32 bits (`popc32K_eq_bitSum` in `PrimeCert.PopCount`). The constants are the repeating
masks `0101…`, `00110011…` and `00001111…`, and `0x01010101`, whose product with a byte-per-group
value places the sum of the four bytes in the top byte. -/
@[expose] public def popc32K (v : Nat) : Nat :=
  let a := v.sub ((v.shiftRight (nat_lit 1)).land (nat_lit 0x55555555))
  let b := (a.land (nat_lit 0x33333333)).add ((a.shiftRight (nat_lit 2)).land (nat_lit 0x33333333))
  let c := (b.add (b.shiftRight (nat_lit 4))).land (nat_lit 0x0f0f0f0f)
  ((c.mul (nat_lit 0x01010101)).shiftRight (nat_lit 24)).land (nat_lit 0xff)

/-! ### Compiled twins

Executable copies of the definitions above, used to compute the literals a command emits. They
appear in no proof: a twin that disagreed with its kernel definition would produce an equation that
fails its kernel check. -/

public def popc32 (v : Nat) : Nat :=
  let a := v - ((v >>> 1) &&& 0x55555555)
  let b := (a &&& 0x33333333) + ((a >>> 2) &&& 0x33333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f
  ((c * 0x01010101) >>> 24) &&& 0xff

end PrimeCert
