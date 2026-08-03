/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# A kernel-checked parity table for the Liouville function

The number of prime factors of `n` counted with multiplicity is the number of prime powers
dividing `n`, so the parity of that count is the exclusive-or over prime powers `q` of `q ∣ n`.
This file builds the whole table by one exclusive-or per prime power: the state is a natural
number used as a bitset holding bits `0 … M`, and bit `n` records the parity for `n`.

The prime powers arrive as a bitset `pp`, whose bit `q` is set exactly for the prime powers
`q ≤ M`; `PolyaCorrect` derives that from the certified sieve.

Strides up to `2 ^ 32` times the table width are supported (32 doubling rounds in `strideMaskK`).

The `run_lam` command in `Meta/Polya` computes the table natively in batches, has the kernel check
each, and glues them into an equation `lamK pp M = <literal>`.
-/

namespace PrimeCert.Polya

/-- The natural number whose bits at positions `0 … M` are set exactly at the positive multiples of
`q`, namely `q, 2q, 3q, …`; see `testBit_strideMaskK` in `PolyaCorrect`. Positions above `M` are
cleared by `markStrideK`. -/
@[expose] public noncomputable def strideMaskK (q M : Nat) : Nat :=
  Nat.rec
    (Nat.shiftLeft 1 q)
    (fun i mk =>
      ((q.shiftLeft i).ble M).rec mk
        (mk.lor (mk.shiftLeft (q.shiftLeft i))))
    32

/-- One step: flip the parity bit of every multiple of `q` up to `M`, and clear everything above
`M`, so the table stays `M + 1` bits wide. -/
@[expose] public noncomputable def markStrideK (lam q M : Nat) : Nat :=
  (lam.xor (strideMaskK q M)).land ((Nat.shiftLeft 1 (Nat.succ M)).sub 1)

/-- Perform `fuel` steps on the table `lam`, scanning strides `start, start+1, …`: at each stride
whose bit in `pp` is set, flip the parity bit of its multiples. `lamK` runs this from an empty
table. -/
@[expose] public noncomputable def lamLoopK (pp M lam start fuel : Nat) : Nat :=
  fuel.rec lam fun i l =>
      (Nat.ble 1 (pp.land (Nat.shiftLeft 1 (start.add i)))).rec l
        (markStrideK l (start.add i) M)

/-- The full parity table for numbers up to `M`: bit `n` is set iff `n` has an odd number of prime
factors counted with multiplicity, given that bit `q` of `pp` is set exactly for the prime powers
`q ≤ M` (`lamK_testBit_iff` in `PolyaCorrect`). -/
@[expose] public noncomputable def lamK (pp M : Nat) : Nat :=
  lamLoopK pp M 0 2 (M.sub 1)

/-- Loop recurrence: peel the top stride `start+fuel`, in the exact `Bool.rec` form the def uses. -/
public theorem lamLoopK_succ (pp M lam start fuel : Nat) :
    lamLoopK pp M lam start (fuel + 1)
      = Bool.rec (lamLoopK pp M lam start fuel)
          (markStrideK (lamLoopK pp M lam start fuel) (start + fuel) M)
          (Nat.ble 1 (pp &&& (1 <<< (start + fuel)))) := rfl

/-! ### Compiled twins

Executable copies of the definitions above, used by `run_lam` to compute the batch literals.
They appear in no proof: a twin that disagreed with its kernel definition would produce a batch
equation that fails its kernel check. -/

public def strideMask (q M : Nat) : Nat := Id.run do
  let mut mask := 1 <<< q
  for i in [0:32] do
    let s := q <<< i
    if s ≤ M then
      mask := mask ||| (mask <<< s)
  return mask

public def markStride (lam q M : Nat) : Nat := (lam ^^^ strideMask q M) &&& ((1 <<< (M + 1)) - 1)

public def lamLoop (pp M lam start fuel : Nat) : Nat := Id.run do
  let mut l := lam
  for i in [0:fuel] do
    let j := start + i
    if pp &&& (1 <<< j) ≠ 0 then
      l := markStride l j M
  return l

/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` steps from where the
first run stopped. This is the glue that joins consecutive batches. -/
public theorem lamLoopK_add (pp M lam start a b : Nat) :
    lamLoopK pp M lam start (a + b)
      = lamLoopK pp M (lamLoopK pp M lam start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [lamLoopK_succ]

/-- One chain step: given `L = lamLoopK pp M lam start (len + rest)` and a kernel-checked batch
equation saying `len` steps from `lam` reach `lam'`, restate `L` as a loop from `lam'` at stride
`start + len` with `rest` steps left. -/
public theorem lamLoopK_chain (L pp M lam lam' start len rest : Nat)
    (hP : L = lamLoopK pp M lam start (len.add rest))
    (h : (lamLoopK pp M lam start len).beq lam') :
    L = lamLoopK pp M lam' (start.add len) rest := by
  grind [lamLoopK_add, Nat.beq_eq]

end PrimeCert.Polya
