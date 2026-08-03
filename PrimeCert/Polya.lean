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

The prime powers arrive packed into one natural number as `w`-bit fields, lowest first, one field
per step of the loop; `PolyaCorrect` derives that packing from the certified sieve.

Strides up to `2 ^ 32` times the table width are supported (32 doubling rounds in `strideMaskK`).

The `run_lam` command in `Meta/Polya` computes the table natively in batches, has the kernel check
each, and glues them into an equation `lamK qs w M cnt = <literal>`.
-/

namespace PrimeCert.Polya

/-- The natural number whose bits at positions `0 … M` are set exactly at the positive multiples of
`q`, namely `q, 2q, 3q, …`; see `testBit_strideMaskK` in `PolyaCorrect`. Positions above `M` are
cleared by `markStrideK`. -/
@[expose] public noncomputable def strideMaskK (q M : Nat) : Nat :=
  Nat.rec
    (Nat.shiftLeft (nat_lit 1) q)
    (fun i mk =>
      ((q.shiftLeft i).ble M).rec mk
        (mk.lor (mk.shiftLeft (q.shiftLeft i))))
    (nat_lit 32)

/-- One step: flip the parity bit of every multiple of `q` up to `M`, and clear everything above
`M`, so the table stays `M + 1` bits wide. -/
@[expose] public noncomputable def markStrideK (lam q M : Nat) : Nat :=
  (lam.xor (strideMaskK q M)).land ((Nat.shiftLeft (nat_lit 1) (Nat.succ M)).sub (nat_lit 1))

/-- Field `i` of `qs`, reading `w` bits from position `w * i`. -/
@[expose] public def fieldK (qs w i : Nat) : Nat :=
  (qs.shiftRight (w.mul i)).land ((Nat.shiftLeft (nat_lit 1) w).sub (nat_lit 1))

/-- Perform `fuel` steps on the table `lam`, taking the strides from fields `start, start+1, …` of
`qs` and flipping the parity bit of each stride's multiples. `lamK` runs this from an empty
table. -/
@[expose] public noncomputable def lamLoopK (qs w M lam start fuel : Nat) : Nat :=
  fuel.rec lam fun i l => markStrideK l (fieldK qs w (start.add i)) M

/-- The full parity table for numbers up to `M`: bit `n` is set iff `n` has an odd number of prime
factors counted with multiplicity, given that the `cnt` fields of `qs` are exactly the prime powers
`q ≤ M` (`lamK_testBit_iff` in `PolyaCorrect`). -/
@[expose] public noncomputable def lamK (qs w M cnt : Nat) : Nat :=
  lamLoopK qs w M (nat_lit 0) (nat_lit 0) cnt

/-- The number of set bits of `v`, for `v < 2 ^ 32`, summing bit counts within fields of 2, 4, 8 and
then 32 bits (`popc32K_eq_count` in `PolyaCorrect`). The constants are the repeating masks `0101…`,
`00110011…` and `00001111…`, and `0x01010101`, whose product with a byte-per-field value places the
sum of the four bytes in the top byte. -/
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
      (Nat.shiftLeft
        ((fieldK t w (start.add i)).add
          (popc32K ((lam.shiftRight (Nat.mul (nat_lit 32) (start.add i))).land
            ((Nat.shiftLeft (nat_lit 1) (nat_lit 32)).sub (nat_lit 1)))))
        (w.mul (Nat.succ (start.add i))))

/-- Running counts of the set bits of `lam` at every multiple of 32, covering positions below
`32 * cnt` (`onesK_field_eq` in `PolyaCorrect`). -/
@[expose] public noncomputable def onesK (lam w cnt : Nat) : Nat :=
  onesLoopK lam w (nat_lit 0) (nat_lit 0) cnt

/-- Loop recurrence: peel the top step, in the exact form the def uses. -/
public theorem onesLoopK_succ (lam w tbl start fuel : Nat) :
    onesLoopK lam w tbl start (fuel + 1)
      = (onesLoopK lam w tbl start fuel).lor
          (Nat.shiftLeft
            ((fieldK (onesLoopK lam w tbl start fuel) w (start + fuel)).add
              (popc32K ((lam.shiftRight (32 * (start + fuel))).land ((Nat.shiftLeft 1 32).sub 1))))
            (w * Nat.succ (start + fuel))) := rfl

/-- Loop recurrence: peel the top field `start+fuel`, in the exact form the def uses. -/
public theorem lamLoopK_succ (qs w M lam start fuel : Nat) :
    lamLoopK qs w M lam start (fuel + 1)
      = markStrideK (lamLoopK qs w M lam start fuel) (fieldK qs w (start + fuel)) M := rfl

/-- Field `i` of `st`, reading 64 bits from position `64 * i`. The loop state below holds the next
index in field 0 and the two halves of the running sum in fields 1 and 2. -/
@[expose] public def stFieldK (st i : Nat) : Nat :=
  (st.shiftRight (Nat.mul (nat_lit 64) i)).land ((Nat.shiftLeft (nat_lit 1) (nat_lit 64)).sub 1)

/-- Set bits of `lam` below position `p`, from the recorded count at the nearest lower multiple of
32 plus the bits of the partial chunk. -/
@[expose] public noncomputable def onesBelowK (lam ones wc p : Nat) : Nat :=
  (fieldK ones wc (p.div (nat_lit 32))).add
    (popc32K
      (((lam.shiftRight ((p.div (nat_lit 32)).mul (nat_lit 32))).land
          ((Nat.shiftLeft (nat_lit 1) (nat_lit 32)).sub (nat_lit 1))).land
        ((Nat.shiftLeft (nat_lit 1) (p.mod (nat_lit 32))).sub (nat_lit 1))))

/-- One block of the recurrence for `L v`. The index `k` in field 0 gives the quotient `q = v / k`,
which repeats for every index up to `v / q`; the run length times `L q` is added to the running sum,
held as the pair of fields 1 and 2 standing for their difference. Values of `q` up to `cutoff` come
from the parity and count tables, larger ones from field `x / q` of `big`, which holds `L` offset by
`off`. -/
@[expose] public noncomputable def blockAddK (v k st a b : Nat) : Nat :=
  let k2 := v.div (v.div k)
  let run := (k2.sub k).succ
  (k2.succ.add (Nat.shiftLeft ((stFieldK st (nat_lit 1)).add (run.mul a)) (nat_lit 64))).add
    (Nat.shiftLeft ((stFieldK st (nat_lit 2)).add (run.mul b)) (nat_lit 128))

@[expose] public noncomputable def blockStepK
    (x v cutoff lam ones wc big wb off st : Nat) : Nat :=
  (Nat.ble (stFieldK st (nat_lit 0)) v).rec st
    (let k := stFieldK st (nat_lit 0)
     let q := v.div k
     (Nat.ble q cutoff).rec
       (blockAddK v k st (fieldK big wb (x.div q)) off)
       (blockAddK v k st q ((onesBelowK lam ones wc q.succ).mul (nat_lit 2))))

/-- Perform `fuel` blocks of the recurrence for `L v`. -/
@[expose] public noncomputable def blockLoopK
    (x v cutoff lam ones wc big wb off st fuel : Nat) : Nat :=
  fuel.rec st fun _ s => blockStepK x v cutoff lam ones wc big wb off s

/-- Loop recurrence: peel the top block, in the exact form the def uses. -/
public theorem blockLoopK_succ (x v cutoff lam ones wc big wb off st fuel : Nat) :
    blockLoopK x v cutoff lam ones wc big wb off st (fuel + 1)
      = blockStepK x v cutoff lam ones wc big wb off
          (blockLoopK x v cutoff lam ones wc big wb off st fuel) := rfl

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

public def field (qs w i : Nat) : Nat := (qs >>> (w * i)) &&& ((1 <<< w) - 1)

public def lamLoop (qs w M lam start fuel : Nat) : Nat := Id.run do
  let mut l := lam
  for i in [0:fuel] do
    l := markStride l (field qs w (start + i)) M
  return l

public def popc32 (v : Nat) : Nat :=
  let a := v - ((v >>> 1) &&& 1431655765)
  let b := (a &&& 858993459) + ((a >>> 2) &&& 858993459)
  let c := (b + (b >>> 4)) &&& 252645135
  ((c * 16843009) >>> 24) &&& 255

public def stField (st i : Nat) : Nat := (st >>> (64 * i)) &&& ((1 <<< 64) - 1)

public def onesBelow (lam ones wc p : Nat) : Nat :=
  field ones wc (p / 32)
    + popc32 (((lam >>> ((p / 32) * 32)) &&& ((1 <<< 32) - 1)) &&& ((1 <<< (p % 32)) - 1))

public def blockAdd (v k st a b : Nat) : Nat :=
  let k2 := v / (v / k)
  let run := k2 - k + 1
  (k2 + 1) + ((stField st 1 + run * a) <<< 64) + ((stField st 2 + run * b) <<< 128)

public def blockStep (x v cutoff lam ones wc big wb off st : Nat) : Nat :=
  let k := stField st 0
  if k ≤ v then
    let q := v / k
    if q ≤ cutoff then blockAdd v k st q (2 * onesBelow lam ones wc (q + 1))
    else blockAdd v k st (field big wb (x / q)) off
  else st

public def blockLoop (x v cutoff lam ones wc big wb off st fuel : Nat) : Nat := Id.run do
  let mut s := st
  for _ in [0:fuel] do
    s := blockStep x v cutoff lam ones wc big wb off s
  return s

public def onesLoop (lam w tbl start fuel : Nat) : Nat := Id.run do
  let mut t := tbl
  for i in [0:fuel] do
    let j := start + i
    t := t ||| (((field t w j) + popc32 ((lam >>> (32 * j)) &&& ((1 <<< 32) - 1))) <<< (w * (j + 1)))
  return t

/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` steps from where the
first run stopped. This is the glue that joins consecutive batches. -/
public theorem lamLoopK_add (qs w M lam start a b : Nat) :
    lamLoopK qs w M lam start (a + b)
      = lamLoopK qs w M (lamLoopK qs w M lam start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [lamLoopK_succ]

/-- One chain step: given `L = lamLoopK qs w M lam start (len + rest)` and a kernel-checked batch
equation saying `len` steps from `lam` reach `lam'`, restate `L` as a loop from `lam'` at field
`start + len` with `rest` steps left. -/
public theorem lamLoopK_chain (L qs w M lam lam' start len rest : Nat)
    (hP : L = lamLoopK qs w M lam start (len.add rest))
    (h : (lamLoopK qs w M lam start len).beq lam') :
    L = lamLoopK qs w M lam' (start.add len) rest := by
  grind [lamLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the blocks, the glue joining consecutive batches. -/
public theorem blockLoopK_add (x v cutoff lam ones wc big wb off st a b : Nat) :
    blockLoopK x v cutoff lam ones wc big wb off st (a + b)
      = blockLoopK x v cutoff lam ones wc big wb off
          (blockLoopK x v cutoff lam ones wc big wb off st a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [blockLoopK_succ]

/-- One chain step for the blocks, matching `lamLoopK_chain`. -/
public theorem blockLoopK_chain (L x v cutoff lam ones wc big wb off st st' len rest : Nat)
    (hP : L = blockLoopK x v cutoff lam ones wc big wb off st (len.add rest))
    (h : (blockLoopK x v cutoff lam ones wc big wb off st len).beq st') :
    L = blockLoopK x v cutoff lam ones wc big wb off st' rest := by
  grind [blockLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the running counts, the glue joining consecutive batches. -/
public theorem onesLoopK_add (lam w tbl start a b : Nat) :
    onesLoopK lam w tbl start (a + b)
      = onesLoopK lam w (onesLoopK lam w tbl start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [onesLoopK_succ]

/-- One chain step for the running counts, matching `lamLoopK_chain`. -/
public theorem onesLoopK_chain (L lam w tbl tbl' start len rest : Nat)
    (hP : L = onesLoopK lam w tbl start (len.add rest))
    (h : (onesLoopK lam w tbl start len).beq tbl') :
    L = onesLoopK lam w tbl' (start.add len) rest := by
  grind [onesLoopK_add, Nat.beq_eq]

end PrimeCert.Polya
