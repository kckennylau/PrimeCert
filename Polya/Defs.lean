/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Bits

/-!
# A kernel-checked parity table for the Liouville function

The number of prime factors of `n` counted with multiplicity is the number of prime powers
dividing `n`, so the parity of that count is the exclusive-or over prime powers `q` of `q ∣ n`.
This file builds the whole table by one exclusive-or per prime power: the state is a natural
number used as a bitset holding bits `0 … M`, and bit `n` records the parity for `n`.

The prime powers arrive packed into one natural number as `w`-bit entries, lowest first, one entry
per step of the loop; `Polya.Correct.TableSpec` derives that packing from the certified sieve.

The `rounds` argument is the number of doubling rounds in `strideMaskK`, so strides up to
`2 ^ rounds` times the table width are covered.

The `run_lam` command in `Polya.Meta` computes the table natively in batches, has the kernel check
each, and glues them into an equation `lamK qs w M cnt = <literal>`.
-/

namespace PrimeCert.Polya

/-- The natural number whose bits at positions `0 … M` are set exactly at the positive multiples of
`q`, namely `q, 2q, 3q, …`; see `testBit_strideMaskK` in `Polya.Correct.Parity`. Positions above
`M` are cleared by `markStrideK`. -/
@[expose] public noncomputable def strideMaskK (q M rounds : Nat) : Nat :=
  Nat.rec
    (Nat.shiftLeft (nat_lit 1) q)
    (fun i mk =>
      ((q.shiftLeft i).ble M).rec mk
        (mk.lor (mk.shiftLeft (q.shiftLeft i))))
    rounds

/-- One step: flip the parity bit of every multiple of `q` up to `M`, and clear everything above
`M`, so the table stays `M + 1` bits wide. -/
@[expose] public noncomputable def markStrideK (lam q M rounds : Nat) : Nat :=
  (lam.xor (strideMaskK q M rounds)).land ((Nat.shiftLeft (nat_lit 1) M.succ).sub (nat_lit 1))

/-- Perform `fuel` steps on the table `lam`, taking the strides from entries `start, start+1, …` of
`qs` and flipping the parity bit of each stride's multiples. `lamK` runs this from an empty
table. -/
@[expose] public noncomputable def lamLoopK (qs w M rounds lam start fuel : Nat) : Nat :=
  fuel.rec lam fun i l => markStrideK l (entryK qs w (start.add i)) M rounds

/-- The full parity table for numbers up to `M`: bit `n` is set iff `n` has an odd number of prime
factors counted with multiplicity, given that the `cnt` entries of `qs` are exactly the prime powers
`q ≤ M` (`testBit_lamK` in `Polya.Correct.Lam`). -/
@[expose] public noncomputable def lamK (qs w M rounds cnt : Nat) : Nat :=
  lamLoopK qs w M rounds (nat_lit 0) (nat_lit 0) cnt

/-- Loop recurrence: peel the top entry `start+fuel`, in the exact form the def uses. -/
public theorem lamLoopK_succ (qs w M rounds lam start fuel : Nat) :
    lamLoopK qs w M rounds lam start (fuel + 1)
      = markStrideK (lamLoopK qs w M rounds lam start fuel) (entryK qs w (start + fuel)) M
          rounds := rfl

/-- Perform `fuel` steps, appending to `tbl` the value `L i + off` for `i = start, start+1, …`,
each read off the parity table and the running counts. -/
@[expose] public noncomputable def lowLoopK (lam ones wc off wb tbl start fuel : Nat) : Nat :=
  fuel.rec tbl fun i t =>
    t.lor
      ((((start.add i).add off).sub
          ((onesBelowK lam ones wc (start.add i).succ).mul (nat_lit 2))).shiftLeft
        (wb.mul (start.add i)))

/-- Perform `fuel` steps, appending to `tbl` the value `L (x / i) + off` for `i = start, start+1,
…`, each read off the parity table and the running counts. -/
@[expose] public noncomputable def hiLoopK (x lam ones wc off wb tbl start fuel : Nat) : Nat :=
  fuel.rec tbl fun i t =>
    t.lor
      ((((x.div (start.add i)).add off).sub
          ((onesBelowK lam ones wc (x.div (start.add i)).succ).mul (nat_lit 2))).shiftLeft
        (wb.mul (start.add i)))

/-- Loop recurrence for the low table: peel the top step. -/
public theorem lowLoopK_succ (lam ones wc off wb tbl start fuel : Nat) :
    lowLoopK lam ones wc off wb tbl start (fuel + 1)
      = (lowLoopK lam ones wc off wb tbl start fuel).lor
          ((((start + fuel) + off).sub
              ((onesBelowK lam ones wc (start + fuel).succ).mul 2)).shiftLeft
            (wb * (start + fuel))) := rfl

/-- Loop recurrence for the high table: peel the top step. -/
public theorem hiLoopK_succ (x lam ones wc off wb tbl start fuel : Nat) :
    hiLoopK x lam ones wc off wb tbl start (fuel + 1)
      = (hiLoopK x lam ones wc off wb tbl start fuel).lor
          ((((x / (start + fuel)) + off).sub
              ((onesBelowK lam ones wc (x / (start + fuel)).succ).mul 2)).shiftLeft
            (wb * (start + fuel))) := rfl

/-- One block of the recurrence for `L v`. The index `k` in entry 0 gives the quotient `q = v / k`,
which repeats for every index up to `v / q`; the run length times `L q` is added into the running
sum, held as entries 1 and 2 standing for their difference. `L q` comes from entry `q` of `low` when
`q` is at most `rootx`, and from entry `x / q` of `hi` otherwise, both holding `L` offset by `off`.
The step count is exact, so the index stays at or below `v` throughout. -/
@[expose] public noncomputable def blockStepK
    (x v rootx low hi wb off st : Nat) : Nat :=
  let k := st.land ((Nat.shiftLeft (nat_lit 1) (nat_lit 64)).sub (nat_lit 1))
  let q := v.div k
  let run := ((v.div q).sub k).succ
  let val := (q.ble rootx).rec (entryK hi wb (x.div q)) (entryK low wb q)
  ((st.sub k).add (v.div q).succ).add
    (((run.mul val).shiftLeft (nat_lit 64)).add ((run.mul off).shiftLeft (nat_lit 128)))

/-- Perform `fuel` blocks of the recurrence for `L v`. -/
@[expose] public noncomputable def blockLoopK
    (x v rootx low hi wb off st fuel : Nat) : Nat :=
  fuel.rec st fun _ s => blockStepK x v rootx low hi wb off s

/-- Loop recurrence: peel the top block, in the exact form the def uses. -/
public theorem blockLoopK_succ (x v rootx low hi wb off st fuel : Nat) :
    blockLoopK x v rootx low hi wb off st (fuel + 1)
      = blockStepK x v rootx low hi wb off
          (blockLoopK x v rootx low hi wb off st fuel) := rfl

/-! ### Compiled twins

Executable copies of the definitions above, used by the commands to compute the batch literals.
They appear in no proof: a twin that disagreed with its kernel definition would produce a batch
equation that fails its kernel check. -/

public def strideMask (q M rounds : Nat) : Nat := Id.run do
  let mut mask := 1 <<< q
  for i in [0:rounds] do
    let s := q <<< i
    if s ≤ M then
      mask := mask ||| (mask <<< s)
  return mask

public def markStride (lam q M rounds : Nat) : Nat :=
  (lam ^^^ strideMask q M rounds) &&& ((1 <<< (M + 1)) - 1)

public def lamLoop (qs w M rounds lam start fuel : Nat) : Nat := Id.run do
  let mut l := lam
  for i in [0:fuel] do
    l := markStride l (entry qs w (start + i)) M rounds
  return l

public def stEntry (st i : Nat) : Nat := (st >>> (64 * i)) &&& ((1 <<< 64) - 1)

public def blockStep (x v rootx low hi wb off st : Nat) : Nat :=
  let k := st &&& ((1 <<< 64) - 1)
  let q := v / k
  let k2 := v / q
  let run := k2 - k + 1
  let val := if q ≤ rootx then entry low wb q else entry hi wb (x / q)
  ((st - k) + (k2 + 1)) + ((run * val) <<< 64) + ((run * off) <<< 128)

public def blockLoop (x v rootx low hi wb off st fuel : Nat) : Nat := Id.run do
  let mut s := st
  for _ in [0:fuel] do
    s := blockStep x v rootx low hi wb off s
  return s

public def lowLoop (lam ones wc off wb tbl start fuel : Nat) : Nat := Id.run do
  let mut t := tbl
  for i in [0:fuel] do
    let j := start + i
    t := t ||| ((j + off - 2 * onesBelow lam ones wc (j + 1)) <<< (wb * j))
  return t

public def hiLoop (x lam ones wc off wb tbl start fuel : Nat) : Nat := Id.run do
  let mut t := tbl
  for i in [0:fuel] do
    let j := start + i
    t := t ||| ((x / j + off - 2 * onesBelow lam ones wc (x / j + 1)) <<< (wb * j))
  return t

/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` steps from where the
first run stopped. This is the glue that joins consecutive batches. -/
public theorem lamLoopK_add (qs w M rounds lam start a b : Nat) :
    lamLoopK qs w M rounds lam start (a + b)
      = lamLoopK qs w M rounds (lamLoopK qs w M rounds lam start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [lamLoopK_succ]

/-- One chain step: given `L = lamLoopK qs w M lam start (len + rest)` and a kernel-checked batch
equation saying `len` steps from `lam` reach `lam'`, restate `L` as a loop from `lam'` at entry
`start + len` with `rest` steps left. -/
public theorem lamLoopK_chain (L qs w M rounds lam lam' start len rest : Nat)
    (hP : L = lamLoopK qs w M rounds lam start (len.add rest))
    (h : (lamLoopK qs w M rounds lam start len).beq lam') :
    L = lamLoopK qs w M rounds lam' (start.add len) rest := by
  grind [lamLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the blocks, the glue joining consecutive batches. -/
public theorem blockLoopK_add (x v rootx low hi wb off st a b : Nat) :
    blockLoopK x v rootx low hi wb off st (a + b)
      = blockLoopK x v rootx low hi wb off (blockLoopK x v rootx low hi wb off st a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [blockLoopK_succ]

/-- One chain step for the blocks, matching `lamLoopK_chain`. -/
public theorem blockLoopK_chain (L x v rootx low hi wb off st st' len rest : Nat)
    (hP : L = blockLoopK x v rootx low hi wb off st (len.add rest))
    (h : (blockLoopK x v rootx low hi wb off st len).beq st') :
    L = blockLoopK x v rootx low hi wb off st' rest := by
  grind [blockLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the low table, the glue joining consecutive batches. -/
public theorem lowLoopK_add (lam ones wc off wb tbl start a b : Nat) :
    lowLoopK lam ones wc off wb tbl start (a + b)
      = lowLoopK lam ones wc off wb (lowLoopK lam ones wc off wb tbl start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [lowLoopK_succ]

/-- One chain step for the low table, matching `lamLoopK_chain`. -/
public theorem lowLoopK_chain (L lam ones wc off wb tbl tbl' start len rest : Nat)
    (hP : L = lowLoopK lam ones wc off wb tbl start (len.add rest))
    (h : (lowLoopK lam ones wc off wb tbl start len).beq tbl') :
    L = lowLoopK lam ones wc off wb tbl' (start.add len) rest := by
  grind [lowLoopK_add, Nat.beq_eq]

/-- Fuel additivity for the high table, the glue joining consecutive batches. -/
public theorem hiLoopK_add (x lam ones wc off wb tbl start a b : Nat) :
    hiLoopK x lam ones wc off wb tbl start (a + b)
      = hiLoopK x lam ones wc off wb (hiLoopK x lam ones wc off wb tbl start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [hiLoopK_succ]

/-- One chain step for the high table, matching `lamLoopK_chain`. -/
public theorem hiLoopK_chain (L x lam ones wc off wb tbl tbl' start len rest : Nat)
    (hP : L = hiLoopK x lam ones wc off wb tbl start (len.add rest))
    (h : (hiLoopK x lam ones wc off wb tbl start len).beq tbl') :
    L = hiLoopK x lam ones wc off wb tbl' (start.add len) rest := by
  grind [hiLoopK_add, Nat.beq_eq]

end PrimeCert.Polya
