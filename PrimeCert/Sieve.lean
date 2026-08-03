/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# A kernel-checked Sieve of Eratosthenes

A Sieve of Eratosthenes over the numbers coprime to 6, written so that the Lean kernel can
evaluate it by reduction. The sieve state is one natural number used as a bitset, with one bit
per coprime-to-6 number. Throughout, `M` is the top index of that bitset, so it holds bits
`0 … M` and a bound of `n` gives `M = (n - 1) / 3`.

Widths up to `2^32` are supported (32 doubling rounds in `buildMaskK`, matching the hypothesis
`M < 2^32` in `SieveCorrect`), capping the sieve bound at `n ≈ 3 * 2^32`.

The `run_sieve n` command in `Meta/Sieve` computes the bitset natively in batches, has the kernel
check each, and glues them into an equation `sieveK n sq = <literal>`. Correctness is
`sieveK_testBit_iff` in `SieveCorrect`, which also turns one bit of the certified table into
`Nat.Prime`; the `sieve_lookup` tactic in `Meta/SieveLookup` applies it.
-/

namespace PrimeCert.Sieve

/-- Bit `i` of `b`, as `0` or `1`. `sieve_lookup` reads one entry of the sieve with this. -/
@[expose] public def bitVal (b i : Nat) : Nat := (b.shiftRight i).land 1

/-- The natural number whose binary digits below position `M` are set exactly at positions
`A, A + 2*p, A + 4*p, …` and `B, B + 2*p, B + 4*p, …`. -/
@[expose] public noncomputable def buildMaskK (p M A B : Nat) : Nat :=
  Nat.rec
    ((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B))
    (fun i Mk =>
      ((p.shiftLeft i.succ).ble M).rec Mk
        (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
    32

/-- One sieving step: clear from `bits` the bits at indices of coprime-to-6 multiples of `p`
(the multiples `5*p, 7*p, 11*p, …`). -/
@[expose] public noncomputable def markMaskK (bits p M : Nat) : Nat :=
  bits.sub (bits.land (buildMaskK p M (((p.mul 5).sub 1).div 3) (((p.mul 7).sub 1).div 3)))

/-- The number sitting at coprime-to-6 index `k`: `0↦1, 1↦5, 2↦7, 3↦11, 4↦13, …`. -/
@[expose] public def num (k : Nat) : Nat := (k * 3 + 1) + k % 2

/-- `num` in the raw `Nat` operations the kernel-side defs use. -/
@[expose] public def numK (k : Nat) : Nat := (k.mul 3).succ.add (k.mod 2)

@[simp, grind =] public theorem numK_eq_num (k : Nat) : numK k = num k := rfl

/-- Perform `fuel` sieving steps on the bitset `bits`, scanning indices `start, start+1, …`: at
each index whose bit is still set, clear the bits of that number's coprime-to-6 multiples.
`sieveK` runs this on `initK M`. -/
@[expose] public noncomputable def sieveLoopK (M bits start fuel : Nat) : Nat :=
  fuel.rec bits fun i b =>
      (Nat.ble 1 (b.land (Nat.shiftLeft 1 (start.add i)))).rec b
        (markMaskK b (numK (start.add i)) M)

/-- Coprime-to-6 candidates `0..M`, all set except bit 0 (number 1, not prime). `= 2^(M+1) − 2`. -/
@[expose] public def initK (M : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 (Nat.succ M)) 2

/-- The full sieve bitset for numbers up to `n`: bit `t` is set iff `num t` is prime, given
`n ≤ sqrtN * sqrtN` (`sieveK_testBit_iff` in `SieveCorrect`). -/
@[expose] public noncomputable def sieveK (n sqrtN : Nat) : Nat :=
  sieveLoopK ((n.sub 1).div 3) (initK ((n.sub 1).div 3)) 1 ((sqrtN.sub 1).div 3)

/-- Loop recurrence: peel the top index `start+fuel`, in the exact `Bool.rec` form the def uses. -/
public theorem sieveLoopK_succ (M bits start fuel : Nat) :
    sieveLoopK M bits start (fuel + 1)
      = Bool.rec (sieveLoopK M bits start fuel)
          (markMaskK (sieveLoopK M bits start fuel) (numK (start + fuel)) M)
          (Nat.ble 1 (sieveLoopK M bits start fuel &&& (1 <<< (start + fuel)))) := rfl

/-! ### Compiled twins

Executable copies of the definitions above, used by `run_sieve` to compute the batch literals.
They appear in no proof: a twin that disagreed with its kernel definition would produce a batch
equation that fails its kernel check. -/

public def buildMask (p M A B : Nat) : Nat := Id.run do
  let mut mask := (1 <<< A) ||| (1 <<< B)
  for i in [0:32] do
    let s := p <<< (i + 1)
    if s ≤ M then
      mask := mask ||| (mask <<< s)
  return mask

public def markMask (bits p M : Nat) : Nat :=
  bits - (bits &&& buildMask p M ((p * 5 - 1) / 3) ((p * 7 - 1) / 3))

public def sieveLoop (M bits start fuel : Nat) : Nat := Id.run do
  let mut b := bits
  for i in [0:fuel] do
    let j := start + i
    if b &&& (1 <<< j) ≠ 0 then
      b := markMask b (num j) M
  return b

/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` steps from where the
first run stopped. This is the glue that joins consecutive batches. -/
public theorem sieveLoopK_add (M bits start a b : Nat) :
    sieveLoopK M bits start (a + b)
      = sieveLoopK M (sieveLoopK M bits start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [sieveLoopK_succ]

/-- Replace the loop's starting bitset by a kernel-checked equal literal. `run_sieve` uses this to
enter the chain at `sieveLoopK M (initK M) 1 fuel = sieveLoopK M b₀ 1 fuel`. -/
public theorem sieveLoopK_congr (M b b' start fuel : Nat) (h : b.beq b') :
    sieveLoopK M b start fuel = sieveLoopK M b' start fuel := by
  rw [Nat.eq_of_beq_eq_true h]

/-- One chain step: given `L = sieveLoopK M b start (len + rest)` and a kernel-checked batch
equation saying `len` steps from `b` reach `b'`, restate `L` as a loop from `b'` at index
`start + len` with `rest` steps left. -/
public theorem sieveLoopK_chain (L M b b' start len rest : Nat)
    (hP : L = sieveLoopK M b start (len.add rest))
    (h : (sieveLoopK M b start len).beq b') :
    L = sieveLoopK M b' (start.add len) rest := by
  grind [sieveLoopK_add, Nat.beq_eq]

end PrimeCert.Sieve
