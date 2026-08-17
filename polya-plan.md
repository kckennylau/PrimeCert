# Plan: a kernel-certified disproof of Pólya's conjecture

## Goal

Pólya (1919) conjectured that L(n) ≤ 0 for all n ≥ 2, where

    L(v) = Σ_{n=1}^{v} λ(n),    λ = the Liouville function, λ(n) = (−1)^Ω(n),

with Ω(n) the number of prime factors of n counted with multiplicity. The conjecture is false; the
smallest counterexample is x = 906,150,257, where L(x) = 1 (Tanaka 1980).

Target theorems, with L defined over mathlib's `ArithmeticFunction.liouville`:

    def L (v : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 v, ArithmeticFunction.liouville n
    theorem polya_witness    : L 906150257 = 1
    theorem polya_disproof   : ∃ n, 2 ≤ n ∧ 0 < L n
    theorem polya_conjecture_false : ¬ ∀ n, 2 ≤ n → L n ≤ 0

Everything is checked by the Lean kernel: `decide`, `native_decide` and trusted evaluation are all
excluded. Proof terms are built explicitly (`mkAppN`, one `reflBoolTrue` per boolean hypothesis),
following the house style established by the sieve work in this repo.

## The identity

Σ_{d ∣ n} λ(d) is 1 when n is a perfect square and 0 otherwise. Summing that over n ≤ v and
exchanging the order of summation gives

    Σ_{k=1}^{v} L(⌊v/k⌋) = ⌊√v⌋

and isolating k = 1,

    L(v) = ⌊√v⌋ − Σ_{k=2}^{v} L(⌊v/k⌋).

This is proved once as a theorem and then evaluated, so no instance of the recurrence is
reconstructed as a proof term.

## The quotient set

Write x = 906150257 and Q = {⌊x/k⌋ : 1 ≤ k ≤ x}. Then |Q| ≈ 2√x ≈ 60,200, and Q is closed under
v ↦ ⌊v/j⌋ because ⌊⌊x/k⌋/j⌋ = ⌊x/(kj)⌋ (`Nat.div_div_eq_div_mul`), so the recurrence never leaves
Q.

The certificate is the vector of L values on Q. Every entry satisfies |L| < 10⁵.

## Choosing the split

Take K = (x/c₁)^{2/3}, where c₁ is the measured cost of one table element relative to one
recurrence block. The cost is

    c₁·K + Σ_{k ≤ x/K} √(x/k) ≈ c₁·K + 2x/√K

which lands at 3–4·10⁶ blocks. Beyond that K the first term grows linearly while the second falls
as K^{−1/2}.

Settled by measurement: `defaultCutoff x = cbrt (x * x)`, giving K = 936411 at x, and the swept
neighbours 3·10⁵ and 3·10⁶ each cost half again as much. Steps per emitted theorem is 256, and 64
measured slightly faster once theorems are added one at a time, which is unsettled. Every run
generating more than a few thousand theorems wants `set_option Elab.async false`, worth several
times the peak memory at the full target. Numbers in project memory `project_polya_measurements`.

## Building the table below K

Ω(n) counts the prime powers dividing n, so the parity bit of Ω is the exclusive-or over prime
powers q ≤ K of the mask with bits set at q, 2q, 3q, …. One exclusive-or per prime power fixes the
sign of λ for every n ≤ K at once, 74,164 of them at the cutoff 936411. The set bits are then
counted in blocks of 32, and from those counts `L v = v − 2·(set bits below v+1)` gives every running total the
next stage reads.

The construction is sound only if the supplied list of prime powers is exactly the prime powers
≤ K. The sieve's computational core is on `master` as of #98 and its correctness proof lands soon;
its `buildMaskK` and this file's `strideMaskK` are the same doubling construction differing in seed
and first stride, so one definition should serve both. Deriving the list from the certified sieve is
gap 1 in the status section.

## Evaluating above K

Apply the recurrence to each v = ⌊x/k⌋ with k ≤ x/K, in increasing order of v.

Within one instance k ↦ ⌊v/k⌋ takes O(√v) distinct values, and the k producing quotient q form the
contiguous run ending at ⌊v/q⌋. Walking those runs replaces v terms with O(√v) blocks, each
contributing (run length)·L(q). The value ⌊√v⌋ = a is checked by a² ≤ v < (a+1)².

Each v ∈ Q is one independent obligation: given the certificate, verify that instance. Sixty
thousand checks of a few hundred blocks each, with no single large reduction.

## Files

Written:

The whole development is the `Polya` lean_lib, built on demand rather than as a default target.

```
Polya/Defs.lean        -- module, imports nothing: strideMaskK, markStrideK, fieldK, lamLoopK,
                          popc32K, onesLoopK, stFieldK, onesBelowK, lowLoopK, hiLoopK, blockStepK,
                          blockLoopK, the peel/additivity/chain lemmas, and a compiled twin of
                          every kernel-reduced definition
Polya/Meta.lean        -- run_lam n, run_polya x c K, the native prime powers and packing, one
                          emitter per chain, defaultCutoff
Polya/PrimePowers.lean -- bitCheckLoopK, popcLoopK, hpLoopK, their chain lemmas, and the twins
Polya/Summatory.lean   -- def L, basic lemmas
Polya/Identity.lean    -- Σ_{k≤v} L(⌊v/k⌋) = ⌊√v⌋ and the recurrence
Polya/Field.lean       -- reading a packed field: bounds and the value at an index
Polya/BitCheck.lean    -- what surviving the sieve bit checks says about the packed primes
Polya/Complete.lean    -- equal counts leave no prime out of the packing
Polya/PowerPack.lean   -- the packed state of the power collection, and what one loop appends
Polya/Parity.lean      -- the stride masks mark the multiples
Polya/CardFactors.lean -- the prime powers dividing n number Ω n
Polya/LamCorrect.lean  -- lamK is the parity of Ω
Polya/PopCount.lean    -- popc32K counts set bits
Polya/Ones.lean        -- onesK holds the running counts
Polya/Count.lean       -- L from a count of odd Ω
Polya/Tables.lean      -- lowLoopK and hiLoopK hold values of L
Polya/Runs.lean        -- the run decomposition of Σ_{k=2}^{v} L(⌊v/k⌋)
Polya/TableSpec.lean   -- the packed table holds exactly the prime powers
Polya/BlockCorrect.lean -- the invariant of blockLoopK over its packed state
Polya/Recursion.lean   -- the two tables answer every read one block makes
Polya/Main.lean        -- the three lemmas the emitted run applies, one per stage
PrimeCertTest/PolyaCertCheck.lean -- the run at 10^6, with L_million read off it
PrimeCertTest/PolyaFull.lean      -- the x = 906150257 run, polya_witness, polya_disproof,
                                     polya_conjecture_false
```

To write:

```
.github/workflows -- a dispatch-only job for the run at x
```

## Status

Done: `PrimeCertTest/PolyaFull.lean` builds on CI, printing `L(906150257) = 1` and proving
`polya_witness`, `polya_disproof` and `polya_conjecture_false` over `ArithmeticFunction.liouville`,
on `propext`, `Classical.choice` and `Quot.sound` alone. Where each of the four gaps it rests on
stands:

1. **The prime powers come from the sieve, proved.** `isPrimePowerTable_of_checks` in
   `Polya/TableSpec.lean` turns what the three loops check into `IsPrimePowerTable`. It rests on
   `bitCheckLoopK_spec` (`Polya/BitCheck.lean`, what a surviving flag forces), `primeBlock_spec`
   (`Polya/Complete.lean`, equal counts leave no prime out), and `hpLoopK_spec` with `hpVal_iff`
   (`Polya/HigherPowers.lean`, the walk collects the powers with base 2 or 3 and those with
   exponent at least two), over the packed state of `Polya/PowerPack.lean`.
2. **The parity table, proved.** `testBit_lamK` in `Polya/LamCorrect.lean`: bit `n` is set exactly
   when `Ω n` is odd, for `1 ≤ n ≤ M`, given `IsPrimePowerTable`. It rests on the stride masks
   marking the multiples (`Polya/Parity.lean`) and on the prime powers dividing `n` numbering `Ω n`
   (`Polya/CardFactors.lean`).
3. **The counts and the value tables, proved.** `popc32K_eq_bitSum` in `Polya/PopCount.lean`
   (the byte-wise argument, no `decide` over the word), `fieldK_onesK` and `onesBelowK_eq` in
   `Polya/Ones.lean`, `lowLoopK_spec`, `hiLoopK_spec_start` and `lowVal_eq_L` in
   `Polya/Tables.lean`.
4. **The block loop, proved.** `blockLoopK_sum` in `Polya/BlockCorrect.lean`: a run of blocks
   ending at index `v + 1` with the second accumulator at `off * (v - 1)` has covered `2 … v`, so
   the accumulators differ by the sum in the recurrence. It rests on the run decomposition of
   `Polya/Runs.lean`.

The recurrence itself is proved: `Polya/Summatory.lean` defines `L`, and `Polya/Identity.lean`
gives `∑_{k=1}^{v} L ⌊v/k⌋ = ⌊√v⌋` and `L_eq_sqrt_sub`, off the divisor sum of `λ` being the
indicator of the squares.

`Polya/Recursion.lean` joins the last two: the two tables answer every read a block makes
(`blockValues_of_tables`), the value a run of blocks produces goes back into the high table one
index lower (`isHiTable_write`), and `L_eq_of_blockLoopK` reads `L v` off a finished run.

`Polya/Main.lean` holds the three lemmas a run applies: `tables_of_data` turns the equations of the
six loops into the two table invariants, `isHiTable_step` extends the high table to one more index,
and `L_eq_of_final` reads `L x` off the last run of blocks. Each carries its numeric side conditions
as one decidable predicate over the emitted literals (`SetupOK`, `StepOK`, `FinalOK`), so one
kernel-checked theorem per stage covers the packing of a block state, the square root of an
argument, the value written into the table, and the widths and ranges the invariants need.
`run_polya x` walks `j` from `x / cutoff` down to 1, one application per index, and emits
`polyaValue : L x = p - q`.

## Gap 1: the prime powers come from the sieve

### What the sieve supplies

`PrimeCert.Sieve.sieveK n sqrtN` is a bitset over the numbers coprime to 6, indexed by
`num t = 3*t + 1 + t % 2` (so `num 1 = 5`, `num 2 = 7`). `sieveK_testBit_iff` states that bit `t` is
set iff `num t` is prime, for `1 ≤ t ≤ (n-1)/3` with `num t ≤ n ≤ sqrtN * sqrtN`. It is an
equivalence, so a clear bit gives "not prime", which is what completeness of the list rests on.
`run_sieve n` emits a literal and `sieveData : sieveK n (Nat.sqrt n + 1) = sieveLit`, and registers
the pair, so `run_polya` reads the cutoff's sieve out of that registry and calls `run_sieve` when no
cache covers the cutoff.

### The statement gap 2 consumes

Over the emitted table arguments `qs`, `w`, `cnt` and the cutoff `M`:

```
∀ q, (IsPrimePow q ∧ q ≤ M) ↔ ∃ i < cnt, fieldK qs w i = q
∀ i j, i < cnt → j < cnt → fieldK qs w i = fieldK qs w j → i = j
```

Injectivity is not decoration: the parity table is one exclusive-or per field, so a field appearing
twice cancels and the table is wrong.

### What the kernel checks

The strides stay computed by the metaprogram and arrive packed as before, in two blocks: the primes
from 5 upward in increasing order, then 2, 3 and the powers whose exponent is at least two. Three
loops in `Polya/PrimePowers.lean` tie both blocks to the sieve, each batched in the house
style with a peel lemma by `rfl`, fuel additivity by induction, and a chain lemma.

- `bitCheckLoopK` tests the first block field by field: the value is 1 or 5 modulo 6, its sieve index
  `(q-1)/3` exceeds the previous field's, and its sieve bit is set. The state carries that index
  above bit 0 and a flag in bit 0, which survives only when every test passes.
- `popcLoopK` adds up the sieve's set bits over 32-position blocks through `popc32K`. The run
  demands that total equal the number of fields in the first block.
- `hpLoopK`, over sieve positions `1 … (√M - 1)/3`, collects each prime's powers through `powLoopK`,
  starting from a state seeded with the powers of 2 and of 3 and joined to the chain by
  `hpLoopK_congr`. The run demands its output equal the packed second block.

Why the three suffice: a set bit gives primality by the forward direction of `sieveK_testBit_iff`,
rising indices make the first block injective, and a count equal to the sieve's own set-bit total
leaves no prime out, since an injection into a set of that size is onto. Every prime power with
exponent at least two has base at most `√M`, which is the range `hpLoopK` walks.

Measured at the cutoff on one CI machine, this design ran fastest of the five tried; numbers and the
alternatives are in project memory `project_polya_measurements`.

### The proof to write

Canonical base and exponent of a prime power come from
`IsPrimePow.minFac_pow_factorization_eq : q.minFac ^ q.factorization q.minFac = q`.

- From the surviving flag: each field of the first block is prime, by `num_wheel` and the forward
  direction of `sieveK_testBit_iff`, and the fields strictly increase.
- From the count: the fields of the first block are every prime in `[5, M]`. Cardinality closes it,
  with the set-bit count of the sieve equal to that of the primes by `popcLoopK`'s own lemma.
- From `hpLoopK`: an induction over the positions it walks, whose invariant names the powers
  collected so far by base and exponent, giving the second block exactly. Distinct fields follow
  from distinct bases and `Nat.pow_right_injective`.

Reading fields back out of a packed number is shared with gap 3, so those lemmas go in their own
file.

### What the sieve supplies now

`master` carries `IsSieve n lit`, which says that for every index `t ≠ 0` whose number `num t` is at
most `n`, bit `t` of `lit` is set exactly when `num t` is prime, and `sieveK_lt`, which bounds a
sieve below `2 ^ ((n-1)/3 + 1)` so a count over whole 32-position blocks sees nothing above the
range. `run_sieve n` emits `sieveBits_n`, `sieveK_eq_n` and `isSieve_n`, and registers all three.
The proofs below take `IsSieve` as their hypothesis. `num` stays exposed, so its residues, its lower
bound of 5, its monotonicity, its injectivity and `num ((q-1)/3) = q` are each one line here.

### Files

```
Polya/PrimePowers.lean  -- bitCheckLoopK, popcLoopK, hpLoopK, their chain lemmas
Polya/BitCheck.lean     -- what the surviving flag says about the packed primes
Polya/Complete.lean     -- equal counts leave no prime out
Polya/PowerPack.lean    -- the packed state of the power collection
Polya/Field.lean        -- reading a packed field: bounds and the value at an index
Polya/Meta.lean         -- the sieve-cache lookup, the two blocks, one emitter per chain
```

The loops, their emitters and the batching are written and run: `run_polya` prints the published
value at `10^6` and `10^7` with the checks inside it. The theorems above wait on the sieve's
correctness proof reaching `master`.

## Milestones

- **P** [probes]: done. Sweeps of the split point and of steps per theorem, and a comparison of six
  proposed speed changes; four of the six are merged.
- **M2** [metaprogramming]: done. The value at 10⁶, 10⁷, 10⁸ matches published tables and the run at
  x gives 1.
- **M1** [math]: done. `Summatory.lean`, `Identity.lean`.
- **M3** [math]: done. The table correctness chain, the run decomposition, the assembly, and
  `polya_witness` at 10⁶ locally and at x on CI.

## Risks

1. The sieve dependency, now the largest open risk: gap 1 of the status section rests on the
   sieve's correctness proof reaching `master`.
2. The count of generated theorems, about 14,000 at x. Measured: with them queued, peak memory rises
   steeply as that count grows, reaching 13 GB at a split of 2·10⁵; with each finished before the
   next it stays near 2 GB across every setting tried.
3. Off-by-ones in the run boundaries and in the Icc 1 v summation convention. Met by differential
   tests at small x against the oracle, and by fixing the convention once in `Summatory.lean`.

## Parked

A certified prime-counting table via the `lehmer` branch's φ machinery (its identity layer is
complete there, zero sorries; for x < (B+1)², π(x) = φ(x,B) + π(B) − 1 by `P_eq_zero_of_lt` +
`lehmer_identity`). Revisit after Pólya.

Also parked: carrying the whole computation modulo one word-size prime p > 2x with a final lift
using |L(x)| ≤ x.
