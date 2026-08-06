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

```
PrimeCert/Polya.lean       -- module, imports nothing: strideMaskK, markStrideK, fieldK, lamLoopK,
                              popc32K, onesLoopK, stFieldK, onesBelowK, lowLoopK, hiLoopK,
                              blockStepK, blockLoopK, the peel/additivity/chain lemmas, and a
                              compiled twin of every kernel-reduced definition
PrimeCert/Meta/Polya.lean  -- run_lam n, run_polya x c K, the native prime powers and packing,
                              one emitter per chain, defaultCutoff
```

To write, one file per gap in the status section:

```
PrimeCert/Polya/Summatory.lean    -- def L, basic lemmas
PrimeCert/Polya/Identity.lean     -- Σ_{k≤v} L(⌊v/k⌋) = ⌊√v⌋ and the recurrence
PrimeCert/Polya/TableCorrect.lean -- the prime powers come from the sieve; lamK is the parity of Ω;
                                     onesK counts set bits; lowLoopK and hiLoopK hold L
PrimeCert/Polya/BlockCorrect.lean -- the run decomposition of Σ_{k=2}^{v} L(⌊v/k⌋)
PrimeCert/Polya/Main.lean         -- assembly, polya_witness, polya_disproof
PrimeCertTest/PolyaOracle.lean    -- independent compiled implementations, kept untracked for now
PrimeCertTest/PolyaFull.lean      -- the x = 906150257 run, dispatch-only CI workflow
```

## Status

The computation runs and prints `L(906150257) = 1`, with every batch equation checked by the kernel.
That establishes that the numbers are what the definitions compute, and nothing about the Liouville
function: no theorem yet connects any definition here to `ArithmeticFunction.liouville`, so the
printed value is not evidence that the conjecture fails. Four things stand between the two:

1. The prime powers are supplied by `primePowers` in the metaprogram and enter the emitted
   statements as a literal. A list containing a composite, or missing a prime, passes every kernel
   check and gives a wrong table. This is the sieve dependency below.
2. Bit `n` of `lamK` is claimed to be the parity of `Ω n`.
3. A field of `onesK` is claimed to count set bits below a position, and the fields of `lowLoopK`
   and `hiLoopK` to hold values of `L`.
4. `blockLoopK` is claimed to accumulate `Σ_{k≥2} L(⌊v/k⌋)`, and the identity giving `L v` from it
   is unstated.

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

### Generate rather than validate

Validating the existing literal needs, between consecutive entries, a witness that each intervening
number is not a prime power, which is a witness per number up to the cutoff. Generating the list
inside the kernel from the sieve bits gets completeness from a single induction over the index range
instead. Two ways to generate:

1. A generator loop builds the packed list from the sieve literal, and the parity loop stays exactly
   as it is, with its measured tuning intact. One new loop, one new literal.
2. The parity loop reads the sieve bits directly and skips clear ones, so the list never exists.
   One stage fewer, at the price of changing the hot loop, running it over every candidate index
   rather than every prime power, and nesting the powers of each base inside its fuel.

Take route 1.

### Shape of the generator

State layout: the count in the low 64 bits, the packed fields above bit 64, so appending field `k`
is `state + (q <<< (64 + w * k)) + 1` and reading the count is one `land`. This is the packed-state
pattern `blockStepK` already uses.

One definition `ppLoopK sieve M e state start fuel` walks candidate indices; at each index whose bit
is set it appends `p`, `p^2`, … up to `min` of `M` and exponent fuel `e`, through an inner loop.
It runs twice:

- indices `1 … (Nat.sqrt M - 1)/3` with `e` at `Nat.log2 M + 1`, covering every base whose higher
  powers stay below the cutoff, 322 steps at the cutoff 936411;
- the remaining indices up to `(M-1)/3` with `e = 1`, sound because `p > Nat.sqrt M` gives
  `p * p > M`, 312,136 steps.

Bases 2 and 3 sit outside the sieve's index range, so a seed emits `2, 4, 8, …` and `3, 9, 27, …`
first, with the primality of 2 and 3 by `norm_num`.

Each of the two runs is batched in the house style: peel by `rfl`, fuel additivity by induction,
chain lemma, one emitter, batch length swept like every other stage.

### The proof

Canonical base and exponent of a prime power come from
`IsPrimePow.minFac_pow_factorization_eq : q.minFac ^ q.factorization q.minFac = q`. Loop invariant
after processing indices `[1, t)`: the fields hold exactly those `q ≤ M` with `IsPrimePow q` whose
base is 2, 3, or `num s` for a processed `s`, each once. Soundness of an appended field is the
sieve's forward direction; completeness is its backward direction together with
`num ((q - 1) / 3) = q` for `q` coprime to 6 (`num_wheel`, `prime_ge5_mod6`), which puts every prime
in `[5, M]` at an index the loop visits. Injectivity splits on the base: distinct bases give
distinct values, equal bases give equal exponents by `Nat.pow_right_injective`.

Reading fields back out of the accumulator is shared with gap 3, so the append and read lemmas, with
the invariant that bits above `w * k` are clear and every entry is below `2 ^ w`, go in their own
file.

### Order

The native `primePowers` sorts its output; the generator emits by base. Drop the `qsort` so the two
agree. No order-independence lemma is needed, because the table equation is recomputed for whichever
list the generator produces.

### Prerequisites in the sieve file

`num_wheel`, `prime_ge5_mod6`, `num_inj`, `num_mod6` and `five_le_num` carry no `public` marker, so
the module system hides them downstream. Gap 1 needs them exported.

### Files and order of work

```
PrimeCert/Polya/Field.lean        -- packing: append, read back, field bounds
PrimeCert/Polya/PrimePowers.lean  -- ppLoopK, its chain lemmas, the two theorems above
PrimeCert/Meta/Polya.lean         -- emitPPChain, the sieve-cache lookup, drop the qsort
```

The loop, its emitter and the batching are independent of the sieve's correctness proof and can be
written and checked now against the native list at `M = 10^3` and `10^5`. The mathematical bridge
lands after the sieve does. Step counts and the literal's width (74,164 fields of 20 bits at the
cutoff) say nothing about cost; measure the new stage in CI before it goes in.

## Milestones

- **P** [probes]: done. Sweeps of the split point and of steps per theorem, and a comparison of six
  proposed speed changes; four of the six are merged.
- **M2** [metaprogramming]: done. The value at 10⁶, 10⁷, 10⁸ matches published tables and the run at
  x gives 1.
- **M1** [math, next]: `Summatory.lean`, `Identity.lean`.
- **M3** [math]: the table correctness chain, the run decomposition, assembly, `polya_witness` at
  10⁵ first and then at x.

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
