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

## Building the table below K

Ω(n) counts the prime powers dividing n, so the parity bit of Ω is the exclusive-or over prime
powers q ≤ K of the mask with bits set at q, 2q, 3q, …. One exclusive-or per prime power fixes the
sign of λ for every n ≤ K at once: 74,164 of them at K = 936,411, against 862,477 composites had
each been given a factorization witness instead. Running totals over the bits then give L, one step
per n, retaining values only at indices lying in Q.

The construction is sound only if the supplied list of prime powers is exactly the prime powers
≤ K, so it rests on the kernel sieve on branch `sieve-variants` (bit t of a certified bitset is set
exactly when the corresponding number is prime, with a lookup lemma and caches built to a chosen
bound). K is around 10⁶, inside the range that branch already runs. Landing it is a prerequisite
for this step.

## Evaluating above K

Apply the recurrence to each v = ⌊x/k⌋ with k ≤ x/K, in increasing order of v.

Within one instance k ↦ ⌊v/k⌋ takes O(√v) distinct values, and the k producing quotient q form the
contiguous run ending at ⌊v/q⌋. Walking those runs replaces v terms with O(√v) blocks, each
contributing (run length)·L(q). The value ⌊√v⌋ = a is checked by a² ≤ v < (a+1)².

Each v ∈ Q is one independent obligation: given the certificate, verify that instance. Sixty
thousand checks of a few hundred blocks each, with no single large reduction.

## Files

```
PrimeCert/Polya/Kernel.lean       -- mathlib-free: signed pair core, field get/set, the block walk,
                                     the table builder, compiled twins
PrimeCert/Polya/ChainRunner.lean  -- mathlib-free meta: per-obligation declaration builder
PrimeCert/Polya/Summatory.lean    -- def L, basic lemmas
PrimeCert/Polya/Identity.lean     -- Σ_{k≤v} L(⌊v/k⌋) = ⌊√v⌋ and the recurrence
PrimeCert/Polya/TableCorrect.lean -- the witness check gives λ below K, the prefix sum gives L
PrimeCert/Polya/BlockCorrect.lean -- the run decomposition of Σ_{k=2}^{v} L(⌊v/k⌋)
PrimeCert/Polya/Main.lean         -- assembly, polya_witness, polya_disproof
PrimeCertTest/PolyaSmall.lean     -- end to end at x = 10⁵…10⁷ against a compiled oracle
PrimeCertTest/PolyaDev.lean       -- #eval oracles, outside the proof import graph
PrimeCertTest/PolyaFull.lean      -- the x = 906150257 run, dispatch-only CI workflow
```

## Probes

Each probe times a marginal operation by differencing two declarations that hold everything fixed
except the number of repetitions, so operand construction cancels. Rules: state the operand sizes,
run each declaration at least twice, report every raw `[Kernel]` line and the variance, record peak
resident memory with `/usr/bin/time -v`, and re-run any close call on CI, because the host is
shared.

| probe | declarations | decides |
|---|---|---|
| A. table element | m and 2m exclusive-ors of a stride mask into a K-bit operand, then m and 2m running-total steps | the first half of c₁ |
| B. recurrence block | a fold of m and 2m blocks, each one division, one table read, one multiply-add | the second half of c₁, hence K |
| C. one obligation | a single v ∈ Q verified as one declaration, at v near x and near K | the per-declaration cost and the memory held per obligation |
| D. end to end | the whole certificate at x = 10⁵, 10⁶, 10⁷, value compared against a compiled oracle, no proof attached | feasibility, and the obligation count |

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

## Milestones

- **P** [probes]: A and B fix c₁ and K; C fixes the declaration granularity; D at 10⁵ and 10⁶.
  Raw numbers, judged by Bhavik, before anything downstream is written.
- **M1** [math, parallel with M2]: `Summatory.lean`, `Identity.lean`.
- **M2** [metaprogramming]: the block walk, the table builder, twins, the per-obligation builder.
  Ends with a correct unverified value at 10⁷ and then at x.
- **M3** [math]: the table correctness chain (witness check, prefix sum), the run decomposition,
  assembly, `polya_witness` at 10⁵ first and then at x.

## Risks

1. The sieve dependency: the prime case of the table check rests on branch `sieve-variants`
   landing. Until then the table is verified only below the built-in cache bound.
2. Sixty thousand declarations, each cheap, against one process. Probe C measures whether the
   per-declaration overhead or the block count governs, and the obligations split across files or
   CI jobs if it is the former.
3. Off-by-ones in the run boundaries and in the Icc 1 v summation convention. Met by differential
   tests at small x against the oracle, and by fixing the convention once in `Summatory.lean`.

## Parked

A certified prime-counting table via the `lehmer` branch's φ machinery (its identity layer is
complete there, zero sorries; for x < (B+1)², π(x) = φ(x,B) + π(B) − 1 by `P_eq_zero_of_lt` +
`lehmer_identity`). Revisit after Pólya.

Also parked: carrying the whole computation modulo one word-size prime p > 2x with a final lift
using |L(x)| ≤ x.
