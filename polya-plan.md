# Plan: a kernel-certified disproof of Pólya's conjecture

## Goal

Pólya (1919) conjectured that L(n) ≤ 0 for all n ≥ 2, where

    L(n) = Σ_{k=1}^{n} λ(k),    λ = the Liouville function, λ(k) = (−1)^Ω(k),

with Ω(k) the number of prime factors of k counted with multiplicity. The conjecture is false; the
smallest counterexample is N = 906,150,257, where L(N) = 1 (Tanaka 1980).

Target theorems, with L defined over mathlib's `ArithmeticFunction.liouville`:

    def L (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.liouville k
    theorem polya_witness    : L 906150257 = 1
    theorem polya_disproof   : ∃ n, 2 ≤ n ∧ 0 < L n
    theorem polya_conjecture_false : ¬ ∀ n, 2 ≤ n → L n ≤ 0

Everything is checked by the Lean kernel: no `decide`, no `native_decide`, no trusted evaluation.
Proof terms are built explicitly (`mkAppN`, one `reflBoolTrue` per boolean hypothesis), following
the house style established by the sieve work in this repo.

## Method: Möbius/Mertens

Decided against alternatives (brute λ-sieving to N, and a Legendre-style decomposition through the
prime-counting function, whose smooth-sum recursion costs ~30× more operations). The chosen route
is self-contained: **no sieve, no primality testing, and no λ values appear in the computation.**
It reuses the sieve project's *techniques* (checkpointed kernel chains, native twins, packed-Nat
encodings) but none of its objects; deleting every sieve file would not break the mathematics here.

Two identities reduce L(N) to Mertens values M(x) = Σ_{k≤x} μ(k):

1. **λ from μ over squares.** λ(k) = Σ_{d : d²∣k} μ(k/d²). (Both sides multiplicative; check on
   prime powers.) Summing over k ≤ N and exchanging sums:

       L(N) = Σ_{d=1}^{B} M(⌊N/d²⌋),        B = 30102,

   the range ending at B because d² ≤ N exactly when d ≤ B (30102² < N < 30103²).

2. **The Mertens recursion.** Σ_{k=1}^{x} M(⌊x/k⌋) = 1 for x ≥ 1 (count pairs (k, m) with k·m ≤ x
   via Σ_{d∣n} μ(d) = [n = 1], mathlib's `moebius_mul_coe_zeta`). Rearranged:

       M(x) = 1 − Σ_{k=2}^{x} M(⌊x/k⌋),

   which determines M everywhere from M(1) = 1.

### The quotient set, and why it has ~60k elements

Every argument the recursion ever touches has the form ⌊N/j⌋. These take at most 2√N ≈ 60,204
distinct values: for j ≤ √N ≈ 30102 there are at most 30102 values, and for j > √N the quotient
itself is < √N, giving at most 30102 more. The set is closed under the recursion because
⌊⌊N/j⌋/k⌋ = ⌊N/(j·k)⌋ (`Nat.div_div_eq_div_mul`). So one table over these ~60k points suffices.

In the recursion for one entry M(x), equal quotients ⌊x/k⌋ are grouped: quotient value v occurs for
exactly ⌊x/v⌋ − ⌊x/(v+1)⌋ consecutive k, so the sum has ~2√x block terms. Filling the whole table
costs on the order of 10⁷ block terms (Σ_j 2√(N/j) ≈ 2·N^{3/4} plus the small half). That count is
arithmetic; what the kernel makes of it is a measurement question (see gates below).

## Kernel artifacts

- **Packed signed table.** M values at the 60k quotient points, one 32-bit field per entry, offset
  encoding: store M(x) + 2³¹ as a natural number. Since |M(x)| ≤ x < 2³⁰, the offset keeps every
  field positive and every subtraction in the update non-truncating; the required inequality is
  carried inside the loop invariant, not assumed. Two halves, ~120KB each: `small[v]` = M(v) for
  v ≤ B, and `big[j]` = M(⌊N/j⌋) for j ≤ B. Every read happens at a *known divisor index* d
  (read `big[d]` if d ≤ B, else `small[⌊N/d⌋]`), so no inverse-quotient reasoning is ever needed.
- **Field access.** `getF`/`setF` by shift-and-mask, with spec lemmas (`getF_setF_self`,
  `getF_setF_ne`) proved once via `Nat.testBit` decomposition.
- **The M-loop.** Fills the table smallest-point-first; raw `Nat.rec` definition plus a compiled
  twin with identical batch structure; run in batches, each batch a `reflBoolTrue` equation between
  loop-state literals, glued by a fuel-additivity lemma — exactly the `run_sieve_chain` pattern.
- **Assembly fold.** Reads the ~30k entries at square indices d² and accumulates
  Σ_d M(⌊N/d²⌋) as an add-only pair of naturals (positive part, negative part), the signed-value
  idiom ported from ECCompute's `SignedNat`. A final small computation closes `L N = 1`.

## Proof obligations

| Piece | Effort |
|---|---|
| identity 1 (λ = Σ μ(k/d²)) and the sum exchange | medium, mathlib multiplicativity machinery |
| identity 2 (Mertens recursion) | medium, divisor-pair double count |
| `getF`/`setF` spec lemmas | small |
| loop invariant: every filled field decodes to M at its point | **the hardest proof**; structured around a generic "packed table represents g : ℕ → ℤ" predicate |
| assembly: table + identities ⇒ `polya_witness` | small once the above exist |

## Files

```
PrimeCert/Polya/Kernel.lean       -- mathlib-free: SN pair core, getF/setF, M-loop + assembly defs,
                                     peel/additivity lemmas, native twins (imports Lean only)
PrimeCert/Polya/ChainRunner.lean  -- mathlib-free meta: generic chain builder + run_mertens_chain
PrimeCert/Polya/Summatory.lean    -- def L, basic lemmas
PrimeCert/Polya/Identity.lean     -- the two identities
PrimeCert/Polya/TableCorrect.lean -- decode predicate + the loop invariant
PrimeCert/Polya/Main.lean         -- assembly, polya_witness, polya_disproof
PrimeCertTest/PolyaSmall.lean     -- end-to-end at N = 1e5..1e7 against a dev oracle
PrimeCertTest/PolyaDev.lean       -- #eval oracles (dev only, outside the proof import graph)
PrimeCertTest/PolyaFull.lean      -- the N = 906150257 run; CI workflow polya.yml (dispatch-only)
```

## Milestones and measurement gates

- **M0** [metaprogramming, small]: `getF`/`setF` + specs; SN core; calibration probes (single ops
  and mini-loops against 120KB-scale operands, named declarations, `trace.profiler` kernel lines)
  → raw numbers, judged by Bhavik, before anything is committed to.
- **M1** [math, medium — parallel with M2]: `Summatory.lean`, `Identity.lean`.
- **M2** [metaprogramming, medium]: M-loop + twin + chain command. First an **unverified** value at
  N = 1e5..1e7, cross-checked against a compiled oracle — design bugs caught before the hard proof
  is attempted. Then gate **G3**: measured per-batch kernel lines at 1e6/1e7 for the monolithic
  table vs a 32-chunk variant; layout picked from data. Then the full-N table in CI (gate **G4a**).
- **M3** [math, hardest]: the loop invariant; assembly; `polya_witness` at small N first, then at
  N = 906150257 (gate **G4b**).

## Verification protocol

- Dev oracle (compiled trial-division fold for λ, direct summation) vs pipeline output at
  N = 1e5, 1e6, 1e7; one tiny hand-checked value (e.g. L(100)) proved by direct unfolding,
  independent of all machinery.
- Differential micro-tests for `getF`/`setF` and for block boundaries at small x.
- `Nat.sub` audit of `Kernel.lean`: every occurrence needs a named non-truncation lemma.
- Every kernel run recorded with per-declaration `[Kernel]` profiler lines and peak-RSS
  (`/usr/bin/time -v`); the full-N run in a dispatch-only CI workflow on the 16GB runner.

## Risks

1. **Kernel cost of ~10⁷ ops against a ~120KB table** — the one real gamble; measured in week one
   (M0 probes, M2 small-N gates) with the chunked layout as fallback. No timing predictions made.
2. Loop-invariant proof size — mitigated by the M2 unverified-value milestone (definitions known
   correct before proving) and the generic decode predicate.
3. Off-by-ones in block grouping and the Icc 1 n summation convention — differential tests, and
   the convention fixed once in `Summatory.lean`.

## Parked (out of scope for now)

A certified prime-counting table via the `lehmer` branch's φ machinery (its identity layer is
complete there, zero sorries; for x < (B+1)², π(x) = φ(x,B) + π(B) − 1 by `P_eq_zero_of_lt` +
`lehmer_identity`). Revisit after Pólya.
