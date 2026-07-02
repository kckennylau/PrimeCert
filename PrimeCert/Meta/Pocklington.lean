/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import PrimeCert.Pocklington

/-! # The `pock` certificate method

Syntax and elaboration glue for classic Pocklington certificates. The mathematics lives in
`PrimeCert.Pocklington`; this file parses `(N, root, F₁)` steps and assembles the proof terms,
registering the `pock` method and providing the `pock%` convenience elaborator.
-/

namespace PrimeCert.Meta

open Lean Meta Qq

/-- A prime power is represented by either `p ^ e` or `p`. -/
syntax prime_pow := num (" ^ " num)?

inductive ParsedPrimePow : Type
  | prime (p : ℕ) | pow (p e : ℕ)

instance : ToMessageData ParsedPrimePow where
  toMessageData x := match x with
    | .prime p => m!"{p}"
    | .pow p e => m!"{p}^{e}"

def parsePrimePow (stx : TSyntax ``prime_pow) : Q(Nat) × ParsedPrimePow :=
  match stx with
  | `(prime_pow| $p:num^$e:num) =>
      have p := p.getNat
      have e := e.getNat
      (mkApp2 (mkConst ``Nat.pow) (mkNatLit p) (mkNatLit e), .pow p e)
  | `(prime_pow| $p:num) =>
      have p := p.getNat
      (mkNatLit p, .prime p)
  | _ => (mkNatLit 0, .prime 0)

/-- A full factorisation of a number, written like `3 ^ 4 * 29 * 41`. -/
syntax factored := sepBy1(prime_pow," * ")

def parseFactored (stx : TSyntax ``factored) : Q(Nat) × Array ParsedPrimePow :=
  match stx with
  | `(factored| $head * $body**) =>
    have head := parsePrimePow head
    have body := body.getElems.map parsePrimePow
    ((body.map (·.1)).foldl (fun ih new ↦ (mkApp2 (mkConst ``Nat.mul) ih new)) head.1,
      #[head.2] ++ body.map (·.2))
  | `(factored| $head:prime_pow) =>
    have head := parsePrimePow head
    (head.1, #[head.2])
  | _ => (mkNatLit 0, #[])

def mkPockPred (N a F₁ : Q(Nat)) (steps : Array ParsedPrimePow) (dict : PrimeDict) :
    MetaM Q(PocklingtonPred $N $a $F₁) := do
  if h : steps.size = 0 then return mkConst ``PocklingtonPred.one
  else
    have head : Expr := ← match steps[0] with
    | .prime p => do
      mkAppOptM ``PocklingtonPred.base #[N, a, mkNatLit p, ← dict.getM p,
        eagerReflBoolTrue, eagerReflBoolTrue]
    | .pow p e => do
      mkAppOptM ``PocklingtonPred.base_pow #[N, a, mkNatLit p, mkNatLit e, ← dict.getM p,
        eagerReflBoolTrue, eagerReflBoolTrue]
    (steps.drop 1).foldlM (fun ih step ↦ match step with
      | .prime p => do
        mkAppM ``PocklingtonPred.step #[← dict.getM p, ih,
          eagerReflBoolTrue, eagerReflBoolTrue]
      | .pow p e => do
        mkAppOptM ``PocklingtonPred.step_pow #[N, a, none, mkNatLit p, mkNatLit e,
          ← dict.getM p, ih, eagerReflBoolTrue, eagerReflBoolTrue]) head

/-- Syntax for a `pock` certificate step: `(N, root, F₁)`.

- `N`: the number to certify as prime
- `root`: a value satisfying `root ^ (N-1) ≡ 1 (mod N)` and the GCD conditions
- `F₁`: a fully-factored divisor of `N - 1` with `F₁ > √N`, written as `p₁ ^ e₁ * p₂ * ...`

All prime factors appearing in `F₁` must already be in the `PrimeDict` (certified by
earlier `small` or `pock` steps).

```lean
-- In a pock% or prime_cert% call:
pock (339392917, 2, 3 ^ 4 * 29 * 41)
pock (16290860017, 5, 339392917)
```
-/
syntax pock_spec := num <|> ("(" num ", " num ", " factored ")")

def parsePockSpec : PrimeCertMethod ``pock_spec := fun stx dict ↦ do
  match stx with
  | `(pock_spec| ($N:num, $a:num, $F₁:factored)) =>
      have Nnat := N.getNat
      have N : Q(Nat) := mkNatLit Nnat
      have a : Q(Nat) := mkNatLit a.getNat
      have (F₁, steps) := parseFactored F₁
      have pred := ← mkPockPred N a F₁ steps dict
      have pf : Q(Nat.Prime $N) := ← mkAppM ``pocklington_certifyKR
        #[N, a, F₁, pred, eagerReflBoolTrue, eagerReflBoolTrue,
          eagerReflBoolTrue, eagerReflBoolTrue]
      return ⟨Nnat, N, pf⟩
  | _ => Elab.throwUnsupportedSyntax

@[prime_cert pock] def PrimeCertExt.pock : PrimeCertExt where
  syntaxName := ``pock_spec
  methodName := ``parsePockSpec

end Meta

open Meta

/-- Convenience elaborator combining `small` and `pock` steps into a single term.

Syntax: `pock% [small_primes; pock_steps]`

- Before the `;`: comma-separated small prime literals whose primality is already known
  (looked up as `PrimeCert.prime_<n>` declarations, e.g. `PrimeCert.prime_31`).
- After the `;`: comma-separated Pocklington steps `(N, root, F₁)` where:
  - `N` is the number to certify
  - `root` is a pseudo-primitive root of `N`
  - `F₁` is a factored divisor of `N - 1` with `F₁ > √N`, written as `p₁ ^ e₁ * p₂ * ...`

Steps are processed in order; each step can reference primes certified by earlier steps.
The last step's `N` becomes the certified prime.

```lean
-- Certify 31: declare small primes 2, 3; then one Pocklington step
theorem prime_31 : Nat.Prime 31 := pock% [2, 3; (31, 3, 2 * 3)]

-- Multi-step ladder: small primes, then intermediate, then target
theorem prime_16290860017 : Nat.Prime 16290860017 :=
  pock% [3, 29, 41; (339392917, 2, 3 ^ 4 * 29 * 41), (16290860017, 5, 339392917)]
```
-/
scoped elab "pock%" "[" heads:small_spec,+ ";" steps:pock_spec,+ "]" : term => do
  Lean.Elab.Term.elabTerm (← `(prime_cert% [small {$heads;*}, pock {$steps;*}])) none

end PrimeCert
