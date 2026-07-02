/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import PrimeCert.Pocklington3
import PrimeCert.Meta.Pocklington

/-! # The `pock3` certificate method

Syntax and elaboration glue for cube-root Pocklington certificates. The mathematics lives in
`PrimeCert.Pocklington3`; this file parses `(N, root, m, mode, F)` steps and assembles the proof
terms, registering the `pock3` method. It reuses the `prime_pow`/`factored` syntax from
`PrimeCert.Meta.Pocklington`.
-/

namespace PrimeCert.Meta

open Lean Meta Qq

/-- Syntax for the non-square certificate mode in `pock3`:
- A numeric literal `0` means `s = 0`
- A numeric literal `p` (prime, `p > 2`) means `r² - 8s` is a quadratic non-residue mod `p`
- `<` means `r² < 8s` -/
syntax pock3_mode := num <|> "<"

def parsePock3Mode (stx : TSyntax ``pock3_mode) (dict : PrimeDict) :
    MetaM Q(Pocklington3CertMode) := match stx with
  | `(pock3_mode| $n:num) =>
    have n := n.getNat
    if n = 0 then return q(.zero) else do
      have nE : Q(ℕ) := mkNatLit n
      let pf : Q(($nE).Prime) ← dict.getM n
      return q(.prime $nE $pf)
  | `(pock3_mode| <) => return q(.lt)
  | _ => Elab.throwUnsupportedSyntax

/-- Syntax for a `pock3` certificate step: `(N, root, m, mode, F)`.

- `N`: the number to certify as prime
- `root`: a pseudo-primitive root (for the factored part of `N - 1`)
- `m`: sieve bound — all `l * F + 1` for `1 ≤ l < m` must not divide `N`
  (smaller `m` = less sieve work but requires larger `F`)
- `mode`: how to discharge the non-square condition (see `pock3_mode`)
- `F`: the even, fully-factored divisor of `N - 1`, written as `2 ^ e * p₁ ^ e₁ * p₂ * ...`
  (the power of 2 must come first)

```lean
-- Certify 73471: root 3, sieve bound 1, non-square witness 7, F = 2 * 31
pock3 (73471, 3, 1, 7, 2 * 31)

-- With higher power of 2 and multiple odd factors:
pock3 (32560621, 2, 1, 7, 2 ^ 2 * 3 * 29)
```
-/
syntax pock3_spec := "(" num "," num "," num "," pock3_mode "," prime_pow "*" factored")"

def ParsedPrimePow.base : ParsedPrimePow → ℕ
| .prime p => p
| .pow p _ => p

def parsePrimePow' (stx : TSyntax ``prime_pow) (dict : PrimeDict) :
    MetaM Q(PrimeCert.PrimePow) := match stx with
  | `(prime_pow| $p ^ $e) => do
    have p := p.getNat; have pE := mkNatLit p
    have e := e.getNat; have eE := mkNatLit e
    let pf ← dict.getM p
    return mkApp4 (mkConst ``PrimeCert.PrimePow.mk) pE eE pf eagerReflBoolTrue
  | `(prime_pow| $p:num) => do
    have p := p.getNat; have pE := mkNatLit p
    let pf ← dict.getM p
    return mkApp4 (mkConst ``PrimeCert.PrimePow.mk) pE (mkNatLit 1) pf eagerReflBoolTrue
  | _ => Elab.throwUnsupportedSyntax

def parseFactored' (stx : TSyntax ``factored) (dict : PrimeDict) :
    MetaM Q(List PrimeCert.PrimePow) := do
  match stx with
  | `(factored| $pps:prime_pow**) =>
    pps.getElems.foldlM (fun ih pp ↦ return q($(← parsePrimePow' pp dict) :: $ih)) q([])
  | _ => Elab.throwUnsupportedSyntax

-- TODO: special case for `F = 2 ^ e`

def parsePock3Spec : PrimeCertMethod ``pock3_spec := fun stx dict ↦ match stx with
  | `(pock3_spec| ($N:num, $root:num, $m:num, $mode:pock3_mode,
      $head:prime_pow * $F:factored)) => do
    have (_, headF) := parsePrimePow head
    unless headF.base == 2 do throwError "the first prime in the factorization must be 2"
    let F'E ← parseFactored' F dict
    have N := N.getNat
    have NE : Q(ℕ) := mkNatLit N
    have e := match headF with | .prime _ => 1 | .pow _ e => e
    have eE : Q(ℕ) := mkNatLit e
    have root := root.getNat
    have rootE : Q(ℕ) := mkNatLit root
    have m := m.getNat
    have mE : Q(ℕ) := mkNatLit m
    let mode ← parsePock3Mode mode dict
    have pf : Q(Nat.Prime $NE) := mkAppN (mkConst ``pocklington3_certKR)
      #[NE, rootE, mE, eE, F'E, mode, eagerReflBoolTrue]
    return ⟨N, NE, pf⟩
  | _ => Elab.throwUnsupportedSyntax

@[prime_cert pock3] def pock3 : PrimeCertExt where
  syntaxName := ``pock3_spec
  methodName := ``parsePock3Spec

end PrimeCert.Meta
