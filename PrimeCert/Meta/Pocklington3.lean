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

/-- Syntax for a `pock3` certificate step: `(N, root, mode, F)`.

- `N`: the number to certify as prime
- `root`: a pseudo-primitive root (for the factored part of `N - 1`)
- `mode`: how to discharge the non-square condition (see `pock3_mode`)
- `F`: the even, fully-factored divisor of `N - 1`, written as `2 ^ e * p₁ ^ e₁ * p₂ * ...`
  (the power of 2 must come first)

The sieve bound `m` (all `l * F + 1` for `1 ≤ l < m` must not divide `N`) is computed
automatically as the smallest valid value. A legacy 5-field form `(N, root, m, mode, F)` with
an explicit `m` still parses and behaves identically.

```lean
-- Certify 73471: root 3, non-square witness 7, F = 2 * 31
pock3 (73471, 3, 7, 2 * 31)

-- With higher power of 2 and multiple odd factors:
pock3 (32560621, 2, 7, 2 ^ 2 * 3 * 29)
```
-/
declare_syntax_cat pock3_spec
/-- The `pock3` step, with the sieve bound `m` computed automatically. -/
syntax "(" num "," num "," pock3_mode "," prime_pow "*" factored ")" : pock3_spec
/-- Legacy `pock3` step with an explicit sieve bound `m` (now computed automatically). -/
syntax "(" num "," num "," num "," pock3_mode "," prime_pow "*" factored ")" : pock3_spec

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

/-- The smallest `m ≥ 1` with `2s + m² < (2F + r)·m + 2` (the `pock3` bound condition), or `0`
if no such `m` exists — which indicates `F` is too small for a valid certificate.

Writing `b := 2F + r`, the condition is `m² - b·m + (2s - 2) < 0`, satisfied on the open interval
between the roots of that quadratic. A solution exists iff the discriminant `b² - 8s + 8` is
positive, and the least one sits just above the lower root `(b - √(b² - 8s + 8)) / 2`. So we
compute it directly with an integer square root and confirm against a tiny window, rather than
scanning — the failure case (`F` too small) returns at once instead of iterating. -/
def minimalSieveBound (twoF r s : ℕ) : ℕ :=
  let b := twoF + r
  if b * b + 8 ≤ 8 * s then 0
  else Id.run do
    let sq := Nat.sqrt (b * b + 8 - 8 * s)
    let cand := (b - sq) / 2
    for m in [max 1 (cand - 3) : cand + 4] do
      if 2 * s + m * m < b * m + 2 then return m
    return 0

def parsePock3Spec : PrimeCertMethod `pock3_spec := fun stx dict ↦ do
  -- Both forms share every field except `m`: the new form computes it, the legacy form
  -- supplies it explicitly.
  let (N, root, mOpt, mode, head, F) ←
    match stx with
    | `(pock3_spec| ($N:num, $root:num, $mode:pock3_mode, $head:prime_pow * $F:factored)) =>
      pure (N, root, (none : Option (TSyntax `num)), mode, head, F)
    | `(pock3_spec| ($N:num, $root:num, $m:num, $mode:pock3_mode, $head:prime_pow * $F:factored)) =>
      logWarning "pock3: the 5-field form `(N, root, m, mode, F)` is deprecated; \
        use the 4-field form `(N, root, mode, F)` instead (m is now computed automatically)"
      pure (N, root, some m, mode, head, F)
    | _ => Elab.throwUnsupportedSyntax
  have (_, headF) := parsePrimePow head
  unless headF.base == 2 do throwError "the first prime in the factorization must be 2"
  let F'E ← parseFactored' F dict
  have N := N.getNat
  have NE : Q(ℕ) := mkNatLit N
  have e := match headF with | .prime _ => 1 | .pow _ e => e
  have eE : Q(ℕ) := mkNatLit e
  have root := root.getNat
  have rootE : Q(ℕ) := mkNatLit root
  let m ← match mOpt with
    | some mStx => pure mStx.getNat
    | none => do
      have (_, oddParsed) := parseFactored F
      have F₀ : ℕ := 2 ^ e * oddParsed.foldl (init := 1)
        (fun acc pp ↦ acc * match pp with | .prime p => p | .pow p k => p ^ k)
      have twoF := 2 * F₀
      have R := (N - 1) / F₀
      have m := minimalSieveBound twoF (R % twoF) (R / twoF)
      if m == 0 then
        throwError "pock3: could not find a valid sieve bound for N = {N}; F may be too small"
      pure m
  have mE : Q(ℕ) := mkNatLit m
  let mode ← parsePock3Mode mode dict
  have pf : Q(Nat.Prime $NE) := mkAppN (mkConst ``pocklington3_certKR)
    #[NE, rootE, mE, eE, F'E, mode, eagerReflBoolTrue]
  return ⟨N, NE, pf⟩

@[prime_cert pock3] def pock3 : PrimeCertExt where
  syntaxName := `pock3_spec
  methodName := ``parsePock3Spec

end PrimeCert.Meta
