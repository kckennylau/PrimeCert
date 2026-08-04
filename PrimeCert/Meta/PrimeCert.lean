/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Qq

/-! # Extensible framework for primality certificates

The `prime_cert%` elaborator processes a sequence of *step groups* (e.g. `small`, `pock`, `pock3`),
each registered via the `@[prime_cert]` attribute. A `PrimeDict` threads proof terms for
already-certified primes through the ladder so later steps can reference earlier ones.
-/

open Lean Meta Elab Command Qq

namespace PrimeCert.Meta

/-- We store the metavariable assigned to each certified prime. -/
public abbrev PrimeDict := Std.HashMap Nat Expr

public meta def PrimeDict.getM (dict : PrimeDict) (n : ℕ) : MetaM Expr := do
  let .some entry := dict.get? n
    | throwError s!"Primality not yet certified for {n}"
  return entry

public abbrev PrimeCertMethod (syntaxName : Name) :=
  TSyntax syntaxName → PrimeDict → MetaM (Nat × (N : Q(Nat)) × Q(($N).Prime))

/-- A method to climb one step in the ladder, given the dictionary of previously proved primes. -/
public structure PrimeCertExt where
  /-- The syntax specific to the certification method -/
  syntaxName : Name
  /-- The function to build the prime proof in the step -/
  methodName : Name
  deriving Inhabited

meta initialize primeCertExt : SimpleScopedEnvExtension
    (String × PrimeCertExt) (Std.HashMap String PrimeCertExt) ←
  registerSimpleScopedEnvExtension {
    addEntry dict entry := dict.insert entry.1 entry.2
    initial := ∅
  }

/-- Attribute to register a new certification method for use in `prime_cert%`.

Usage: `@[prime_cert key] def myExt : PrimeCertExt where ...`

This registers the method under `key`, generating syntax rules so it can be used as
`key spec` or `key {spec₁; spec₂; ...}` inside `prime_cert%`. -/
syntax (name := prime_cert) "prime_cert " ident : attr

/-- Read a `prime_cert` extension from a declaration of the right type. -/
meta def mkPrimeCertExt (n : Name) : ImportM PrimeCertExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck PrimeCertExt opts ``PrimeCertExt n

/-- Read a prime certifying method from a declaration of the right type. -/
meta def PrimeCertExt.mkMethod (ext : PrimeCertExt) :
    ImportM (PrimeCertMethod ext.syntaxName) := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConst (PrimeCertMethod ext.syntaxName) opts ext.methodName

-- Specification for a group of steps in the ladder
declare_syntax_cat step_group

/-- Convert a syntax category name to a ``TSyntax `stx`` dynamically. -/
meta def _root_.Lean.Name.toSyntaxCat (cat : Name) : TSyntax `stx :=
  .mk <| mkNode `Lean.Parser.Syntax.cat #[mkIdent cat, mkNullNode]

/-- If we're given a syntax `pock_spec` for a step in `pock`, we do the following:
```lean
syntax "pock" pock_spec : step_spec
syntax "pock" "{" pock_spec;+ "}" : step_spec
```
-/
meta def mkSyntax (key : String) (spec : Name) : CommandElabM Unit := do
  have spec := spec.toSyntaxCat
  elabCommand =<< `(command| syntax $(quote key):str $spec : step_group)
  elabCommand =<< `(command| syntax $(quote key):str "{" sepBy1($spec,"; ") "}" : step_group)

meta initialize registerBuiltinAttribute {
  name := `prime_cert
  descr := "adds a prime_cert extension"
  applicationTime := .afterCompilation
  add declName stx kind := match stx with
    | `(attr| prime_cert $key) => do
      have key := key.getId.toString
      let ext ← mkPrimeCertExt declName
      liftCommandElabM <| mkSyntax key ext.syntaxName
      primeCertExt.add (key, ext) kind
    | _ => throwUnsupportedSyntax
}

-- section
-- syntax pock_spec := num
-- syntax "pock" pock_spec : step_group
-- syntax "pock" "{" sepBy1(pock_spec,"; ") "}" : step_group
-- #eval `(step_group| pock 3)
-- #eval `(step_group| pock {3; 4})
-- end

meta def parseStepGroup (stx : TSyntax `step_group) :
    CoreM ((e : PrimeCertExt) × Array (TSyntax e.syntaxName)) := do
  match stx.raw with
  | .node _ _ #[.atom _ key, step] => do
    let .some ext := (primeCertExt.getState (← getEnv)).get? key
      | throwError s!"unknown prime_cert extension {key}"
    return ⟨ext, #[.mk step]⟩
  | .node _ _ #[.atom _ key, _, .node _ _ steps, _] => do
    let .some ext := (primeCertExt.getState (← getEnv)).get? key
      | throwError s!"unknown prime_cert extension {key}"
    return ⟨ext, Syntax.TSepArray.getElems <| .mk (sep := ";") steps⟩
  | _ => throwUnsupportedSyntax

/-- Run the certificate ladder `[group₁, group₂, ...]`, returning the dictionary of every
certified prime together with its proof term, plus the last prime certified.

Each group is a registered method name followed by one or more steps:
- `small {p₁; p₂; ...}` — look up pre-proved small primes
- `pock (N, root, F₁)` or `pock {step₁; step₂; ...}` — Pocklington certificates
- `pock3 (N, root, m, mode, F)` — cube-root Pocklington certificates

Groups are processed left-to-right, steps within a group in order. Every certified prime is
added to the `PrimeDict` so later steps can reference it. -/
public meta def runPrimeCertLadder (grps : Array (TSyntax `step_group)) :
    MetaM (PrimeDict × Nat) := do
  let mut dict : PrimeDict := ∅
  let mut goal : ℕ := 0
  for group in grps do
    let ⟨ext, steps⟩ ← parseStepGroup group
    let method ← ext.mkMethod
    for step in steps do
      let ⟨n, nE, pf⟩ ← method step dict
      goal := n
      let mVar ← mkFreshExprMVar q(Nat.Prime $nE) default <| .mkSimple s!"prime_{n}"
      dict := dict.insert n mVar
      mVar.mvarId!.assign pf
  return (dict, goal)

/-- The main primality certificate elaborator.

Syntax: `prime_cert% [group₁, group₂, ...]`; see `runPrimeCertLadder` for the group syntax.
Returns the proof of the last prime certified.

```lean
theorem prime_60digit :
    Nat.Prime 236684654874665389773181956283167565443541280517430278333971 := prime_cert%
  [small {2; 3; 7; 11; 29; 31},
   pock3 (73471, 3, 1, 7, 2 * 31),
   pock3 (32560621, 2, 1, 7, 2 ^ 2 * 3 * 29),
   pock3 (3586530508831189, 2, 1, 11, 2 ^ 2 * 73471),
   pock3 (236684654874665389773181956283167565443541280517430278333971,
     2, 1, 3, 2 * 32560621 * 3586530508831189)]
```
-/
elab "prime_cert% " "[" grps:step_group,+ "]" : term => do
  let (dict, goal) ← runPrimeCertLadder grps.getElems
  let .some entry := dict.get? goal
    | throwError s!"Primality not certified for {goal}"
  return entry

/-- Build a proof term for the primality goal `t` from a completed `PrimeDict`. Handles a
conjunction `A ∧ B`, a `Nat.Prime n`, or the general `Prime n` (for `n : ℕ`), recursing through
conjunctions. Each prime must have been certified by the ladder.

This is the MetaM entry point into the machinery: given a `dict` (built by `runPrimeCertLadder`)
and a goal type, it returns the proof term, so other tactics can reuse it. -/
public meta partial def provePrimeGoal (dict : PrimeDict) (t : Expr) : MetaM Expr := do
  match_expr t with
  | And a b =>
    return mkApp4 (mkConst ``And.intro) a b (← provePrimeGoal dict a) (← provePrimeGoal dict b)
  | Nat.Prime nE =>
    let some n := nE.nat?
      | throwError "prime_cert: the goal `Nat.Prime {nE}` is not a numeral"
    dict.getM n
  | Prime α _ nE =>
    unless α.isConstOf ``Nat do
      throwError "prime_cert: the general `Prime` goal is only supported over ℕ, not {α}"
    let some n := nE.nat?
      | throwError "prime_cert: the goal `Prime {nE}` is not a numeral"
    return mkAppN (mkConst ``Nat.Prime.prime) #[nE, ← dict.getM n]
  | _ =>
    throwError "prime_cert: unsupported goal {t}; expected `Nat.Prime _`, `Prime _`, \
      or a conjunction of these"

/-- The primality certificate tactic. Runs the ladder `[group₁, group₂, ...]` (same syntax as
`prime_cert%`), then closes the goal, which may be `Nat.Prime n`, the general `Prime n`, or a
conjunction of such (each prime must be certified by the ladder).

```lean
theorem prime_pair : Nat.Prime 32560621 ∧ Nat.Prime 73471 := by
  prime_cert [small {2; 3; 7; 29; 31}, pock3 (73471, 3, 1, 7, 2 * 31),
    pock3 (32560621, 2, 1, 7, 2 ^ 2 * 3 * 29)]
```
-/
elab "prime_cert" ppSpace "[" grps:step_group,+ "]" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let (dict, _) ← runPrimeCertLadder grps.getElems
    g.assign (← provePrimeGoal dict (← g.getType))

end PrimeCert.Meta
