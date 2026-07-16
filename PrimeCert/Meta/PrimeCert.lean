/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Qq
public meta import Lean.Elab.Command

/-! # Extensible framework for primality certificates

The `prime_cert%` elaborator processes a sequence of *step groups* (e.g. `small`, `pock`, `pock3`),
each registered via the `@[prime_cert]` attribute. A `PrimeDict` threads proof terms for
already-certified primes through the ladder so later steps can reference earlier ones.
-/

open Lean Meta Elab Command Qq

namespace PrimeCert.Meta

public section

/-- We store the metavariable assigned to each certified prime. -/
abbrev PrimeDict := Std.HashMap Nat Expr

meta def PrimeDict.getM (dict : PrimeDict) (n : ℕ) : MetaM Expr := do
  let .some entry := dict.get? n
    | throwError s!"Primality not yet certified for {n}"
  return entry

abbrev PrimeCertMethod (syntaxName : Name) :=
  TSyntax syntaxName → PrimeDict → MetaM (Nat × (N : Q(Nat)) × Q(($N).Prime))

/-- A method to climb one step in the ladder, given the dictionary of previously proved primes. -/
structure PrimeCertExt where
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
meta def PrimeCertExt.mkMethod (ext : PrimeCertExt) : ImportM (PrimeCertMethod ext.syntaxName) := do
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

/-- The main primality certificate elaborator.

Syntax: `prime_cert% [group₁, group₂, ...]`

Each group is a registered method name followed by one or more steps:
- `small {p₁; p₂; ...}` — look up pre-proved small primes
- `pock (N, root, F₁)` or `pock {step₁; step₂; ...}` — Pocklington certificates
- `pock3 (N, root, m, mode, F)` — cube-root Pocklington certificates

Groups are processed left-to-right. Within each group, steps are processed in order.
Every certified prime is added to an internal `PrimeDict` so later steps can reference it.
The last prime certified becomes the result.

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
  let mut dict : PrimeDict := ∅
  let mut goal : ℕ := 0
  for group in grps.getElems do
    let ⟨ext, steps⟩ ← parseStepGroup group
    let method ← ext.mkMethod
    for step in steps do
      let ⟨n, nE, pf⟩ ← method step dict
      goal := n
      let mVar ← mkFreshExprMVar q(Nat.Prime $nE) default <| .mkSimple s!"prime_{n}"
      dict := dict.insert n mVar
      mVar.mvarId!.assign pf
  let .some entry := dict.get? goal
    | throwError s!"Primality not certified for {goal}"
  return entry

end

end PrimeCert.Meta
