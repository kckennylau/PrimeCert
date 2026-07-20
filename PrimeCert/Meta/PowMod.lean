/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.PowMod
public meta import Lean.Elab.Tactic

/-! # The `prove_pow_mod` tactic

Elaboration-time evaluation of `a ^ b % n`, producing a kernel proof via `powModTR` and
`eagerReduce`. Split out from `PrimeCert.PowMod` so the computational core stays free of
metaprogramming.
-/

namespace Tactic.powMod

open Lean Meta Elab Tactic

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
meta def mkPowModEq' (a b n : Nat) (aE bE nE : Expr) : MetaM (Nat × Expr × Expr) := do
  let m := powModTR' a b n
  let mE := mkNatLit m
  return (m, mE, mkApp5 (mkConst ``powMod_eq_of_powModTR) aE bE nE mE eagerReflBoolTrue)

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
meta def provePowModEq' (a b n m : Nat) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq' a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
meta def provePowModNe' (a b n m : Nat) (aE bE nE mE : Expr) : MetaM Expr := do
  let m' := powModTR' a b n
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  return mkApp5 (mkConst ``powMod_ne_of_powModTR) aE bE nE mE eagerReflBoolFalse

meta def prove_pow_mod_tac (g : MVarId) : MetaM Unit := do
  let t : Expr ← g.getType
  match_expr t with
  | Eq ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModEq' a b n rhs aE bE nE
    g.assign pf
  | Ne ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModNe' a b n rhs aE bE nE rhsE
    g.assign pf
  | _ => throwError "not an accepted expression"

/-- Tactic to close goals about modular exponentiation. Handles two goal shapes:

- `powMod a b n = m` — proves the equality by computing `a ^ b % n` at elaboration time
- `powMod a b n ≠ m` — proves the disequality similarly

All of `a`, `b`, `n`, `m` must be numeric literals. The computation uses `powModTR'`
(the `partial_fixpoint` version) at elaboration time, then produces a kernel proof via
`powModTR` and `eagerReduce`.

```lean
example : powMod 11 100002 100003 = 1 := by prove_pow_mod
example : powMod 2 100002 100003 ≠ 1 := by prove_pow_mod
```
-/
elab "prove_pow_mod" : tactic => liftMetaFinishingTactic prove_pow_mod_tac

end Tactic.powMod
