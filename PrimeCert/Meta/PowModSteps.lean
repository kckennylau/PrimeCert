/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.PowMod
public meta import Lean.Elab.Tactic

/-! # The `prove_pow_mod_steps` tactic

An alternative to the pure-reflection `prove_pow_mod`: instead of one `eagerReduce` of `powModTR`,
recurse on the exponent's bits in the elaborator and emit a chain of small `powModAux_*_eq` step
lemmas (from `PrimeCert.PowMod`), each closed by a tiny `rfl`. The kernel then checks ~(bits of
`b`) small steps rather than one giant reduction. Adapted from
`b-mehta/mathlib4@large-prime:Mathlib/V2/PowMod.lean`.
-/

namespace PrimeCert.Tactic.powModSteps

open Lean Meta Elab Tactic

/-- Approach A: given `a, b, c, n`, recurse on the exponent in the elaborator, returning
`(m, mE, ⊢ powModAux a b c n = m)` as a chain of `powModAux_*_eq` steps. -/
meta partial def mkPowModAuxEq (a b c n : Nat) (aE bE cE nE : Expr) : MetaM (Nat × Expr × Expr) :=
  if b = 0 then
    let m : Nat := c % n
    let mE : Expr := mkNatLit m
    return (m, mE, mkApp5 (mkConst ``powModAux_zero_eq) aE cE nE mE eagerReflBoolTrue)
  else if b = 1 then
    let m : Nat := (a * c) % n
    let mE : Expr := mkNatLit m
    return (m, mE, mkApp5 (mkConst ``powModAux_one_eq) aE cE nE mE eagerReflBoolTrue)
  else if b % 2 = 0 then do
    let b' := b / 2
    let a' := a * a % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let (m, mE, eq) ← mkPowModAuxEq a' b' c n a'E b'E cE nE
    return (m, mE, mkApp10 (mkConst ``powModAux_even_eq) aE a'E bE b'E cE nE mE
      eagerReflBoolTrue eagerReflBoolTrue eq)
  else do
    let a' := a * a % n
    let b' := b / 2
    let c' := a * c % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let c'E := mkNatLit c'
    let (m, mE, eq) ← mkPowModAuxEq a' b' c' n a'E b'E c'E nE
    return (m, mE, mkApp5 (mkApp7 (mkConst ``powModAux_odd_eq) aE a'E bE b'E cE c'E nE)
      mE eagerReflBoolTrue eagerReflBoolTrue eagerReflBoolTrue eq)

/-- Given `a, b, n`, return `(m, ⊢ powMod a b n = m)` via approach A. -/
meta def mkPowModEq (a b n : Nat) (aE bE nE : Expr) : MetaM (Nat × Expr × Expr) := do
  let a' := a % n
  let a'E := mkNatLit a'
  let (m, mE, eq) ← mkPowModAuxEq a' b 1 n a'E bE (mkNatLit 1) nE
  return (m, mE, ← mkAppM ``powMod_eq_steps #[aE, eq, eagerReflBoolTrue])

meta def prove_pow_mod_steps_tac (g : MVarId) : MetaM Unit := do
  let t : Expr ← g.getType
  match_expr t with
  | Eq ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let (m', _, eq) ← mkPowModEq a b n aE bE nE
    unless m' = rhs do throwError "attempted to prove {a} ^ {b} % {n} = {rhs} but it's {m'}"
    g.assign eq
  | _ => throwError "not an accepted equality of pow-mod"

/-- Approach A tactic: proves `powMod a b n = m` by building a step chain in the elaborator. -/
elab "prove_pow_mod_steps" : tactic => liftMetaFinishingTactic prove_pow_mod_steps_tac

example : powMod 11 100002 100003 = 1 := by prove_pow_mod_steps
example : powMod 2 12345 100003 = 83832 := by prove_pow_mod_steps

end PrimeCert.Tactic.powModSteps
