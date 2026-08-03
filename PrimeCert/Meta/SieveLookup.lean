/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrimeCert.SieveCorrect
import PrimeCert.SieveBase
import PrimeCert.Meta.PrimeCert

/-! # Reading a prime off the sieve cache

`mkSieveLookup` builds the proof term; the `sieve_lookup` tactic and the `sieve` certificate
method both call it. The cache from `PrimeCert.SieveBase` covers numbers up to `100000`; beyond
that a caller adds one with `run_sieve`.
-/

namespace PrimeCert.Sieve

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

/-- A proof of `Nat.Prime p`, read off the sieve cache in the environment; `2` and `3` come from
`Nat.prime_two` and `Nat.prime_three`, which the sieve's numbers skip. Fails if `p` shares a factor
with 6, lies outside the cache, or has its bit clear (i.e. is composite). -/
def mkSieveLookup (p : Nat) : MetaM Expr := do
  if p == 2 then return mkConst ``Nat.prime_two
  if p == 3 then return mkConst ``Nat.prime_three
  if p < 5 ∨ (p % 6 != 1 && p % 6 != 5) then
    throwError "sieve lookup: {p} must be 2, 3, or coprime to 6"
  let t := (p - 1) / 3
  let some cache ← findSieveCache p
    | throwError "sieve lookup: no sieve cache covers {p}; the caches in scope are {
        (← sieveCaches).map fun c => (c.lo, c.hi)}"
  let some ci := (← getEnv).find? cache.dataName
    | throwError "sieve lookup: {cache.dataName} is registered but absent"
  let args := ci.type.getAppArgs
  unless args.size == 3 && args[1]!.isAppOf ``sieveK do
    throwError "sieve lookup: {cache.dataName} has unexpected shape: {ci.type}"
  let sargs := args[1]!.getAppArgs
  let some litVal := (← getEnv).find? cache.litName >>= (·.value?) >>= (·.rawNatLit?)
    | throwError "sieve lookup: {cache.litName} does not hold a raw literal"
  unless (litVal >>> t) &&& 1 == 1 do
    throwError "sieve lookup: bit {t} of the sieve is clear, so {p} is not prime"
  return mkAppN (mkConst ``prime_of_sieve_eq)
    #[sargs[0]!, sargs[1]!, mkRawNatLit t, mkConst cache.litName, mkRawNatLit p,
      mkConst cache.dataName,
      Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
      Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue]

/-- Close a `Nat.Prime p` goal with `mkSieveLookup`. -/
elab "sieve_lookup" : tactic => withMainContext do
  let g ← getMainGoal
  let_expr Nat.Prime p := ← instantiateMVars (← g.getType)
    | throwError "sieve_lookup: goal is not `Nat.Prime _`"
  let some pv := p.nat?
    | throwError "sieve_lookup: the argument of `Nat.Prime` is not a numeral"
  g.assign (← mkSieveLookup pv)
  replaceMainGoal []

/-- Syntax for the `sieve` method: a numeric literal `n`, looked up in the sieve cache.

```lean
-- In a prime_cert call, after `run_sieve`:
prime_cert [sieve {1009; 1999}, ...]
```
-/
syntax sieve_spec := num

def mkSieveProof : Meta.PrimeCertMethod ``sieve_spec := fun stx _ ↦ match stx with
  | `(sieve_spec| $n:num) => do
    have n := n.getNat
    return ⟨n, mkNatLit n, ← mkSieveLookup n⟩
  | _ => throwUnsupportedSyntax

@[prime_cert sieve] def PrimeCertExt.sieve : Meta.PrimeCertExt where
  syntaxName := ``sieve_spec
  methodName := ``mkSieveProof

end PrimeCert.Sieve
