/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeCert
public meta import PrimeCert.Meta.SieveCache
import PrimeCert.SieveCorrect
meta import PrimeCert.SieveBase

/-! # Reading a prime off the sieve cache

`mkSieveLookup` builds the proof term and the `sieve_lookup` tactic calls it, choosing the
tightest sieve in scope that covers the number. `run_sieve` adds a wider one.
-/

namespace PrimeCert.Sieve

open Lean Elab Tactic

/-- A proof of `Nat.Prime p`, read off a sieve in the environment. `2` and `3` come from
`Nat.prime_two` and `Nat.prime_three`, the primes a mod-6 sieve skips. -/
meta def mkSieveLookup (p : Nat) : MetaM Expr := do
  if p == 2 then return mkConst ``Nat.prime_two
  if p == 3 then return mkConst ``Nat.prime_three
  if p % 2 == 0 then throwError "sieve lookup: {p} is even, so it is not prime"
  if p % 3 == 0 then throwError "sieve lookup: {p} is a multiple of 3, so it is not prime"
  if p < 5 then throwError "sieve lookup: {p} is not prime"
  let t := (p - 1) / 3
  let some cache ← findSieveCache p
    | throwError "sieve lookup: no sieve cache covers {p}; the caches in scope are {
        (← sieveCaches).map fun c => (c.lo, c.hi)}"
  let some litVal := (← getEnv).find? cache.litName >>= (·.value?) >>= (·.rawNatLit?)
    | throwError "sieve lookup: {cache.litName} does not hold a raw literal"
  unless (litVal >>> t) &&& 1 == 1 do
    throwError "sieve lookup: bit {t} of the sieve is clear, so {p} is not prime"
  return mkAppN (mkConst ``IsSieve.prime)
    #[mkRawNatLit cache.hi, mkConst cache.litName, mkRawNatLit t, mkRawNatLit p,
      mkConst cache.isSieveName,
      Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue]

/-- Close a `Nat.Prime p` goal with `mkSieveLookup`. -/
elab "sieve_lookup" : tactic => liftMetaFinishingTactic fun g => do
  let_expr Nat.Prime p := ← instantiateMVars (← g.getType)
    | throwError "sieve_lookup: goal is not `Nat.Prime _`"
  let some pv := p.nat?
    | throwError "sieve_lookup: the argument of `Nat.Prime` is not a numeral"
  g.assign (← mkSieveLookup pv)

/-- Syntax for the `sieve` method: a numeric literal `n`, looked up in the sieve cache.

```lean
-- In a prime_cert call, after `run_sieve`:
prime_cert [sieve {1009; 1999}, ...]
```
-/
public syntax sieve_spec := num

/-- The `sieve` method: certify the number in the step by a sieve lookup. -/
public meta def mkSieveProof : Meta.PrimeCertMethod ``sieve_spec := fun stx _ ↦ match stx with
  | `(sieve_spec| $n:num) => do
    have n := n.getNat
    return ⟨n, mkNatLit n, ← mkSieveLookup n⟩
  | _ => throwUnsupportedSyntax

/-- Registration of the `sieve` method with the `prime_cert` ladder. -/
@[prime_cert sieve] public meta def PrimeCertExt.sieve : Meta.PrimeCertExt where
  syntaxName := ``sieve_spec
  methodName := ``mkSieveProof

end PrimeCert.Sieve
