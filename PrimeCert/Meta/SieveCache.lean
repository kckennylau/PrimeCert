/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Lean

/-! # The registry of sieve caches

Each `run_sieve` records the range it covers and the declarations holding the bitset and its
equation. `sieve_lookup` picks the tightest cache covering the number it is asked about.
-/

open Lean

namespace PrimeCert.Sieve

/-- A certified sieve in the environment: bits for the coprime-to-6 numbers in `[lo, hi]`, held by
`litName` and certified by `dataName : sieveK hi sq = <lit>`. -/
public structure SieveCache where
  /-- Smallest number the cache decides. -/
  lo : Nat
  /-- Largest number the cache decides. -/
  hi : Nat
  /-- Declaration holding the bitset literal. -/
  litName : Name
  /-- Declaration holding the equation for the bitset. -/
  dataName : Name
  deriving Inhabited

public meta initialize sieveCacheExt : SimpleScopedEnvExtension SieveCache (Array SieveCache) ←
  registerSimpleScopedEnvExtension {
    addEntry caches c := caches.push c
    initial := #[]
  }

/-- The caches in scope. -/
public meta def sieveCaches : CoreM (Array SieveCache) :=
  return sieveCacheExt.getState (← getEnv)

/-- The smallest cache deciding `p`, if any. -/
public meta def findSieveCache (p : Nat) : CoreM (Option SieveCache) := do
  let covering := (← sieveCaches).filter fun c => c.lo ≤ p && p ≤ c.hi
  return covering.foldl (init := none) fun best c =>
    match best with
    | none => some c
    | some b => if c.hi - c.lo < b.hi - b.lo then some c else some b

end PrimeCert.Sieve
