/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import MillerRabin.Bound

/-! # Covering every residue class by splicing the per-class theorems

`Cover m len step k` says that every remainder below `k` which is coprime to `m`, and is neither
of the two holding a known Wieferich prime, has the scan of its class. Its proof is assembled from
`cover_zero` and `cover_succ`, one step per remainder, so each class contributes its own theorem.
-/

namespace MillerRabin

open PrimeCert PrimeCert.Sieve

/-- Every remainder below `k` coprime to `m`, other than the two holding a known Wieferich prime,
has the scan of its class. -/
public def Cover (m len step k : ℕ) : Prop :=
  ∀ r < k, Nat.gcd r m = 1 → r ≠ 1093 % m → r ≠ 3511 % m →
    forallB wieferichAtK (indexK r) len step

public theorem cover_zero {m len step : ℕ} : Cover m len step 0 := by grind [Cover]

public theorem cover_succ {m len step k : ℕ} (h : Cover m len step k)
    (hk : Nat.gcd k m = 1 → k ≠ 1093 % m → k ≠ 3511 % m →
      forallB wieferichAtK (indexK k) len step) :
    Cover m len step (k + 1) := by
  grind [Cover, Nat.lt_succ_iff_lt_or_eq]

/-- A remainder sharing a factor with `m` meets the condition vacuously. -/
public theorem step_of_gcd {m len step k : ℕ} (h : ((Nat.gcd k m).beq 1).not') :
    Nat.gcd k m = 1 → k ≠ 1093 % m → k ≠ 3511 % m → forallB wieferichAtK (indexK k) len step := by
  grind [Bool.not'_eq_not, Nat.beq_eq]

/-- A remainder holding a known Wieferich prime meets the condition vacuously. -/
public theorem step_of_exception {m len step k : ℕ}
    (h : (k.beq (1093 % m)).or' (k.beq (3511 % m))) :
    Nat.gcd k m = 1 → k ≠ 1093 % m → k ≠ 3511 % m → forallB wieferichAtK (indexK k) len step := by
  grind [Bool.or'_eq_or, Nat.beq_eq]

/-- A remainder whose class scan holds meets the condition. -/
public theorem step_of_scan {m len step k : ℕ} (h : forallB wieferichAtK (indexK k) len step) :
    Nat.gcd k m = 1 → k ≠ 1093 % m → k ≠ 3511 % m → forallB wieferichAtK (indexK k) len step := by
  grind

end MillerRabin
