/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SieveCorrect

/-!
# Reading a prime off the sieve

`prime_of_sieve_eq` turns a bit of the cached sieve literal into `Nat.Prime`. The `sieve_lookup`
tactic and the `sieve` certificate method in `Meta/SieveLookup` apply it, discharging each
hypothesis by kernel computation.
-/

namespace PrimeCert.Sieve

/-- From the numeric side-conditions (each as `Nat.ble … = true`) and "bit `t` of the stored sieve
literal `lit` is set", and `numK t = p`, conclude `p` is prime; `hEq : sieveK n sqrtN = lit` (the
equation `run_sieve` proves) carries the bit read back to the sieve, so the kernel shifts the
literal instead of re-sieving. -/
public theorem prime_of_sieve_eq (n sqrtN t lit p : Nat) (hEq : sieveK n sqrtN = lit)
    (h1 : Nat.ble 1 t)
    (h2 : t.ble ((n.sub 1).div 3))
    (h3 : (((n.sub 1).div 3).add 1).ble (Nat.pow 2 32))
    (h4 : (numK t).ble n)
    (h5 : n.ble (sqrtN.mul sqrtN))
    (hbit : (bitVal lit t).beq 1)
    (hp : (numK t).beq p) :
    Nat.Prime p := by
  rw [← Nat.eq_of_beq_eq_true hp, numK_eq_num]
  refine (sieveK_testBit_iff n sqrtN t (Nat.le_of_ble_eq_true h1) (Nat.le_of_ble_eq_true h2)
    (Nat.le_of_ble_eq_true h3) (Nat.le_of_ble_eq_true h4) (Nat.le_of_ble_eq_true h5)).mp ?_
  rw [← bitVal_eq_one_iff, hEq]
  exact Nat.eq_of_beq_eq_true hbit

end PrimeCert.Sieve
