/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum.PowMod
public import PrimeCert.ForLean

/-!
# Proof-producing evaluation of `a ^ b % n`

Note that `Mathlib.Tactic.NormNum.PowMod` contains a similar tactic, but that runs significantly
slower and less efficiently than the one here.
-/

open Nat

/-- The pow-mod auxiliary function, named explicitly to allow more precise control of reduction. -/
def powModAux (a b c n : ℕ) : ℕ := (a ^ b * c) % n

def Nat.eager (k : Nat → Nat) (n : Nat) : Nat := k (eagerReduce n)

/-- Kernel-reducible tail-recursive modular exponentiation: computes `a ^ b % n`.
Uses `Nat.rec` with bounded fuel so the kernel can reduce it via `eagerReduce`. -/
@[expose] public noncomputable def powModK (a b n : Nat) : Nat :=
  aux b.succ (a.mod n) b 1
where
  aux : Nat → ((a b c : Nat) → Nat) :=
    Nat.rec (fun _ _ _ => 0)
      (fun _ r a b c =>
        (b.beq 0).rec
          (((b.mod 2).beq 0).rec
            (r ((a.mul a).mod n) (b.div 2) ((a.mul c).mod n))
            (r ((a.mul a).mod n) (b.div 2) c))
          (c.mod n))

/-- Computable version of `powModK` using `partial_fixpoint`. Used at elaboration time
(e.g. in `mkPowModEq'`) where we need actual computation, not kernel reduction. -/
public def powMod (a b n : ℕ) : ℕ :=
  aux (a % n) b 1
  where aux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux (a * a % n) (b / 2) c
    else
      aux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint

@[simp] lemma powModK_aux_zero_eq {n a b c : ℕ} :
    powModK.aux n 0 a b c = 0 := rfl

lemma powModK_aux_succ_eq {n a b c fuel : ℕ} :
    powModK.aux n (fuel + 1) a b c =
      (b.beq 0).rec (true := c % n)
      (((b % 2).beq 0).rec
        (powModK.aux n fuel (a * a % n) (b / 2) (a * c % n))
        (powModK.aux n fuel (a * a % n) (b / 2) c)) := by
  rfl

lemma powModK_aux_succ_eq' {n a b c fuel : ℕ} :
    powModK.aux n (fuel + 1) a b c =
      if b = 0 then c % n else
      if b % 2 = 0 then powModK.aux n fuel (a * a % n) (b / 2) c
      else powModK.aux n fuel (a * a % n) (b / 2) (a * c % n) := by
  simp only [powModK_aux_succ_eq, Bool.rec_eq, beq_eq]

lemma powModK_aux_eq (n a b c fuel) (hfuel : b < fuel) :
    powModK.aux n fuel a b c = powModAux a b c n := by
  induction fuel generalizing a b c with
  | zero => omega
  | succ fuel ih =>
    rw [powModK_aux_succ_eq']
    split
    case isTrue hb0 => rw [hb0, powModAux, pow_zero, one_mul]
    split
    case isTrue hb0 hbe =>
      rw [ih _ _ _ (by omega)]
      rw [powModAux, powModAux, Nat.mul_mod _ c, Nat.mul_mod _ c]
      conv_rhs =>
        rw [← Nat.mod_add_div b 2]
      rw [hbe, zero_add, pow_mul, ← pow_two, ← Nat.pow_mod]
    case isFalse hb0 hbo =>
      rw [ih _ _ _ (by omega)]
      rw [powModAux, powModAux, Nat.mul_mod, Nat.mod_mod, ← pow_two,
        ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod, ← mul_assoc, ← Nat.pow_add_one]
      congr! 3
      lia

public lemma powModK_eq (a b n : ℕ) : powModK a b n = a ^ b % n := by
  rw [powModK, powModK_aux_eq _ _ _ _ _ (by omega)]
  rw [powModAux, mul_one, mod_eq_mod, ← Nat.pow_mod]

public lemma powMod_eq_of_powModK (a b n m : ℕ) (h : (powModK a b n).beq m) :
    a ^ b % n = m := by
  rwa [powModK_eq, beq_eq] at h

public lemma powMod_ne_of_powModK (a b n m : ℕ) (h : (powModK a b n).beq m = false) :
    a ^ b % n ≠ m := by
  have := Nat.ne_of_beq_eq_false h
  rwa [powModK_eq] at this
