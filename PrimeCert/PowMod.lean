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

/-- The pow-mod function, named explicitly to allow more precise control of reduction. -/
@[expose] public def powMod (a b n : ℕ) : ℕ := a ^ b % n
/-- The pow-mod auxiliary function, named explicitly to allow more precise control of reduction. -/
public def powModAux (a b c n : ℕ) : ℕ := (a ^ b * c) % n

private def Nat.eager (k : Nat → Nat) (n : Nat) : Nat := k (eagerReduce n)

/-- Kernel-reducible tail-recursive modular exponentiation: computes `a ^ b % n`.
Uses `Nat.rec` with bounded fuel so the kernel can reduce it via `eagerReduce`. -/
@[expose] public noncomputable def powModTR (a b n : Nat) : Nat :=
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

/-- Computable version of `powModTR` using `partial_fixpoint`. Used at elaboration time
(e.g. in `mkPowModEq'`) where we need actual computation, not kernel reduction. -/
public def powModTR' (a b n : ℕ) : ℕ :=
  aux (a % n) b 1
  where aux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux (a * a % n) (b / 2) c
    else
      aux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint

private lemma Bool.rec_eq_ite {α : Type*} {b : Bool} {t f : α} :
    b.rec f t = if b then t else f := by
  cases b <;> simp

@[simp] private lemma powModTR_aux_zero_eq {n a b c : ℕ} :
    powModTR.aux n 0 a b c = 0 := rfl

private lemma powModTR_aux_succ_eq {n a b c fuel : ℕ} :
    powModTR.aux n (fuel + 1) a b c =
      (b.beq 0).rec (true := c % n)
      (((b % 2).beq 0).rec
        (powModTR.aux n fuel (a * a % n) (b / 2) (a * c % n))
        (powModTR.aux n fuel (a * a % n) (b / 2) c)) := by
  rfl

private lemma powModTR_aux_succ_eq' {n a b c fuel : ℕ} :
    powModTR.aux n (fuel + 1) a b c =
      if b = 0 then c % n else
      if b % 2 = 0 then powModTR.aux n fuel (a * a % n) (b / 2) c
      else powModTR.aux n fuel (a * a % n) (b / 2) (a * c % n) := by
  simp only [powModTR_aux_succ_eq, Bool.rec_eq_ite, beq_eq]

private lemma powModTR_aux_eq (n a b c fuel) (hfuel : b < fuel) :
    powModTR.aux n fuel a b c = powModAux a b c n := by
  induction fuel generalizing a b c with
  | zero => omega
  | succ fuel ih =>
    rw [powModTR_aux_succ_eq']
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

public lemma powModTR_eq (a b n : ℕ) : powModTR a b n = powMod a b n := by
  rw [powModTR, powModTR_aux_eq _ _ _ _ _ (by omega)]
  rw [powModAux, mul_one, powMod, mod_eq_mod, ← Nat.pow_mod]

public lemma powMod_eq_of_powModTR (a b n m : ℕ) (h : (powModTR a b n).beq m) :
    powMod a b n = m := by
  rwa [powModTR_eq, beq_eq] at h

public lemma powMod_ne_of_powModTR (a b n m : ℕ) (h : (powModTR a b n).beq m = false) :
    powMod a b n ≠ m := by
  have := Nat.ne_of_beq_eq_false h
  rwa [powModTR_eq] at this

/-! ## Step lemmas for elaborator-driven pow-mod

An alternative to the single `eagerReduce` of `powModTR`: recurse on the exponent's bits in the
elaborator, emitting one small step per bit. Each of these lemmas is one such step, closed by a
tiny `rfl` at the call site. See `PrimeCert.Meta.PowModSteps` for the tactic that chains them. -/

public lemma powModAux_zero_eq {a c n m : ℕ} (hm : Nat.beq (Nat.mod c n) m = true) :
    powModAux a 0 c n = m := by
  simpa [powModAux] using Nat.eq_of_beq_eq_true hm

public lemma powModAux_one_eq {a c n m : ℕ} (hm : Nat.beq (Nat.mod (Nat.mul a c) n) m = true) :
    powModAux a 1 c n = m := by
  have hm' : (a * c) % n = m := Nat.eq_of_beq_eq_true hm
  simp_all [powModAux]

public lemma powModAux_even_eq {a a' b b' c n m : ℕ}
    (ha' : Nat.beq (Nat.mod (Nat.mul a a) n) a' = true)
    (hb' : Nat.beq (Nat.shiftLeft b' 1) b = true)
    (h : powModAux a' b' c n = m) :
    powModAux a b c n = m := by
  have ha'' : a * a % n = a' := Nat.eq_of_beq_eq_true ha'
  have hb'' : b' <<< 1 = b := Nat.eq_of_beq_eq_true hb'
  rw [← ha'', powModAux, mul_mod] at h
  rw [Nat.shiftLeft_eq, mul_comm, pow_one] at hb''
  rw [← hb'', powModAux, pow_mul, mul_mod, pow_two, pow_mod, h]

public lemma powModAux_odd_eq {a a' b b' c c' n m : ℕ}
    (hb' : Nat.beq (Nat.add (Nat.mul 2 b') 1) b = true)
    (ha' : Nat.beq (Nat.mod (Nat.mul a a) n) a' = true)
    (hc' : Nat.beq (Nat.mod (Nat.mul a c) n) c' = true)
    (h : powModAux a' b' c' n = m) :
    powModAux a b c n = m := by
  have hb'' : 2 * b' + 1 = b := Nat.eq_of_beq_eq_true hb'
  have ha'' : a * a % n = a' := Nat.eq_of_beq_eq_true ha'
  have hc'' : a * c % n = c' := Nat.eq_of_beq_eq_true hc'
  rw [← ha'', ← hc'', powModAux, mul_mod, mod_mod] at h
  rw [← hb'', powModAux, pow_succ, pow_mul, mul_assoc, mul_mod, pow_mod, pow_two, h]

public lemma powMod_eq_steps (a : ℕ) {a' b n m : ℕ}
    (h : powModAux a' b 1 n = m) (ha : Nat.beq (Nat.mod a n) a' = true) :
    powMod a b n = m := by
  have ha' : a % n = a' := Nat.eq_of_beq_eq_true ha
  rwa [powModAux, mul_one, ← ha', pow_mod, mod_mod, ← pow_mod] at h
