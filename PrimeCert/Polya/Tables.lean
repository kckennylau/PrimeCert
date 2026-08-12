/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Polya.Ones
public import PrimeCert.Polya.LamCorrect
public import PrimeCert.Polya.Count

/-!
# The tables of values of `L`

Field `j` of `lowLoopK` holds `j + off - 2 * (set bits below j + 1)` (`fieldK_lowLoopK`), which is
`L j + off` once the parity table and the counts are what they claim to be (`fieldK_low_eq_L`).
The same holds for `hiLoopK` at the quotients `x / j`.
-/

namespace PrimeCert.Polya

open Nat ArithmeticFunction

/-- The value written into field `j` of the low table. -/
@[expose] public noncomputable def lowVal (lam ones wc off j : ℕ) : ℕ :=
  (j + off) - onesBelowK lam ones wc (j + 1) * 2

/-- The low table after `fuel` steps: field `j` holds `lowVal`, and the table stops below field
`fuel`. -/
theorem lowLoopK_spec {lam ones wc off wb : ℕ} (hval : ∀ j, lowVal lam ones wc off j < 2 ^ wb)
    (fuel : ℕ) :
    (∀ j < fuel, fieldK (lowLoopK lam ones wc off wb 0 0 fuel) wb j = lowVal lam ones wc off j) ∧
      lowLoopK lam ones wc off wb 0 0 fuel < 2 ^ (wb * fuel) := by
  induction fuel with
  | zero =>
    refine ⟨by omega, ?_⟩
    have h0 : lowLoopK lam ones wc off wb 0 0 0 = 0 := rfl
    rw [h0]
    exact Nat.two_pow_pos _
  | succ f ih =>
    obtain ⟨ihfield, ihlt⟩ := ih
    have hstep : lowLoopK lam ones wc off wb 0 0 (f + 1)
        = lowLoopK lam ones wc off wb 0 0 f ||| (lowVal lam ones wc off f) <<< (wb * f) := by
      rw [lowLoopK_succ]
      simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.zero_add, lowVal, Nat.succ_eq_add_one,
        Nat.sub_eq, Nat.mul_eq]
    rw [hstep]
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases Nat.lt_or_ge j f with h | h
      · rw [fieldK_lor_shiftLeft_of_lt h, ihfield j h]
      · have hjf : j = f := by omega
        subst hjf
        exact fieldK_lor_shiftLeft_self ihlt (hval j)
    · exact lor_shiftLeft_lt ihlt (hval f)

/-- The value written into field `j` of the high table. -/
@[expose] public noncomputable def hiVal (x lam ones wc off j : ℕ) : ℕ :=
  ((x / j) + off) - onesBelowK lam ones wc (x / j + 1) * 2

/-- The high table after `fuel` steps: field `j` holds `hiVal`, and the table stops below field
`fuel`. -/
theorem hiLoopK_spec {x lam ones wc off wb : ℕ} (hval : ∀ j, hiVal x lam ones wc off j < 2 ^ wb)
    (fuel : ℕ) :
    (∀ j < fuel, fieldK (hiLoopK x lam ones wc off wb 0 0 fuel) wb j
        = hiVal x lam ones wc off j) ∧
      hiLoopK x lam ones wc off wb 0 0 fuel < 2 ^ (wb * fuel) := by
  induction fuel with
  | zero =>
    refine ⟨by omega, ?_⟩
    have h0 : hiLoopK x lam ones wc off wb 0 0 0 = 0 := rfl
    rw [h0]
    exact Nat.two_pow_pos _
  | succ f ih =>
    obtain ⟨ihfield, ihlt⟩ := ih
    have hstep : hiLoopK x lam ones wc off wb 0 0 (f + 1)
        = hiLoopK x lam ones wc off wb 0 0 f ||| (hiVal x lam ones wc off f) <<< (wb * f) := by
      rw [hiLoopK_succ]
      simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.zero_add, hiVal, Nat.succ_eq_add_one,
        Nat.sub_eq, Nat.mul_eq]
    rw [hstep]
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases Nat.lt_or_ge j f with h | h
      · rw [fieldK_lor_shiftLeft_of_lt h, ihfield j h]
      · have hjf : j = f := by omega
        subst hjf
        exact fieldK_lor_shiftLeft_self ihlt (hval j)
    · exact lor_shiftLeft_lt ihlt (hval f)

/-! ## The values are `L` -/

/-- A table value read against `L`: the set bits below `v + 1` give `L v`, offset by `off`. -/
public theorem val_eq_L {qs w M r cnt off v : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r) (hv : v ≤ M)
    (hoff : bitSum (lamK qs w M r cnt) (v + 1) * 2 ≤ v + off) :
    (((v + off) - bitSum (lamK qs w M r cnt) (v + 1) * 2 : ℕ) : ℤ) = L v + off := by
  have hb : bitSum (lamK qs w M r cnt) (v + 1)
      = ({n ∈ Finset.Icc 1 v | Odd (cardFactors n)}).card := by
    rw [bitSum_lamK htab hr (by omega)]
    simp
  rw [Nat.cast_sub hoff, hb, L_eq_sub_two_mul v]
  push_cast
  ring

end PrimeCert.Polya
