/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Ones
public import Polya.LamCorrect
public import Polya.Count

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
public theorem lowLoopK_spec {lam ones wc off wb : ℕ} (fuel : ℕ)
    (hval : ∀ j < fuel, lowVal lam ones wc off j < 2 ^ wb) :
    (∀ j < fuel, fieldK (lowLoopK lam ones wc off wb 0 0 fuel) wb j = lowVal lam ones wc off j) ∧
      lowLoopK lam ones wc off wb 0 0 fuel < 2 ^ (wb * fuel) := by
  induction fuel with
  | zero =>
    refine ⟨by omega, ?_⟩
    have h0 : lowLoopK lam ones wc off wb 0 0 0 = 0 := rfl
    rw [h0]
    exact Nat.two_pow_pos _
  | succ f ih =>
    obtain ⟨ihfield, ihlt⟩ := ih fun j hj => hval j (by omega)
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
        exact fieldK_lor_shiftLeft_self ihlt (hval j (by omega))
    · exact lor_shiftLeft_lt ihlt (hval f (by omega))

/-- The value written into field `j` of the high table. -/
@[expose] public noncomputable def hiVal (x lam ones wc off j : ℕ) : ℕ :=
  ((x / j) + off) - onesBelowK lam ones wc (x / j + 1) * 2

/-- The high table built from an empty table at `start`: the fields it covers hold `hiVal`, and the
fields outside stay clear. -/
public theorem hiLoopK_spec_start {x lam ones wc off wb start : ℕ} (fuel : ℕ)
    (hval : ∀ j, start ≤ j → j < start + fuel → hiVal x lam ones wc off j < 2 ^ wb) :
    (∀ j, start ≤ j → j < start + fuel →
        fieldK (hiLoopK x lam ones wc off wb 0 start fuel) wb j = hiVal x lam ones wc off j) ∧
      ∀ j, (j < start ∨ start + fuel ≤ j) →
        fieldK (hiLoopK x lam ones wc off wb 0 start fuel) wb j = 0 := by
  induction fuel with
  | zero =>
    refine ⟨by omega, fun j _ => ?_⟩
    have h0 : hiLoopK x lam ones wc off wb 0 start 0 = 0 := rfl
    rw [h0, fieldK_eq_div_mod]
    simp
  | succ f ih =>
    obtain ⟨ihfield, ihzero⟩ := ih fun j hj1 hj2 => hval j hj1 (by omega)
    have hstep : hiLoopK x lam ones wc off wb 0 start (f + 1)
        = hiLoopK x lam ones wc off wb 0 start f |||
            (hiVal x lam ones wc off (start + f)) <<< (wb * (start + f)) := by
      rw [hiLoopK_succ]
      simp only [Nat.lor_eq, Nat.shiftLeft_eq', hiVal, Nat.succ_eq_add_one, Nat.sub_eq,
        Nat.mul_eq]
    rw [hstep]
    have hlast : hiVal x lam ones wc off (start + f) < 2 ^ wb := hval _ (by omega) (by omega)
    refine ⟨fun j hj1 hj2 => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (start + f) with h | h
      · rw [fieldK_lor_shiftLeft_ne hlast (by omega)]
        exact ihfield j hj1 h
      · have hjf : j = start + f := by omega
        subst hjf
        exact fieldK_lor_shiftLeft_of_zero (ihzero (start + f) (by omega)) hlast
    · rw [fieldK_lor_shiftLeft_ne hlast (by omega)]
      exact ihzero j (by omega)

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

/-- The counts table reads back the count below any position it covers. -/
public theorem onesBelowK_onesK {lam wc chunks p : ℕ} (hw : ∀ n, bitSum lam n < 2 ^ wc)
    (hp : p / 32 ≤ chunks) : onesBelowK lam (onesK lam wc chunks) wc p = bitSum lam p :=
  onesBelowK_eq (fieldK_onesK hw hp)

/-- A low-table entry against `L`. -/
public theorem lowVal_eq_L {qs w M r cnt ones wc off n : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r)
    (hones : onesBelowK (lamK qs w M r cnt) ones wc (n + 1) = bitSum (lamK qs w M r cnt) (n + 1))
    (hn : n ≤ M) (hoff : bitSum (lamK qs w M r cnt) (n + 1) * 2 ≤ n + off) :
    ((lowVal (lamK qs w M r cnt) ones wc off n : ℕ) : ℤ) = L n + off := by
  rw [lowVal, hones]
  exact val_eq_L htab hr hn hoff

/-- A high-table entry against `L`. -/
public theorem hiVal_eq_L {qs w M r cnt ones wc off x m : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r)
    (hones : onesBelowK (lamK qs w M r cnt) ones wc (x / m + 1)
      = bitSum (lamK qs w M r cnt) (x / m + 1))
    (hn : x / m ≤ M) (hoff : bitSum (lamK qs w M r cnt) (x / m + 1) * 2 ≤ x / m + off) :
    ((hiVal x (lamK qs w M r cnt) ones wc off m : ℕ) : ℤ) = L (x / m) + off := by
  rw [hiVal, hones]
  exact val_eq_L htab hr hn hoff

end PrimeCert.Polya
