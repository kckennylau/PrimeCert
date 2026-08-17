/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Correct.Ones
public import Polya.Correct.Lam
public import Polya.Theory.Count

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

/-- The low table after `fuel` steps: field `j` holds `lowVal`. -/
public theorem lowLoopK_spec {lam ones wc off wb : ℕ} (fuel : ℕ)
    (hval : ∀ j < fuel, lowVal lam ones wc off j < 2 ^ wb) :
    ∀ j < fuel, fieldK (lowLoopK lam ones wc off wb 0 0 fuel) wb j = lowVal lam ones wc off j := by
  intro j hj
  refine (fieldK_of_lor_chain (start := 0) (F := lowVal lam ones wc off) rfl (fun f => ?_) fuel
    (fun i _ hi => hval i (by omega))).1 j (Nat.zero_le j) (by omega)
  rw [lowLoopK_succ]
  simp only [Nat.lor_eq, Nat.shiftLeft_eq', lowVal, Nat.succ_eq_add_one, Nat.sub_eq, Nat.mul_eq]

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
  refine fieldK_of_lor_chain (F := hiVal x lam ones wc off) rfl (fun f => ?_) fuel hval
  rw [hiLoopK_succ]
  simp only [Nat.lor_eq, Nat.shiftLeft_eq', hiVal, Nat.succ_eq_add_one, Nat.sub_eq, Nat.mul_eq]

/-! ## The values are `L` -/

/-- The counts table reads back the count below any position it covers. -/
public theorem onesBelowK_onesK {lam wc chunks p : ℕ} (hw : ∀ n, bitSum lam n < 2 ^ wc)
    (hp : p / 32 ≤ chunks) : onesBelowK lam (onesK lam wc chunks) wc p = bitSum lam p :=
  onesBelowK_eq (fieldK_onesK hw hp)

/-- A low-table entry against `L`: the set bits below `n + 1` count the numbers up to `n` with an
odd number of prime factors, so the entry is `L n` offset by `off`. -/
public theorem lowVal_eq_L {qs w M r cnt ones wc off n : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r)
    (hones : onesBelowK (lamK qs w M r cnt) ones wc (n + 1) = bitSum (lamK qs w M r cnt) (n + 1))
    (hn : n ≤ M) (hoff : bitSum (lamK qs w M r cnt) (n + 1) * 2 ≤ n + off) :
    ((lowVal (lamK qs w M r cnt) ones wc off n : ℕ) : ℤ) = L n + off := by
  have hb : bitSum (lamK qs w M r cnt) (n + 1)
      = ({m ∈ Finset.Icc 1 n | Odd (cardFactors m)}).card := by
    rw [bitSum_lamK htab hr (by omega)]
    simp
  rw [lowVal, hones, Nat.cast_sub hoff, hb, L_eq_sub_two_mul n]
  push_cast
  ring

/-- A high-table entry against `L`: it is the low-table entry at the quotient. -/
public theorem hiVal_eq_L {qs w M r cnt ones wc off x m : ℕ} (htab : IsPrimePowerTable qs w M cnt)
    (hr : M < 2 ^ r)
    (hones : onesBelowK (lamK qs w M r cnt) ones wc (x / m + 1)
      = bitSum (lamK qs w M r cnt) (x / m + 1))
    (hn : x / m ≤ M) (hoff : bitSum (lamK qs w M r cnt) (x / m + 1) * 2 ≤ x / m + off) :
    ((hiVal x (lamK qs w M r cnt) ones wc off m : ℕ) : ℤ) = L (x / m) + off :=
  lowVal_eq_L htab hr hones hn hoff

end PrimeCert.Polya
