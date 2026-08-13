/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Recursion
public import Polya.TableSpec
public import Polya.Tables

/-!
# The assembly

Three theorems take the emitted equations to a statement about `L`. `tables_of_data` turns the
loops of the setup into the two table invariants, `isHiTable_step` extends the high table by one
index, and `L_eq_of_final` reads `L x` off the last run of blocks. Each carries its numeric side
conditions as one decidable predicate over the emitted literals, checked by the kernel.
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (IsSieve num)

/-! ## The setup -/

/-- What the setup checks on its literals: the side conditions of `isPrimePowerTable_of_checks`,
the width of a count and of a table field, and the range the high table covers. -/
public abbrev SetupOK (x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st
    hpSt : ℕ) : Prop :=
  st % 2 = 1 ∧ num (st / 2) ≤ M ∧ (M - 1) / 3 < 32 * chunks2 ∧
    M < (3 * fuel + 4) * (3 * fuel + 4) ∧ 3 * fuel + 2 ≤ M ∧ M < 2 ^ w ∧ M < 2 ^ 64 ∧
    M < 2 ^ e ∧ e + e + e * fuel + e + 1 < 2 ^ 64 ∧ qs >>> (w * np) = hpSt >>> 128 ∧
    np + hpSt % 2 ^ 64 = cnt ∧ M < 2 ^ r ∧ M + 1 < 2 ^ wc ∧ (M + 1) / 32 ≤ chunks ∧
    rootx ≤ M ∧ M ≤ off ∧ M + off < 2 ^ wb ∧ top ≤ rootx ∧ x / (top + 1) ≤ M

/-- The decision procedure for `SetupOK`, applied to the emitted literals. -/
@[expose] public def setupOK (x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st
    hpSt : ℕ) : Bool :=
  decide (SetupOK x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st hpSt)

theorem of_setupOK {x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st
    hpSt : ℕ} (h : setupOK x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st hpSt
      = true) :
    SetupOK x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st hpSt :=
  of_decide_eq_true h

/-- The two tables of the recursion, from the equations of the six loops that build them. -/
public theorem tables_of_data {x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st hpSt
    lit lam ones low hi : ℕ} (hsieve : IsSieve M lit)
    (hbit : bitCheckLoopK qs w lit 1 0 np = st)
    (hpop : popcLoopK lit 0 0 chunks2 = np)
    (hhp : hpLoopK lit M w e (powLoopK M w 3 1 (powLoopK M w 2 1 0 e) e) 1 fuel = hpSt)
    (hlam : lamK qs w M r cnt = lam)
    (hones : onesK lam wc chunks = ones)
    (hlow : lowLoopK lam ones wc off wb 0 0 (rootx + 1) = low)
    (hhi : hiLoopK x lam ones wc off wb 0 (top + 1) (rootx - top) = hi)
    (hok : setupOK x M rootx top w r wc chunks off wb qs np cnt chunks2 e fuel st hpSt = true) :
    IsLowTable rootx off wb low ∧ IsHiTable x rootx off wb hi (top + 1) := by
  obtain ⟨hflag, hnum, hchunks2, hfuelup, hfueldn, hMw, hM64, hMe, hroom, hlink, hcnt, hr, hwc,
    hchunk, hroot, hMoff, hwbM, htop, hcut⟩ := of_setupOK hok
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hlink
  have htab : IsPrimePowerTable qs w M cnt :=
    isPrimePowerTable_of_checks hsieve hbit hflag (fun _ => hnum) hpop hchunks2 hhp hfuelup
      hfueldn hMw hM64 hMe hroom hlink hcnt
  have hw : ∀ n, bitSum (lamK qs w M r cnt) n < 2 ^ wc := fun n =>
    lt_of_le_of_lt (bitSum_le_of_lt (lamK_lt qs w M r cnt) n) hwc
  have hcount : ∀ p, p ≤ M + 1 →
      onesBelowK (lamK qs w M r cnt) ones wc p = bitSum (lamK qs w M r cnt) p := by
    intro p hp
    rw [← hones, ← hlam]
    exact onesBelowK_onesK hw (by omega)
  have hbelow : ∀ n, bitSum (lamK qs w M r cnt) (n + 1) ≤ n := by
    intro n
    have h0 : (lamK qs w M r cnt).testBit 0 = false := testBit_lamK_zero htab
    simp only [Nat.testBit_zero, decide_eq_false_iff_not] at h0
    have hone : bitSum (lamK qs w M r cnt) 1 = 0 := by
      simp only [bitSum, Finset.sum_range_one, Nat.shiftRight_zero]
      omega
    have hadd := bitSum_add (lamK qs w M r cnt) 1 n
    rw [Nat.add_comm 1 n, hone] at hadd
    have := bitSum_le (lamK qs w M r cnt / 2 ^ 1) n
    omega
  have hlowbound : ∀ j < rootx + 1, lowVal lam ones wc off j < 2 ^ wb := by
    intro j hj
    simp only [lowVal]
    omega
  have hdiv : ∀ m, top + 1 ≤ m → x / m ≤ M := fun m hm =>
    le_trans (Nat.div_le_div_left hm (by omega)) hcut
  have hhibound : ∀ j, top + 1 ≤ j → j < top + 1 + (rootx - top) →
      hiVal x lam ones wc off j < 2 ^ wb := by
    intro j hj1 hj2
    have := hdiv j hj1
    simp only [hiVal]
    omega
  obtain ⟨hfields, hzero⟩ := hiLoopK_spec_start (rootx - top) hhibound
  refine ⟨fun q hq => ?_, fun m hm1 hm2 => ?_, fun m hm => ?_⟩
  · rw [← hlow, lowLoopK_spec (rootx + 1) hlowbound q (by omega), ← hlam]
    exact lowVal_eq_L htab hr (hcount (q + 1) (by omega)) (by omega)
      (by have := hbelow q; omega)
  · rw [← hhi, hfields m hm1 (by omega), ← hlam]
    exact hiVal_eq_L htab hr (hcount (x / m + 1) (by have := hdiv m hm1; omega)) (hdiv m hm1)
      (by have := hbelow (x / m); have := hdiv m hm1; omega)
  · rw [← hhi]
    exact hzero m (Or.inl hm)

/-! ## One index of the recursion -/

/-- What one index checks on its literals: the packing of the final block state, the bounds the
block invariant needs, the square root of the argument, and the value written into the high
table. -/
public abbrev StepOK (x rootx off wb j v s A B S val hi hiNext : ℕ) : Prop :=
  0 < j ∧ j ≤ rootx ∧ x / j = v ∧ S = v + 1 + 2 ^ 64 * A + 2 ^ 128 * B ∧ A < 2 ^ 64 ∧
    2 * B < 2 ^ 64 ∧ B = off * (v - 1) ∧ 0 < v ∧ v + 1 < 2 ^ 64 ∧ s * s ≤ v ∧
    v < (s + 1) * (s + 1) ∧ val + A = s + B + off ∧ val < 2 ^ wb ∧
    hi ||| val <<< (wb * j) = hiNext ∧ 0 < off ∧ 2 ^ wb ≤ 2 * off ∧
    x < (rootx + 1) * (rootx + 1)

/-- The decision procedure for `StepOK`, applied to the emitted literals. -/
@[expose] public def stepOK (x rootx off wb j v s A B S val hi hiNext : ℕ) : Bool :=
  decide (StepOK x rootx off wb j v s A B S val hi hiNext)

theorem of_stepOK {x rootx off wb j v s A B S val hi hiNext : ℕ}
    (h : stepOK x rootx off wb j v s A B S val hi hiNext = true) :
    StepOK x rootx off wb j v s A B S val hi hiNext :=
  of_decide_eq_true h

/-- The square root the checks pin down. -/
theorem sqrt_eq_of_le_of_lt {v s : ℕ} (h1 : s * s ≤ v) (h2 : v < (s + 1) * (s + 1)) :
    Nat.sqrt v = s := by
  have hle : s ≤ Nat.sqrt v := Nat.le_sqrt.2 h1
  have hlt : Nat.sqrt v < s + 1 := Nat.sqrt_lt.2 h2
  omega

/-- A finished run of blocks at `x / j` extends the high table to index `j`. -/
public theorem isHiTable_step {x rootx off wb low hi hiNext j v s A B S val fuel : ℕ}
    (hlow : IsLowTable rootx off wb low) (hhi : IsHiTable x rootx off wb hi (j + 1))
    (hblock : blockLoopK x v rootx low hi wb off 2 fuel = S)
    (hok : stepOK x rootx off wb j v s A B S val hi hiNext = true) :
    IsHiTable x rootx off wb hiNext j := by
  obtain ⟨hj, hjr, hxj, hS, hA, hB2, hB, hv, hv64, hs1, hs2, hval, hvlt, hnext, hoff, hwb,
    hroot⟩ := of_stepOK hok
  obtain ⟨hk, hA', hB'⟩ := state_split hS (by omega) hA
  have hvals : BlockValues x v rootx low hi wb off := by
    rw [← hxj]
    exact blockValues_of_tables hj hjr hroot hlow hhi
  have hL := L_eq_of_blockLoopK hoff hv hv64 hwb hvals hblock (by rw [hB']; exact hB2) hk
    (by rw [hB', hB])
  rw [hA', ← hB, sqrt_eq_of_le_of_lt hs1 hs2] at hL
  rw [← hnext]
  refine isHiTable_write hj hjr hhi ?_ hvlt
  rw [hxj, hL]
  omega

/-! ## The last index -/

/-- What the last index checks on its literals: as for one index, with the value it produces split
into the two naturals of the answer. -/
public abbrev FinalOK (x rootx off wb s A B S p q : ℕ) : Prop :=
  0 < rootx ∧ S = x + 1 + 2 ^ 64 * A + 2 ^ 128 * B ∧ A < 2 ^ 64 ∧ 2 * B < 2 ^ 64 ∧
    B = off * (x - 1) ∧ 0 < x ∧ x + 1 < 2 ^ 64 ∧ s * s ≤ x ∧ x < (s + 1) * (s + 1) ∧
    p + A = s + B + q ∧ 0 < off ∧ 2 ^ wb ≤ 2 * off ∧ x < (rootx + 1) * (rootx + 1)

/-- The decision procedure for `FinalOK`, applied to the emitted literals. -/
@[expose] public def finalOK (x rootx off wb s A B S p q : ℕ) : Bool :=
  decide (FinalOK x rootx off wb s A B S p q)

theorem of_finalOK {x rootx off wb s A B S p q : ℕ}
    (h : finalOK x rootx off wb s A B S p q = true) : FinalOK x rootx off wb s A B S p q :=
  of_decide_eq_true h

/-- The run of blocks at `x` itself gives the running total. -/
public theorem L_eq_of_final {x rootx off wb low hi s A B S p q fuel : ℕ}
    (hlow : IsLowTable rootx off wb low) (hhi : IsHiTable x rootx off wb hi 2)
    (hblock : blockLoopK x x rootx low hi wb off 2 fuel = S)
    (hok : finalOK x rootx off wb s A B S p q = true) :
    L x = (p : ℤ) - q := by
  obtain ⟨hroot1, hS, hA, hB2, hB, hx, hx64, hs1, hs2, hpq, hoff, hwb, hroot⟩ := of_finalOK hok
  obtain ⟨hk, hA', hB'⟩ := state_split hS (by omega) hA
  have hvals : BlockValues x x rootx low hi wb off := by
    have h := blockValues_of_tables (j := 1) Nat.one_pos hroot1 hroot hlow hhi
    rwa [Nat.div_one] at h
  have hL := L_eq_of_blockLoopK hoff hx hx64 hwb hvals hblock (by rw [hB']; exact hB2) hk
    (by rw [hB', hB])
  rw [hA', ← hB, sqrt_eq_of_le_of_lt hs1 hs2] at hL
  rw [hL]
  omega

/-! ## Pólya's conjecture -/

/-- A positive running total at an argument of at least two is a counterexample. -/
public theorem exists_pos_L (x : ℕ) (hx : 2 ≤ x) (h : 0 < L x) : ∃ n, 2 ≤ n ∧ 0 < L n :=
  ⟨x, hx, h⟩

/-- A positive running total at an argument of at least two refutes the conjecture. -/
public theorem not_forall_L_nonpos (x : ℕ) (hx : 2 ≤ x) (h : 0 < L x) :
    ¬ ∀ n, 2 ≤ n → L n ≤ 0 := fun hall => absurd (hall x hx) (by omega)

end PrimeCert.Polya
