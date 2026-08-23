/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import MillerRabin.Defs
public import PrimeCert.SieveCorrect
public import PrimeCert.ForallB

/-! # The Wieferich condition along a residue class of a sieve

`wieferichAtK s` reads the condition at one position of the sieve `s`. `not_wieferich_of_fold`
turns a scan of one residue class into the statement that a prime of that class fails the
condition.
-/

namespace MillerRabin

open PrimeCert PrimeCert.Sieve

/-- The Wieferich check at position `t` of the sieve `s`: true when the bit at `t` is clear, or
when the number at `t` fails `2 ^ (n - 1) ≡ 1 [MOD n ^ 2]`. -/
@[expose] public noncomputable def wieferichAtK (s t : ℕ) : Bool :=
  (testBitK s t).not'.or' (wieferichK (valueK t)).not'

/-- Along the class of `r`, successive members sit `m / 3` sieve positions apart. -/
public theorem index_add {r m k : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5) (hm : m % 6 = 0) :
    index (r + m * k) = index r + (m / 3) * k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 6 * j := ⟨m / 6, by lia⟩
  obtain ⟨c, hc⟩ : ∃ c, j * k = c := ⟨_, rfl⟩
  have e1 : 6 * j * k = 6 * c := by rw [mul_assoc, hc]
  have e3 : 6 * j / 3 = 2 * j := by lia
  have e2 : 6 * j / 3 * k = 2 * c := by rw [e3, mul_assoc, hc]
  rw [e1, e2]
  unfold index
  obtain ⟨i, hi⟩ : ∃ i, r = 6 * i + r % 6 := ⟨r / 6, by lia⟩
  rcases hr with h | h <;> lia

/-- A prime within the range of a sieve sets its own bit. -/
public theorem testBit_of_prime {n s p : ℕ} (hs : IsSieve n s) (hp : p.Prime) (hb : p ≤ n)
    (hc : p % 6 = 1 ∨ p % 6 = 5) : s.testBit (index p) := by
  have h2 := hp.two_le
  have hnum : value (index p) = p := value_index hc
  have := hs (index p) (by unfold index; lia) (by grind)
  grind

/-- At a prime whose check holds, the Wieferich condition fails. -/
public theorem not_wieferich_of_check {n s p : ℕ} (hs : IsSieve n s) (hp : p.Prime)
    (hb : p ≤ n) (hc : p % 6 = 1 ∨ p % 6 = 5) (h : wieferichAtK s (index p)) :
    ¬ Wieferich p := by
  have hbit := testBit_of_prime hs hp hb hc
  have hnum : value (index p) = p := value_index hc
  grind [wieferichAtK, Bool.not'_eq_not, Bool.or'_eq_or, wieferichK_eq_false_iff, hp.ne_one]

/-- Read the check at one member of a class off that class's scan. -/
public theorem check_of_class {s r m k len : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5) (hm : m % 6 = 0)
    (hk : k < len)
    (hfold : forallB (wieferichAtK s) (index r) len (m / 3)) :
    wieferichAtK s (index (r + m * k)) := by
  rw [index_add hr hm]
  have := (forallB_iff (wieferichAtK s) (index r) len (m / 3)).mp hfold k hk
  simpa [Nat.mul_comm, Nat.add_comm] using this

/-- A prime whose class is covered by a scan fails the Wieferich condition. -/
public theorem not_wieferich_of_fold {n s p m len : ℕ} (hs : IsSieve n s) (hp : p.Prime)
    (hb : p ≤ n) (hm : m % 6 = 0) (hc : p % 6 = 1 ∨ p % 6 = 5)
    (hr : p % m % 6 = 1 ∨ p % m % 6 = 5) (hk : p / m < len)
    (hfold : forallB (wieferichAtK s) (index (p % m)) len (m / 3)) : ¬ Wieferich p := by
  refine not_wieferich_of_check hs hp hb hc ?_
  have := check_of_class (k := p / m) hr hm hk hfold
  rwa [Nat.mod_add_div] at this

/-- Read the check at one member of a class from a scan starting at position `j` of that class,
whose successive members sit `d` sieve positions apart. -/
public theorem check_of_offset {s r m d j k len : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5)
    (hm : m % 6 = 0) (hs : m / 3 = d) (hj : j ≤ k) (hk : k - j < len)
    (hfold : forallB (wieferichAtK s) (index r + d * j) len d) :
    wieferichAtK s (index (r + m * k)) := by
  subst hs
  rw [index_add hr hm]
  have := (forallB_iff (wieferichAtK s) (index r + m / 3 * j) len (m / 3)).mp hfold (k - j) hk
  have hle : j * (m / 3) ≤ k * (m / 3) := Nat.mul_le_mul_right _ hj
  have he : (k - j) * (m / 3) + (index r + m / 3 * j) = index r + m / 3 * k := by
    rw [Nat.sub_mul, Nat.mul_comm (m / 3) j, Nat.mul_comm (m / 3) k]
    lia
  rwa [he] at this

end MillerRabin
