/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import PrimeCert.Wieferich

/-! # From the classwise folds to a statement about a prime

The sieve holds one bit per number coprime to 6; `index n` is the position of `n`. These
lemmas read that position back and track it along a residue class.
-/

namespace PrimeCert.Wieferich

open PrimeCert PrimeCert.Sieve

/-- At a number that is `5 mod 6`, the index also reads as `(n - 2) / 3`. -/
public theorem index_five {n : ℕ} (h : n % 6 = 5) : index n = (n - 2) / 3 := by
  unfold index
  omega

/-- The sieve index of a number coprime to 6 names that number back. -/
public theorem value_index {n : ℕ} (h : n % 6 = 1 ∨ n % 6 = 5) : value (index n) = n := by
  unfold index
  rcases h with h | h <;> grind [value]

/-- Along the class of `r`, successive members sit at indices in steps of `m / 3`. -/
public theorem index_add {r m k : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5) (hm : m % 6 = 0)
    (h1 : 1 ≤ r) : index (r + m * k) = index r + (m / 3) * k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 6 * j := ⟨m / 6, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, j * k = c := ⟨_, rfl⟩
  have e1 : 6 * j * k = 6 * c := by rw [mul_assoc, hc]
  have e2 : 6 * j / 3 * k = 2 * c := by rw [show 6 * j / 3 = 2 * j by omega, mul_assoc, hc]
  rw [e1, e2]
  unfold index
  rcases hr with h | h
  · obtain ⟨i, rfl⟩ : ∃ i, r = 6 * i + 1 := ⟨r / 6, by omega⟩
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, r = 6 * i + 5 := ⟨r / 6, by omega⟩
    omega

/-- Membership in a list of naturals, as a `Bool` the kernel decides by walking the list. -/
@[expose] public noncomputable def memB (n : ℕ) : List ℕ → Bool :=
  List.rec false (fun a _ ih ↦ (n.beq a).or' ih)

public theorem memB_cons (n a : ℕ) (l : List ℕ) :
    memB n (a :: l) = (n.beq a).or' (memB n l) :=
  rfl

/-- The `Bool` form decides membership. -/
public theorem memB_iff {n : ℕ} {l : List ℕ} : memB n l ↔ n ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons a t ih => simp [memB_cons, Bool.or'_eq_or, ih]

/-- A prime below the cached range sets its own sieve bit. -/
public theorem testBit_of_prime {p : ℕ} (hp : p.Prime) (hb : p < 1000000)
    (hc : p % 6 = 1 ∨ p % 6 = 5) : testBitK sieveBits_1000000 (index p) := by
  have h2 := hp.two_le
  have hnum : value (index p) = p := value_index hc
  rw [testBitK_eq_testBit]
  have := isSieve_1000000 (index p) (by unfold index; omega) (by grind)
  grind

/-- At a prime whose check holds, the Wieferich condition fails. -/
public theorem not_wieferich_of_check {p : ℕ} (hp : p.Prime) (hb : p < 1000000)
    (hc : p % 6 = 1 ∨ p % 6 = 5) (h : wieferichAt (index p)) : ¬ Wieferich p := by
  have hbit := testBit_of_prime hp hb hc
  have hnum : valueK (index p) = p := by rw [valueK_eq_value]; exact value_index hc
  rw [wieferichAt, hnum] at h
  simp only [hbit, Bool.not'_eq_not, Bool.or'_eq_or, Bool.not_true, Bool.false_or,
    Bool.not_eq_true'] at h
  exact (wieferichK_eq_false_iff p hp.ne_one).mp h

/-- Read the check at one member of a class off that class's fold. -/
public theorem check_of_class {r m k len : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5) (hm : m % 6 = 0)
    (h1 : 1 ≤ r) (hk : k < len)
    (hfold : forallB wieferichAt (index r) len (m / 3)) :
    wieferichAt (index (r + m * k)) := by
  rw [index_add hr hm h1]
  have := (forallB_iff wieferichAt (index r) len (m / 3)).mp hfold k hk
  simpa [Nat.mul_comm, Nat.add_comm] using this

/-- A prime whose class's generated theorem covers its position fails the Wieferich condition. -/
public theorem not_wieferich_of_fold {p m len : ℕ} (hp : p.Prime) (hb : p < 1000000)
    (hm : m % 6 = 0) (hc : p % 6 = 1 ∨ p % 6 = 5) (h1 : 1 ≤ p % m)
    (hr : p % m % 6 = 1 ∨ p % m % 6 = 5) (hk : p / m < len)
    (hfold : forallB wieferichAt (index (p % m)) len (m / 3)) : ¬ Wieferich p := by
  refine not_wieferich_of_check hp hb hc ?_
  have := check_of_class (k := p / m) hr hm h1 hk hfold
  rwa [Nat.mod_add_div] at this

/-- Read the test at one member of a class from a range starting at position `j` of that class,
with the step given as `s`. -/
public theorem check_of_offset {r m s j k len : ℕ} (hr : r % 6 = 1 ∨ r % 6 = 5) (hm : m % 6 = 0)
    (h1 : 1 ≤ r) (hs : m / 3 = s) (hj : j ≤ k) (hk : k - j < len)
    (hfold : forallB wieferichAt (index r + s * j) len s) :
    wieferichAt (index (r + m * k)) := by
  subst hs
  rw [index_add hr hm h1]
  have := (forallB_iff wieferichAt (index r + m / 3 * j) len (m / 3)).mp hfold (k - j) hk
  have hle : j * (m / 3) ≤ k * (m / 3) := Nat.mul_le_mul_right _ hj
  have he : (k - j) * (m / 3) + (index r + m / 3 * j) = index r + m / 3 * k := by
    rw [Nat.sub_mul, Nat.mul_comm (m / 3) j, Nat.mul_comm (m / 3) k]
    omega
  rwa [he] at this

end PrimeCert.Wieferich
