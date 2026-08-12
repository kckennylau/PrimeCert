/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.BitCheck
public import Polya.Ones

/-!
# The packed primes are every prime up to the cutoff

`bitCheckLoopK` sends each packed field to a distinct set position of the sieve, and `popcLoopK`
counts the set positions. Equal counts make that map onto, so every prime from 5 to the cutoff sits
in a field (`primeBlock_spec`).
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (IsSieve num)

/-- The blockwise count is the count of set positions. -/
public theorem popcLoopK_eq_bitSum (b acc fuel : ℕ) :
    popcLoopK b acc 0 fuel = acc + bitSum b (32 * fuel) := by
  induction fuel with
  | zero =>
    have h : popcLoopK b acc 0 0 = acc := rfl
    rw [h, Nat.mul_zero]
    simp [bitSum]
  | succ f ih =>
    rw [popcLoopK_succ]
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.land_eq, Nat.shiftRight_eq',
      Nat.shiftLeft_eq', Nat.zero_add]
    rw [Nat.mul_comm f 32, popc32K_chunk, ih, Nat.mul_succ, bitSum_add, Nat.add_assoc]

theorem testBit_iff_shiftRight_mod_two {v t : ℕ} : v.testBit t ↔ (v >>> t) % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp

/-- The number at an index rises with the index. -/
theorem num_le_num {t t' : ℕ} (h : t ≤ t') : num t ≤ num t' := by
  simp only [num]
  omega

/-- A field that passed its tests is the number at its sieve index. -/
theorem num_idx_fieldK {qs w lit cnt : ℕ} (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    {i : ℕ} (hi : i < cnt) : num (idx (fieldK qs w i)) = fieldK qs w i := by
  obtain ⟨htests, -, -⟩ := bitCheckLoopK_spec cnt h
  obtain ⟨hmod, -, -⟩ := htests i hi
  exact num_idx (by omega)

/-- Every field sits below the cutoff, since the top one does and the fields rise. -/
theorem fieldK_le {qs w lit cnt M : ℕ} (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    (htop : 0 < cnt → num (bitCheckLoopK qs w lit 1 0 cnt / 2) ≤ M)
    {i : ℕ} (hi : i < cnt) : fieldK qs w i ≤ M := by
  obtain ⟨-, hmono, hlast⟩ := bitCheckLoopK_spec cnt h
  have hcnt : 0 < cnt := by omega
  have htopidx : bitCheckLoopK qs w lit 1 0 cnt / 2 = idx (fieldK qs w (cnt - 1)) := hlast hcnt
  have hle : idx (fieldK qs w i) ≤ idx (fieldK qs w (cnt - 1)) := by
    rcases Nat.lt_or_ge i (cnt - 1) with hlt | hge
    · exact Nat.le_of_lt (hmono i (cnt - 1) hlt (by omega))
    · have : i = cnt - 1 := by omega
      rw [this]
  rw [← num_idx_fieldK h hi]
  exact le_trans (num_le_num hle) (htopidx ▸ htop hcnt)

/-- The set positions of the sieve are exactly the sieve indices of the packed fields: the fields
inject into them and the counts agree. -/
theorem exists_field_of_testBit {qs w lit cnt chunks : ℕ}
    (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1) (hpop : popcLoopK lit 0 0 chunks = cnt)
    (hlt : ∀ i, i < cnt → idx (fieldK qs w i) < 32 * chunks)
    {t : ℕ} (ht : lit.testBit t) (htlt : t < 32 * chunks) :
    ∃ i < cnt, idx (fieldK qs w i) = t := by
  obtain ⟨htests, hmono, -⟩ := bitCheckLoopK_spec cnt h
  have hcard : ({i ∈ Finset.range (32 * chunks) | lit.testBit i}).card = cnt := by
    rw [← bitSum_eq_card, ← Nat.zero_add (bitSum lit (32 * chunks)), ← popcLoopK_eq_bitSum, hpop]
  have hsub : (Finset.range cnt).image (fun i => idx (fieldK qs w i))
      ⊆ {i ∈ Finset.range (32 * chunks) | lit.testBit i} := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨-, -, hset⟩ := htests i hi
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt i hi, testBit_iff_shiftRight_mod_two.2 hset⟩
  have himg : ((Finset.range cnt).image (fun i => idx (fieldK qs w i))).card = cnt := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    by_contra hne
    rcases Nat.lt_or_ge a b with hab' | hab'
    · exact absurd hab (Nat.ne_of_lt (hmono a b hab' hb))
    · exact absurd hab.symm (Nat.ne_of_lt (hmono b a (by omega) ha))
  have heq : (Finset.range cnt).image (fun i => idx (fieldK qs w i))
      = {i ∈ Finset.range (32 * chunks) | lit.testBit i} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : t ∈ (Finset.range cnt).image (fun i => idx (fieldK qs w i)) := by
    rw [heq]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨htlt, ht⟩
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨i, hi, hti⟩ := hmem
  exact ⟨i, hi, hti⟩

/-- A prime of at least 5 is coprime to 6. -/
theorem mod_six_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := fun hd => by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hd) with h | h <;> omega
  have h3 : ¬ (3 ∣ p) := fun hd => by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hd) with h | h <;> omega
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3
  omega

/-- What the two loops say about the block of packed primes: every field is a prime from 5 to the
cutoff, every such prime is a field, and the fields are distinct. -/
public theorem primeBlock_spec {qs w lit M cnt chunks : ℕ} (hsieve : IsSieve M lit)
    (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    (htop : 0 < cnt → num (bitCheckLoopK qs w lit 1 0 cnt / 2) ≤ M)
    (hpop : popcLoopK lit 0 0 chunks = cnt) (hchunks : (M - 1) / 3 < 32 * chunks) :
    (∀ i < cnt, (fieldK qs w i).Prime ∧ fieldK qs w i ≤ M) ∧
      (∀ p, p.Prime → 5 ≤ p → p ≤ M → ∃ i < cnt, fieldK qs w i = p) ∧
        (∀ i j, i < cnt → j < cnt → fieldK qs w i = fieldK qs w j → i = j) := by
  have hbound : ∀ i, i < cnt → fieldK qs w i ≤ M := fun i hi => fieldK_le h htop hi
  have hidx : ∀ i, i < cnt → idx (fieldK qs w i) < 32 * chunks := by
    intro i hi
    have hnum : num (idx (fieldK qs w i)) ≤ M := by
      rw [num_idx_fieldK h hi]
      exact hbound i hi
    simp only [num] at hnum
    omega
  refine ⟨fun i hi => ⟨fieldK_prime hsieve h hi (hbound i hi), hbound i hi⟩, fun p hp h5 hpM => ?_,
    fun i j hi hj hij => fieldK_injOn h hi hj hij⟩
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := mod_six_of_prime hp h5
  have hnum : num (idx p) = p := num_idx hmod
  have hidxpos : idx p ≠ 0 := by
    simp only [idx]
    omega
  have hbit : lit.testBit (idx p) :=
    (hsieve _ hidxpos (by rw [hnum]; exact hpM)).2 (by rw [hnum]; exact hp)
  have hltp : idx p < 32 * chunks := by
    simp only [idx]
    omega
  obtain ⟨i, hi, hti⟩ := exists_field_of_testBit h hpop hidx hbit hltp
  exact ⟨i, hi, by rw [← num_idx_fieldK h hi, hti, hnum]⟩

end PrimeCert.Polya
