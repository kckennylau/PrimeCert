/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.BitCheck
public import PrimeCert.Ones

/-!
# The packed primes are every prime up to the cutoff

The entries map injectively to set positions of the sieve, and the counted positions match the
number of entries, so the map is onto: every prime from 5 to the cutoff sits in an entry
(`primeBlock_spec`).
-/

namespace PrimeCert

open Sieve (IsSieve value index value_index)

/-- The blockwise count is the count of set positions. -/
public theorem popcLoopK_eq_bitSum (b acc fuel : ℕ) :
    popcLoopK b acc 0 fuel = acc + bitSum b (64 * fuel) := by
  induction fuel with
  | zero => simp [popcLoopK, bitSum]
  | succ f ih =>
    rw [popcLoopK_succ]
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.land_eq, Nat.shiftRight_eq',
      Nat.shiftLeft_eq', Nat.zero_add]
    rw [Nat.mul_comm f 64, popc64K_chunk, ih, Nat.mul_succ, bitSum_add, Nat.add_assoc]

/-- The number at an index rises with the index. -/
theorem value_le_value {t t' : ℕ} (h : t ≤ t') : value t ≤ value t' := by grind [value]

/-- Every entry sits below the cutoff, since the top one does and the entries rise. -/
theorem entryK_le {qs w lit cnt M : ℕ} (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    (htop : 0 < cnt → value (bitCheckLoopK qs w lit 1 0 cnt / 2) ≤ M)
    {i : ℕ} (hi : i < cnt) : entryK qs w i ≤ M := by
  obtain ⟨-, hmono, hlast⟩ := bitCheckLoopK_spec cnt h
  have hcnt : 0 < cnt := by lia
  have htopidx : bitCheckLoopK qs w lit 1 0 cnt / 2 = index (entryK qs w (cnt - 1)) := hlast hcnt
  have hle : index (entryK qs w i) ≤ index (entryK qs w (cnt - 1)) := by
    rcases Nat.lt_or_ge i (cnt - 1) with hlt | hge
    · exact Nat.le_of_lt (hmono i (cnt - 1) hlt (by lia))
    · rw [(by lia : i = cnt - 1)]
  have htopvalue := htop hcnt
  rw [htopidx] at htopvalue
  rw [← value_index_entryK h hi]
  exact le_trans (value_le_value hle) htopvalue

/-- The set positions of the sieve are exactly the sieve indices of the packed entries: the entries
inject into them and the counts agree. -/
theorem exists_entry_of_testBit {qs w lit cnt chunks : ℕ}
    (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1) (hpop : popcLoopK lit 0 0 chunks = cnt)
    (hlt : ∀ i, i < cnt → index (entryK qs w i) < 64 * chunks)
    {t : ℕ} (ht : lit.testBit t) (htlt : t < 64 * chunks) :
    ∃ i < cnt, index (entryK qs w i) = t := by
  obtain ⟨htests, hmono, -⟩ := bitCheckLoopK_spec cnt h
  have hcard : ({i ∈ Finset.range (64 * chunks) | lit.testBit i}).card = cnt := by
    rw [← bitSum_eq_card, ← Nat.zero_add (bitSum lit (64 * chunks)), ← popcLoopK_eq_bitSum, hpop]
  have hsub : (Finset.range cnt).image (fun i ↦ index (entryK qs w i))
      ⊆ {i ∈ Finset.range (64 * chunks) | lit.testBit i} := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt i hi, testBit_iff_shiftRight_mod_two.2 (htests i hi).2.2⟩
  have himg : ((Finset.range cnt).image (fun i ↦ index (entryK qs w i))).card = cnt := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    exact fun a ha b hb hab ↦ eq_of_mono hmono (by simpa using ha) (by simpa using hb) hab
  have hmem : t ∈ (Finset.range cnt).image (fun i ↦ index (entryK qs w i)) := by
    rw [Finset.eq_of_subset_of_card_le hsub (by lia)]
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 htlt, ht⟩
  simpa only [Finset.mem_image, Finset.mem_range] using hmem

/-- A prime of at least 5 is coprime to 6. -/
public theorem mod_six_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := fun hd ↦ by rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> lia
  have h3 : ¬ (3 ∣ p) := fun hd ↦ by rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> lia
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3
  lia

/-- What the two loops say about the block of packed primes: every entry is a prime from 5 to the
cutoff, every such prime is an entry, and the entries are distinct. -/
public theorem primeBlock_spec {qs w lit M cnt chunks : ℕ} (hsieve : IsSieve M lit)
    (h : bitCheckLoopK qs w lit 1 0 cnt % 2 = 1)
    (htop : 0 < cnt → value (bitCheckLoopK qs w lit 1 0 cnt / 2) ≤ M)
    (hpop : popcLoopK lit 0 0 chunks = cnt) (hchunks : (M - 1) / 3 < 64 * chunks) :
    (∀ i < cnt, (entryK qs w i).Prime ∧ 5 ≤ entryK qs w i ∧ entryK qs w i ≤ M) ∧
      (∀ p, p.Prime → 5 ≤ p → p ≤ M → ∃ i < cnt, entryK qs w i = p) ∧
        (∀ i j, i < cnt → j < cnt → entryK qs w i = entryK qs w j → i = j) := by
  have hbound : ∀ i, i < cnt → entryK qs w i ≤ M := fun i hi ↦ entryK_le h htop hi
  have hfive : ∀ i, i < cnt → 5 ≤ entryK qs w i := by
    intro i hi
    obtain ⟨htests, -, -⟩ := bitCheckLoopK_spec cnt h
    obtain ⟨hmod, hpos, -⟩ := htests i hi
    simp only [index] at hpos
    lia
  have hidx : ∀ i, i < cnt → index (entryK qs w i) < 64 * chunks := by
    intro i hi
    have hvalue : value (index (entryK qs w i)) ≤ M := by
      rw [value_index_entryK h hi]; exact hbound i hi
    simp only [value] at hvalue
    lia
  refine ⟨fun i hi ↦ ⟨entryK_prime hsieve h hi (hbound i hi), hfive i hi, hbound i hi⟩,
    fun p hp h5 hpM ↦ ?_,
    fun i j hi hj hij ↦ entryK_injOn h hi hj hij⟩
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := mod_six_of_prime hp h5
  have hvalue : value (index p) = p := value_index hmod
  have hidxpos : index p ≠ 0 := by simp only [index]; lia
  have hbit : lit.testBit (index p) := (hsieve _ hidxpos (by rwa [hvalue])).2 (by rwa [hvalue])
  have hltp : index p < 64 * chunks := by simp only [index]; lia
  obtain ⟨i, hi, hti⟩ := exists_entry_of_testBit h hpop hidx hbit hltp
  exact ⟨i, hi, by rw [← value_index_entryK h hi, hti, hvalue]⟩

end PrimeCert
