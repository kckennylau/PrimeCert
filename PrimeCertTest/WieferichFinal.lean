/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import PrimeCertTest.WieferichClasses
public import PrimeCert.WieferichBound
public import PrimeCert.ForallB
public import PrimeCert.ForMathlib
meta import PrimeCert.Meta.QuickRfl

/-! # No prime below 1000000 is Wieferich, apart from 1093 and 3511 -/

namespace PrimeCert.Wieferich

open PrimeCert

/-- A residue coprime to 2310 is one the class theorems cover, or one of the two cut out. -/
@[expose] public noncomputable def coverAt (r : ℕ) : Bool :=
  ((Nat.gcd r 2310).beq 1).not'.or'
    ((memB r classes_2310).or' ((r.beq 1093).or' (r.beq 1201)))

set_option maxRecDepth 40000 in
public theorem cover : forallB coverAt 0 2310 1 := by quickRfl

/-- A remainder coprime to 2310 falls into one of the three cases. -/
public theorem residue_cases {r : ℕ} (hr : r < 2310) (hg : Nat.gcd r 2310 = 1) :
    r ∈ classes_2310 ∨ r = 1093 ∨ r = 1201 := by
  have h := (forallB_iff coverAt 0 2310 1).mp cover r (by omega)
  rw [coverAt] at h
  simp only [Nat.mul_one, Nat.add_zero, hg, Bool.not'_eq_not, Bool.or'_eq_or, Nat.beq_eq,
    Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h | h
  · exact Or.inl (memB_iff.mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- A prime above 11 shares no factor with 2310. -/
public theorem gcd_2310_of_prime {p : ℕ} (hp : p.Prime) (h : 11 < p) : Nat.gcd p 2310 = 1 := by
  have hc : Nat.Coprime p 2310 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    rw [show (2310 : ℕ) = 2 * 3 * 5 * 7 * 11 by norm_num] at hdvd
    simp only [Nat.Prime.dvd_mul hp] at hdvd
    rcases hdvd with ((((h | h) | h) | h) | h) <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  exact hc

/-- No prime below 1000000 satisfies `2 ^ (p - 1) ≡ 1 [MOD p ^ 2]`, apart from 1093 and 3511. -/
public theorem not_wieferich {p : ℕ} (hp : p.Prime) (hb : p < 1000000)
    (h1 : p ≠ 1093) (h2 : p ≠ 3511) : ¬ Wieferich p := by
  rcases Nat.lt_or_ge p 12 with hs | hs
  · have hsmall : ∀ q, q < 12 → q.Prime → ¬ Wieferich q := by
      simp only [Wieferich, Nat.ModEq]
      decide
    exact hsmall p hs hp
  have hc : p % 6 = 1 ∨ p % 6 = 5 := hp.mod_six_eq_one_or_five (by omega) (by omega)
  have hg := gcd_2310_of_prime hp (by omega)
  have hr : Nat.gcd (p % 2310) 2310 = 1 := by
    rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hg
  have hlt : p % 2310 < 2310 := Nat.mod_lt _ (by norm_num)
  have hk : p / 2310 < 433 := by omega
  have h6 : p % 2310 % 6 = 1 ∨ p % 2310 % 6 = 5 := by omega
  have h1' : 1 ≤ p % 2310 := by
    rcases Nat.eq_zero_or_pos (p % 2310) with h | h
    · rw [h] at hr; simp at hr
    · exact h
  rcases residue_cases hlt hr with hm | hm | hm
  · exact not_wieferich_of_fold hp hb (by norm_num) hc h1' h6 hk (all_classes_2310 _ hm)
  · -- remainder 1093, whose own position was cut out
    refine not_wieferich_of_check hp hb hc ?_
    have hkpos : 1 ≤ p / 2310 := by
      rcases Nat.eq_zero_or_pos (p / 2310) with h | h
      · exfalso; apply h1; omega
      · exact h
    have := check_of_offset (r := 1093) (m := 2310) (s := 770) (j := 1) (k := p / 2310)
      (len := 432) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hkpos (by omega)
      class_2310_1093_above_1093
    rwa [← hm, Nat.mod_add_div] at this
  · -- remainder 1201, whose second position was cut out
    refine not_wieferich_of_check hp hb hc ?_
    rcases Nat.lt_or_ge (p / 2310) 1 with hlo | hlo
    · have := check_of_class (r := 1201) (m := 2310) (k := p / 2310) (len := 1) (by norm_num)
        (by norm_num) (by norm_num) hlo class_2310_1201_below_3511
      rwa [← hm, Nat.mod_add_div] at this
    · have hk2 : 2 ≤ p / 2310 := by
        rcases Nat.lt_or_ge (p / 2310) 2 with h | h
        · exfalso; apply h2; omega
        · exact h
      have := check_of_offset (r := 1201) (m := 2310) (s := 770) (j := 2) (k := p / 2310)
        (len := 431) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2 (by omega)
        class_2310_1201_above_3511
      rwa [← hm, Nat.mod_add_div] at this

end PrimeCert.Wieferich
