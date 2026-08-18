/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Polya.Correct.PowerPack
public import PrimeCert.Complete

import Mathlib.Tactic.Ring

/-!
# The second block holds the remaining prime powers

`hpLoopK` walks the sieve positions from 1 upward and appends, at each set bit, the powers of that
position's prime from the square upward. `hpLoopK_spec` states what its state then holds: the
values are the powers named by `HpVal`, each exactly once.
-/

namespace PrimeCert.Polya

open PrimeCert.Sieve (IsSieve num numK numK_eq_num)

/-! ### One base -/

/-- With fuel past the largest exponent, one base contributes `seed * q ^ k` for every `k ≥ 1`
whose power is at most `M`. -/
theorem powLoopK_base {M w q seed st c pw V e : ℕ} (h : IsPowState w st c pw V) (hq : 2 ≤ q)
    (hseed : 1 ≤ seed) (hseed64 : seed < 2 ^ 64) (hMw : M < 2 ^ w) (hM64 : M < 2 ^ 64)
    (hMe : M < 2 ^ e) (hroom : c + e + 1 < 2 ^ 64) :
    ∃ m ≤ e, ∃ V', IsPowState w (powLoopK M w q seed st e) (c + m) (seed * q ^ m) V' ∧
      (∀ j < c, entryK V' w j = entryK V w j) ∧
        (∀ j < m, entryK V' w (c + j) = seed * q ^ (j + 1)) ∧
          (∀ j < m, seed * q ^ (j + 1) ≤ M) ∧ (∀ k, 1 ≤ k → seed * q ^ k ≤ M → k ≤ m) := by
  obtain ⟨m, hme, V', hstate, hbelow, hentries, hle, htop⟩ :=
    powLoopK_spec e h hq hseed64 hMw hM64 hroom
  refine ⟨m, hme, V', hstate, hbelow, hentries, hle, fun k hk hkM => ?_⟩
  by_contra hgt
  have hmlt : m < e := by
    by_contra hge
    have hpow : 2 ^ e ≤ q ^ e := Nat.pow_le_pow_left hq e
    have hlt : q ^ e < q ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
    have hmul : q ^ k ≤ seed * q ^ k := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hmono : seed * q ^ (m + 1) ≤ seed * q ^ k :=
    Nat.mul_le_mul_left seed (Nat.pow_le_pow_right (by omega) (by omega))
  have := htop hmlt
  omega

/-! ### The values collected -/

/-- The powers collected from the sieve positions below `pos`, together with the powers of 2 and of
3 that seed the walk. -/
@[expose] public def HpVal (lit M pos v : ℕ) : Prop :=
  (∃ k, 1 ≤ k ∧ v = 2 ^ k ∧ v ≤ M) ∨ (∃ k, 1 ≤ k ∧ v = 3 ^ k ∧ v ≤ M) ∨
    ∃ t, 1 ≤ t ∧ t < pos ∧ lit.testBit t ∧ (num t).Prime ∧
      ∃ k, 2 ≤ k ∧ v = num t ^ k ∧ v ≤ M

/-- The number at a positive index is at least 5. -/
theorem five_le_num {t : ℕ} (ht : 1 ≤ t) : 5 ≤ num t := by grind [num]

theorem num_inj {t t' : ℕ} (h : num t = num t') : t = t' := by grind [num]

/-- Prime powers with the same value have the same base. -/
theorem prime_base_eq {p r a b : ℕ} (hp : p.Prime) (hr : r.Prime) (ha : 1 ≤ a)
    (h : p ^ a = r ^ b) : p = r := by
  grind [Nat.prime_dvd_prime_iff_eq, Nat.Prime.dvd_of_dvd_pow, dvd_pow_self]

/-- A value collected before position `t` is none of the powers of the prime at `t`. -/
theorem HpVal.ne_pow {lit M pos t k v : ℕ} (h : HpVal lit M pos v) (ht : pos ≤ t) (h1 : 1 ≤ t)
    (hprime : (num t).Prime) (hk : 1 ≤ k) : v ≠ num t ^ k := by
  intro hv
  have hfive := five_le_num h1
  rcases h with ⟨a, ha, hva, -⟩ | ⟨a, ha, hva, -⟩ | ⟨t', ht1, ht'pos, -, hp', a, ha, hva, -⟩
  · have : num t = 2 := prime_base_eq (b := a) hprime Nat.prime_two hk (by rw [← hv, hva])
    omega
  · have : num t = 3 := prime_base_eq (b := a) hprime Nat.prime_three hk (by rw [← hv, hva])
    omega
  · have hbase : num t = num t' := prime_base_eq (b := a) hprime hp' hk (by rw [← hv, hva])
    have := num_inj hbase
    omega

/-- Peel the top position, as a test on the sieve bit. -/
theorem hpLoopK_succ_eq (lit M w e st start fuel : ℕ) :
    hpLoopK lit M w e st start (fuel + 1)
      = if lit.testBit (start + fuel) then
          powLoopK M w (num (start + fuel)) (num (start + fuel))
            (hpLoopK lit M w e st start fuel) e
        else hpLoopK lit M w e st start fuel := by
  rw [hpLoopK_succ, numK_eq_num]
  have hb : Nat.ble 1 ((lit.shiftRight (start + fuel)).land 1) = lit.testBit (start + fuel) := by
    simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod,
      Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    have h2 : lit / 2 ^ (start + fuel) % 2 = 0 ∨ lit / 2 ^ (start + fuel) % 2 = 1 := by omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> rfl
  rw [hb]
  cases lit.testBit (start + fuel) <;> rfl

/-- The values collected only grow as the walk advances. -/
theorem HpVal.mono {lit M pos pos' v : ℕ} (h : HpVal lit M pos v) (hle : pos ≤ pos') :
    HpVal lit M pos' v := by
  rcases h with h | h | ⟨t, ht1, htlt, hrest⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨t, ht1, by omega, hrest⟩)

/-- A position with a clear bit contributes nothing. -/
theorem HpVal.of_not_testBit {lit M pos v : ℕ} (h : HpVal lit M (pos + 1) v)
    (hbit : lit.testBit pos = false) : HpVal lit M pos v := by
  rcases h with h | h | ⟨t, ht1, htlt, htbit, hrest⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨t, ht1, ?_, htbit, hrest⟩)
    rcases Nat.lt_or_ge t pos with h' | h'
    · exact h'
    · rw [(by omega : t = pos), hbit] at htbit
      exact absurd htbit (by simp)

/-- What the walk holds: the values named by `HpVal`, each in exactly one entry. -/
public theorem hpLoopK_spec {lit M w e st c pw V start : ℕ} (fuel : ℕ) (hsieve : IsSieve M lit)
    (hstate : IsPowState w st c pw V) (hMw : M < 2 ^ w) (hM64 : M < 2 ^ 64) (hMe : M < 2 ^ e)
    (hroom : c + e * fuel + e + 1 < 2 ^ 64) (hstart : 1 ≤ start)
    (hnum : ∀ t, t < start + fuel → num t ≤ M)
    (hsound : ∀ j < c, HpVal lit M start (entryK V w j))
    (hcomp : ∀ v, HpVal lit M start v → ∃ j < c, entryK V w j = v)
    (hinj : ∀ j₁ j₂, j₁ < c → j₂ < c → entryK V w j₁ = entryK V w j₂ → j₁ = j₂) :
    ∃ c' pw' V', IsPowState w (hpLoopK lit M w e st start fuel) c' pw' V' ∧
      c ≤ c' ∧ c' ≤ c + e * fuel ∧
        (∀ j < c', HpVal lit M (start + fuel) (entryK V' w j)) ∧
          (∀ v, HpVal lit M (start + fuel) v → ∃ j < c', entryK V' w j = v) ∧
            (∀ j₁ j₂, j₁ < c' → j₂ < c' → entryK V' w j₁ = entryK V' w j₂ → j₁ = j₂) := by
  induction fuel with
  | zero =>
    exact ⟨c, pw, V, hstate, le_rfl, by omega, by simpa using hsound, by simpa using hcomp, hinj⟩
  | succ f ih =>
    have hmul : e * (f + 1) = e * f + e := by ring
    obtain ⟨c', pw', V', hstate', hcc', hc'le, hsound', hcomp', hinj'⟩ :=
      ih (by omega) (fun t ht => hnum t (by omega))
    rw [hpLoopK_succ_eq]
    rcases hbit : lit.testBit (start + f) with _ | _
    · rw [if_neg Bool.false_ne_true]
      refine ⟨c', pw', V', hstate', hcc', by omega, fun j hj => ?_, fun v hv => ?_, hinj'⟩
      · exact (hsound' j hj).mono (by omega)
      · exact hcomp' v (hv.of_not_testBit hbit)
    · rw [if_pos rfl]
      have hnumle : num (start + f) ≤ M := hnum _ (by omega)
      have hprime : (num (start + f)).Prime :=
        (hsieve (start + f) (by omega) hnumle).1 hbit
      have hfive : 5 ≤ num (start + f) := five_le_num (by omega)
      have h2q : 2 ≤ num (start + f) := by omega
      have h1q : 1 ≤ num (start + f) := by omega
      have hq64 : num (start + f) < 2 ^ 64 := by omega
      have hroom' : c' + e + 1 < 2 ^ 64 := by omega
      obtain ⟨m, hme, V'', hstate'', hbelow, hentries, hlem, hall⟩ :=
        powLoopK_base hstate' h2q h1q hq64 hMw hM64 hMe hroom'
      refine ⟨c' + m, num (start + f) * num (start + f) ^ m, V'', hstate'', by omega, by omega,
        fun j hj => ?_, fun v hv => ?_, fun j₁ j₂ hj₁ hj₂ heq => ?_⟩
      · -- soundness
        rcases Nat.lt_or_ge j c' with hjc | hjc
        · rw [hbelow j hjc]
          exact (hsound' j hjc).mono (by omega)
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjc
          have hdm : d < m := by omega
          refine Or.inr (Or.inr
            ⟨start + f, by omega, by omega, hbit, hprime, d + 2, by omega, ?_, ?_⟩)
          · rw [hentries d hdm, Nat.pow_succ]
            ring
          · rw [hentries d hdm]
            exact hlem d hdm
      · -- completeness
        have hprev : ∀ u, HpVal lit M (start + f) u → ∃ j < c' + m, entryK V'' w j = u := by
          intro u hu
          obtain ⟨j, hj, hjv⟩ := hcomp' u hu
          exact ⟨j, by omega, by rw [hbelow j hj, hjv]⟩
        rcases hv with h | h | ⟨t, ht1, htlt, htbit, htp, k, hk, hvk, hvM⟩
        · exact hprev v (Or.inl h)
        · exact hprev v (Or.inr (Or.inl h))
        · rcases Nat.lt_or_ge t (start + f) with htf | htf
          · exact hprev v (Or.inr (Or.inr ⟨t, ht1, htf, htbit, htp, k, hk, hvk, hvM⟩))
          · obtain rfl : t = start + f := by omega
            have hk1 : num (start + f) * num (start + f) ^ (k - 1) = num (start + f) ^ k := by
              rw [← Nat.pow_succ']
              congr 1
              omega
            have hkm : k - 1 ≤ m := hall (k - 1) (by omega) (by rwa [hk1, ← hvk])
            refine ⟨c' + (k - 2), by omega, ?_⟩
            rw [hentries (k - 2) (by omega), hvk]
            rwa [(by omega : k - 2 + 1 = k - 1)]
      · -- injectivity
        have hcross : ∀ a b, a < c' → c' ≤ b → b < c' + m →
            entryK V'' w a ≠ entryK V'' w b := by
          intro a b ha hb hbm heq'
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
          rw [hbelow a ha, hentries d (by omega)] at heq'
          refine (hsound' a ha).ne_pow le_rfl (by omega) hprime (k := d + 2) (by omega) ?_
          rw [heq', Nat.pow_succ]
          ring
        rcases Nat.lt_or_ge j₁ c' with h₁ | h₁ <;> rcases Nat.lt_or_ge j₂ c' with h₂ | h₂
        · rw [hbelow j₁ h₁, hbelow j₂ h₂] at heq
          exact hinj' j₁ j₂ h₁ h₂ heq
        · exact absurd heq (hcross j₁ j₂ h₁ h₂ hj₂)
        · exact absurd heq.symm (hcross j₂ j₁ h₂ h₁ hj₁)
        · obtain ⟨d₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
          obtain ⟨d₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
          rw [hentries d₁ (by omega), hentries d₂ (by omega), ← Nat.pow_succ',
            ← Nat.pow_succ'] at heq
          have := Nat.pow_right_injective h2q heq
          omega

/-! ### The seed -/

/-- The state seeding the walk holds the powers of 2 and of 3 up to `M`, each in one entry. -/
public theorem seed_spec {M w e : ℕ} (lit : ℕ) (hMw : M < 2 ^ w) (hM64 : M < 2 ^ 64)
    (hMe : M < 2 ^ e) (hroom : e + e + 1 < 2 ^ 64) :
    ∃ c pw V, IsPowState w (powLoopK M w 3 1 (powLoopK M w 2 1 0 e) e) c pw V ∧ c ≤ e + e ∧
      (∀ j < c, HpVal lit M 1 (entryK V w j)) ∧
        (∀ v, HpVal lit M 1 v → ∃ j < c, entryK V w j = v) ∧
          (∀ j₁ j₂, j₁ < c → j₂ < c → entryK V w j₁ = entryK V w j₂ → j₁ = j₂) := by
  have h164 : (1 : ℕ) < 2 ^ 64 := by norm_num
  have hzero : IsPowState w 0 0 0 0 := ⟨by simp, Nat.two_pow_pos 64, Nat.two_pow_pos 64, by simp⟩
  obtain ⟨m₂, hm₂, V₂, hst₂, -, hf₂, hle₂, hall₂⟩ :=
    powLoopK_base (q := 2) (seed := 1) hzero (by omega) (by omega) h164 hMw hM64 hMe (by omega)
  simp only [Nat.zero_add, Nat.one_mul] at hst₂ hf₂ hle₂ hall₂
  obtain ⟨m₃, hm₃, V₃, hst₃, hb₃, hf₃, hle₃, hall₃⟩ :=
    powLoopK_base (q := 3) (seed := 1) hst₂ (by omega) (by omega) h164 hMw hM64 hMe (by omega)
  simp only [Nat.one_mul] at hst₃ hf₃ hle₃ hall₃
  refine ⟨m₂ + m₃, _, V₃, hst₃, by omega, fun j hj => ?_, fun v hv => ?_,
    fun j₁ j₂ hj₁ hj₂ heq => ?_⟩
  · rcases Nat.lt_or_ge j m₂ with hjm | hjm
    · rw [hb₃ j hjm, hf₂ j hjm]
      exact Or.inl ⟨j + 1, by omega, rfl, hle₂ j hjm⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjm
      rw [hf₃ d (by omega)]
      exact Or.inr (Or.inl ⟨d + 1, by omega, rfl, hle₃ d (by omega)⟩)
  · rcases hv with ⟨k, hk, hvk, hvM⟩ | ⟨k, hk, hvk, hvM⟩ | ⟨t, ht1, htlt, -⟩
    · have hkm : k ≤ m₂ := hall₂ k hk (by rwa [← hvk])
      refine ⟨k - 1, by omega, ?_⟩
      rw [hb₃ (k - 1) (by omega), hf₂ (k - 1) (by omega), hvk]
      congr 1
      omega
    · have hkm : k ≤ m₃ := hall₃ k hk (by rwa [← hvk])
      refine ⟨m₂ + (k - 1), by omega, ?_⟩
      rw [hf₃ (k - 1) (by omega), hvk]
      congr 1
      omega
    · omega
  · have hcross : ∀ a b, a < m₂ → m₂ ≤ b → b < m₂ + m₃ → entryK V₃ w a ≠ entryK V₃ w b := by
      intro a b ha hb hbm heq'
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
      rw [hb₃ a ha, hf₂ a ha, hf₃ d (by omega)] at heq'
      exact absurd (prime_base_eq Nat.prime_two Nat.prime_three (by omega) heq') (by omega)
    rcases Nat.lt_or_ge j₁ m₂ with h₁ | h₁ <;> rcases Nat.lt_or_ge j₂ m₂ with h₂ | h₂
    · rw [hb₃ j₁ h₁, hb₃ j₂ h₂, hf₂ j₁ h₁, hf₂ j₂ h₂] at heq
      have := Nat.pow_right_injective (le_refl 2) heq
      omega
    · exact absurd heq (hcross j₁ j₂ h₁ h₂ hj₂)
    · exact absurd heq.symm (hcross j₂ j₁ h₂ h₁ hj₁)
    · obtain ⟨d₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
      obtain ⟨d₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
      rw [hf₃ d₁ (by omega), hf₃ d₂ (by omega)] at heq
      have := Nat.pow_right_injective (by omega : 2 ≤ 3) heq
      omega

/-! ### The closed form -/

/-- What a full walk collects: the prime powers up to `M` with base 2 or 3, and those with
exponent at least two. -/
public theorem hpVal_iff {lit M fuel v : ℕ} (hsieve : IsSieve M lit)
    (hfuel : M < (3 * fuel + 4) * (3 * fuel + 4)) :
    HpVal lit M (1 + fuel) v ↔
      ∃ p k, p.Prime ∧ 1 ≤ k ∧ v = p ^ k ∧ v ≤ M ∧ (p < 5 ∨ 2 ≤ k) := by
  constructor
  · rintro (⟨k, hk, hvk, hvM⟩ | ⟨k, hk, hvk, hvM⟩ | ⟨t, ht1, htlt, htbit, htp, k, hk, hvk, hvM⟩)
    · exact ⟨2, k, Nat.prime_two, hk, hvk, hvM, Or.inl (by omega)⟩
    · exact ⟨3, k, Nat.prime_three, hk, hvk, hvM, Or.inl (by omega)⟩
    · exact ⟨num t, k, htp, by omega, hvk, hvM, Or.inr hk⟩
  · rintro ⟨p, k, hp, hk, hvk, hvM, hcase⟩
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have h2 := hp.two_le
      have hp23 : p = 2 ∨ p = 3 := by
        rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hp
          exact absurd hp (by decide)
      rcases hp23 with rfl | rfl
      · exact Or.inl ⟨k, hk, hvk, hvM⟩
      · exact Or.inr (Or.inl ⟨k, hk, hvk, hvM⟩)
    · have hk2 : 2 ≤ k := by omega
      have hsq : p * p ≤ M := by
        have hmono : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
        rw [Nat.pow_two] at hmono
        omega
      have hplt : p < 3 * fuel + 4 := by
        by_contra hge
        have hsqge : (3 * fuel + 4) * (3 * fuel + 4) ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hnumidx : num (idx p) = p := num_idx (mod_six_of_prime hp (by omega))
      have hidx : 1 ≤ idx p ∧ idx p ≤ fuel := by
        simp only [idx]
        omega
      have hprime : (num (idx p)).Prime := by rwa [hnumidx]
      have hpM : p ≤ M := by
        have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
        omega
      have hbit : lit.testBit (idx p) :=
        (hsieve _ (by omega) (by rw [hnumidx]; omega)).2 hprime
      exact Or.inr (Or.inr ⟨idx p, hidx.1, by omega, hbit, hprime, k, hk2,
        by rw [hnumidx]; exact hvk, hvM⟩)

end PrimeCert.Polya
