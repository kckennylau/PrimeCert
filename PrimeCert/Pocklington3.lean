/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.Pocklington

/-! # An improved version of Pocklington's primality test -/

#check PocklingtonPred
#check pocklington_test

theorem Nat.prime_iff_not_exists_mul_eq' (p : ℕ) :
    Nat.Prime p ↔ 2 ≤ p ∧ ¬∃ m n, 2 ≤ m ∧ m < p ∧ 2 ≤ n ∧ n < p ∧ m * n = p := by
  rw [prime_iff_not_exists_mul_eq]
  refine and_congr_right fun hp ↦ not_congr <| exists_congr fun m ↦ exists_congr fun n ↦ ?_
  refine ⟨fun ⟨hmp, hnp, hmnp⟩ ↦ ⟨?_, hmp, ?_, hnp, hmnp⟩, by tauto⟩
  · by_contra hm; interval_cases m <;> grind
  · by_contra hn; interval_cases n <;> grind

theorem Nat.modEq_prod {ι : Type*} {s : Finset ι} {f g : ι → ℕ} {b : ℕ}
    (hb : ∀ i ∈ s, f i ≡ g i [MOD b]) : (∏ i ∈ s, f i) ≡ (∏ i ∈ s, g i) [MOD b] := by
  classical induction s using Finset.induction with
  | empty => simp; rfl
  | insert a s has ih => simp_rw [Finset.prod_insert has]; exact Nat.ModEq.mul (by grind) (by grind)

theorem Nat.modEq_one_of_dvd_of_prime (n b : ℕ) (prime : ∀ p, Nat.Prime p → p ∣ n → p ≡ 1 [MOD b])
    (d : ℕ) (hdn : d ∣ n) : d ≡ 1 [MOD b] := by
  by_cases hn : n = 0
  · have := prime 2 prime_two <| hn ▸ dvd_zero _
    rw [ModEq.comm, modEq_iff_dvd' (by grind), dvd_one] at this
    exact this ▸ modEq_one
  have hd : d ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hdn; grind
  rw [← factorization_prod_pow_eq_self hd, Finsupp.prod,
    ← Finset.prod_const_one (s := d.factorization.support)]
  refine modEq_prod fun p hp ↦ ?_
  rw [support_factorization, mem_primeFactors] at hp
  exact ((prime p hp.1 (hp.2.1.trans hdn)).pow _).trans <| by simp; rfl

theorem Nat.modEq_iff_exists_mul_add {p q b : ℕ} (hqb : q < b) :
    p ≡ q [MOD b] ↔ ∃ k, k * b + q = p := by
  rw [ModEq]
  constructor
  · intro h
    rw [mod_eq_of_lt hqb] at h
    exact ⟨p / b, by rw [← h, Nat.div_add_mod']⟩
  · rintro ⟨k, rfl⟩
    rw [mul_add_mod']

theorem Nat.modEq_iff_exists_mul_add' {p q b : ℕ} (hqp : q ≤ p) :
    p ≡ q [MOD b] ↔ ∃ k, k * b + q = p := by
  rw [ModEq.comm, modEq_iff_dvd' hqp]
  rw [le_iff_exists_add'] at hqp
  obtain ⟨c, rfl⟩ := hqp
  simp_rw [add_tsub_cancel_right, add_left_inj, dvd_iff_exists_eq_mul_left, eq_comm]

theorem Nat.add_sq_eq_dist_sq_add_four_mul (c d : ℕ) :
    (c + d) ^ 2 = (max c d - min c d) ^ 2 + 4 * (c * d) := by
  wlog h : c ≤ d
  · rw [add_comm, max_comm, min_comm, mul_comm]; grind
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp h
  rw [max_eq_right h, min_eq_left h, Nat.add_sub_cancel_left]
  ring

section

set_option hygiene false
local notation "r" => (N - 1) / F₁ % (2 * F₁)
local notation "s" => (N - 1) / F₁ / (2 * F₁)

theorem pocklington3_test (N F₁ m : ℕ) (h2n : 2 ≤ N) (hn : Odd N) (hf₁ : F₁ ∣ N - 1)
    (hr₁ : Odd ((N - 1) / F₁))
    (primitive : ∀ p ∈ F₁.primeFactors, ∃ a, a ^ (N - 1) ≡ 1 [MOD N] ∧
      (a ^ ((N - 1) / p) - 1).gcd N = 1)
    (divisors : ∀ l, 1 ≤ l → l < m → ¬ l * F₁ + 1 ∣ N)
    (bound : N + (m * F₁ + 1) * (m * F₁) < (m * F₁ + 1) * (2 * F₁ ^ 2 + r * F₁ + 1))
    (cert : (N - 1) / F₁ < 2 * F₁ ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s) :
    Nat.Prime N := by
  set r' := r with hr
  set s' := s with hs
  simp_rw [Nat.prime_iff_not_exists_mul_eq', not_exists, not_and]
  refine ⟨by grind, fun p q h2p hpn h2q hqn hpq ↦ ?_⟩
  have := pocklington_test N F₁ (by grind) hf₁ primitive
  replace this := Nat.modEq_one_of_dvd_of_prime _ _ this
  have hp := this p (hpq ▸ dvd_mul_right _ _)
  have hq := this q (hpq ▸ dvd_mul_left _ _)
  rw [Nat.modEq_iff_exists_mul_add' (by grind)] at hp hq
  obtain ⟨c, rfl⟩ := hp
  obtain ⟨d, rfl⟩ := hq
  have hmc : m ≤ c := le_of_not_gt fun hcm ↦ by
    obtain hc | hc := le_or_gt 1 c
    · exact divisors c hc hcm (hpq ▸ dvd_mul_right _ _)
    · interval_cases c; rw [zero_mul] at h2p; grind
  have hmd : m ≤ d := le_of_not_gt fun hdm ↦ by
    obtain hd | hd := le_or_gt 1 d
    · exact divisors d hd hdm (hpq ▸ dvd_mul_left _ _)
    · interval_cases d; rw [zero_mul] at h2q; grind
  obtain ⟨R₁, hR⟩ := hf₁
  have hR₁ := (Nat.sub_eq_iff_eq_add <| by grind).mp hR
  have hf₀ : F₁ ≠ 0 := by rintro rfl; rw [zero_mul] at hR₁; grind
  rw [hR, Nat.mul_div_cancel_left _ (by grind)] at hr hs hr₁ cert
  have hR₂ := Nat.div_add_mod R₁ (2 * F₁)
  rw [← hr, ← hs] at hR₂
  rw [hR₁,
    show (c * F₁ + 1) * (d * F₁ + 1) = F₁ * ((c * d) * F₁ + (c + d)) + 1 by ring,
    add_left_inj, Nat.mul_right_inj hf₀] at hpq
  have even_f₁ : Even F₁ := by
    rw [hR₁, Nat.odd_add_one, Nat.not_odd_iff_even, Nat.even_mul,
      ← Nat.not_odd_iff_even (n := R₁)] at hn; tauto
  have odd_cd : Odd (c + d) := by
    rw [← hpq] at hr₁
    refine (Nat.odd_add'.mp hr₁).mpr <| Even.mul_left even_f₁ _
  have even_cd : Even (c * d) := by
    rw [Nat.odd_add, ← Nat.not_even_iff_odd] at odd_cd
    rw [Nat.even_mul]; tauto
  have hcdr : (c + d) % (2 * F₁) = r' := by
    obtain ⟨q, hq⟩ := even_iff_exists_two_mul.mp even_cd
    replace hpq := congr($hpq % (2 * F₁))
    rwa [hq, mul_right_comm, Nat.mul_add_mod, ← hr] at hpq
  have hcdm : (c + d) * m ≤ c * d + m ^ 2 := by
    rw [add_mul]
    obtain ⟨c, hc⟩ := le_iff_exists_add.mp hmc
    obtain ⟨d, hd⟩ := le_iff_exists_add.mp hmd
    rw [hc, hd]
    grind
  have hcdr₁ : c + d < 2 * F₁ + r' := by
    rw [hR₁, ← hpq] at bound
    conv_lhs at bound => exact
      show _ = (c * d + m ^ 2) * F₁ ^ 2 + (c + d) * F₁ + (m * F₁ + 1) by ring
    grw [← hcdm] at bound
    conv_lhs at bound => exact show _ = (m * F₁ + 1) * ((c + d) * F₁ + 1) by ring
    rw [mul_lt_mul_iff_right₀ (by grind), add_lt_add_iff_right] at bound
    conv_rhs at bound => exact show _ = (2 * F₁ + r') * F₁ by ring
    rwa [mul_lt_mul_iff_left₀ (by grind)] at bound
  have hcdr₂ := Nat.div_add_mod (c + d) (2 * F₁)
  rw [hcdr] at hcdr₂
  rw [← hcdr₂, add_lt_add_iff_right, mul_lt_iff_lt_one_right (by grind), Nat.lt_one_iff] at hcdr₁
  rw [hcdr₁, mul_zero, zero_add] at hcdr₂
  have hscd := hR₂.trans hpq.symm
  rw [← hcdr₂, add_left_inj, mul_right_comm, mul_left_inj' (by grind)] at hscd
  obtain cert | cert := cert
  · -- first case: s = 0
    rw [← Nat.div_eq_zero_iff_lt (by grind), ← hs] at cert
    rw [cert, mul_zero, eq_comm, mul_eq_zero] at hscd
    grind
  · -- second case: r^2-8s is not square
    have square : r' ^ 2 = 8 * s' + (max c d - min c d) ^ 2 := by
      rw [hcdr₂, show 8 = 4 * 2 by rfl, mul_assoc, hscd, Nat.add_sq_eq_dist_sq_add_four_mul,
        add_comm]
    rw [square, Nat.add_sub_cancel_left] at cert
    obtain cert | cert := cert
    · exact cert ⟨_, sq _⟩
    · grind

end

def forallB (f : ℕ → Bool) (start len : ℕ) (step : ℕ := 1) : Bool :=
  (Nat.rec (motive := fun _ ↦ ℕ × Bool) (start, true)
    (fun _ ih ↦ ih.rec fun i b ↦ (eagerReduce (i.add step), f i && b)) len).2

theorem forallB_iff_range' (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n ∈ List.range' start len step, f n := by
  unfold forallB
  induction len with
  | zero => simp
  | succ len ih =>
    simp only [Bool.and_eq_true, ih, List.range'_concat, List.forall_mem_append,
      List.forall_mem_singleton, and_comm]
    refine and_congr_left fun _a ↦ Eq.congr_left <| congr_arg f ?_
    clear ih _a
    induction len with
    | zero => simp
    | succ len ih => simp only; rw [ih, eagerReduce, Nat.add_eq]; ring

theorem forallB_iff (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n < len, f (n * step + start) := by
  simp_rw [add_comm, mul_comm, forallB_iff_range', List.mem_range']; aesop

theorem forallB_iff' (f : ℕ → Bool) (start r len step : ℕ) :
    forallB f (start * step + r) len step ↔
    ∀ n, start ≤ n → n < start + len → f (n * step + r) := by
  simp_rw [forallB_iff, ← add_assoc, ← add_mul, le_iff_exists_add, exists_imp,
    forall_eq_apply_imp_iff, add_lt_add_iff_left, add_comm]

theorem forallB_one_iff (f : ℕ → Bool) (start len : ℕ) :
    forallB f start len ↔ ∀ n, start ≤ n → n < start + len → f n := by
  simp_rw [forallB_iff_range', List.mem_range'_1, and_imp]

/-
(N F₁ m : ℕ) (h2n : 2 ≤ N) (hn : Odd N) (hf₁ : F₁ ∣ N - 1) (hr₁ : Odd ((N - 1) / F₁))
  (primitive : ∀ p ∈ F₁.primeFactors, ∃ a, a ^ (N - 1) ≡ 1 [MOD N] ∧ (a ^ ((N - 1) / p) - 1).gcd N = 1)
  (divisors : ∀ (l : ℕ), 1 ≤ l → l < m → ¬l * F₁ + 1 ∣ N)
  (bound : N + (m * F₁ + 1) * (m * F₁) < (m * F₁ + 1) * (2 * F₁ ^ 2 + (N - 1) / F₁ % (2 * F₁) * F₁ + 1))
  (cert :
    (N - 1) / F₁ < 2 * F₁ ∨
      ¬IsSquare (((N - 1) / F₁ % (2 * F₁)) ^ 2 - 8 * ((N - 1) / F₁ / (2 * F₁))) ∨
        ((N - 1) / F₁ % (2 * F₁)) ^ 2 < 8 * ((N - 1) / F₁ / (2 * F₁))) :
  Nat.Prime N
-/

/--
Inputs:
* `N`: the number to be certified as prime
* `F`: an even divisor of `N-1`, fully factored, to be given as a literal
* `F'`: the odd part of `F`, given in factorised form
* `e`: the exponent of `2` in `F`, so that `F = 2^e * F'`
* `R`: the quotient `(N-1)/F`, odd, given as a literal.
* `root`: a pseudo-primitive root (for `F`)
* `m`: an arbitrary number (`> 0`), which should be small for better performance.
* `s, r := divmod(R, 2*F)`, given as literals
-/
theorem pocklington3_certKR (N F F' e R root m r s : ℕ) (hn : Nat.ble 2 N) (he : Nat.blt 0 e)
    (psp : (powModTR root N.pred N).beq 1)
    (pred : PocklingtonPred N root (Nat.pow 2 e |>.mul F'))
    (e_def : F = 2 ^ e * F') (hfr : N = F * R + 1) (odd_r : (R.mod 2).beq 1)
    (divisors : forallB (fun l ↦ Nat.blt 0 (N.mod l)) F.succ m.pred F)
    (r_def : r = R % (2 * F)) (s_def : s = R / (2 * F))
    (bound : N.add (m.mul F |>.succ |>.mul (m.mul F)) |>.blt
      (m.mul F |>.succ |>.mul (F.pow 2 |>.mul 2 |>.add (r.mul F |>.succ))))
    (cert : s.beq 0 ∨ ¬ IsSquare (r.pow 2 |>.sub (s.mul 8)) ∨ (r.pow 2 |>.blt (s.mul 8))) :
    Nat.Prime N := by
  simp only [Nat.ble_eq] at hn
  simp only [Nat.blt_eq] at he
  simp only [Nat.pred_eq_sub_one, Nat.beq_eq, powModTR_eq, powMod] at psp
  simp only [Nat.mod_eq_mod, Nat.beq_eq, ← Nat.odd_iff] at odd_r
  simp only [Nat.pow_eq, Nat.mul_eq] at pred
  simp only [Nat.mul_eq, Nat.succ_eq_add_one, Nat.add_eq, Nat.pow_eq, Nat.blt_eq] at bound
  simp only [Nat.pow_eq, Nat.mul_eq, Nat.sub_eq, Nat.blt_eq, Nat.beq_eq] at cert
  have hf₀ : F ≠ 0 := by rintro rfl; rw [zero_mul] at hfr; grind
  have R_def : R = (N - 1) / F := by
    rw [hfr, Nat.succ_sub_one, Nat.mul_div_cancel_left _ (by grind)]
  refine pocklington3_test N F m (by simpa using hn) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hfr, Nat.odd_add_one, Nat.not_odd_iff_even, e_def, mul_assoc]
    exact (Nat.even_pow.mpr ⟨even_two, by simpa [Nat.pos_iff_ne_zero] using he⟩).mul_right _
  · rw [hfr, Nat.succ_sub_one]; tauto
  · rwa [← R_def]
  · rw [← e_def, PocklingtonPred] at pred
    exact fun p hp ↦ ⟨root, by rwa [Nat.ModEq, Nat.one_mod_eq_one.mpr (by grind)], by tauto⟩
  · rw [show F.succ = 1 * F + 1 by simp, forallB_iff'] at divisors
    simp only [Nat.pred_eq_sub_one, Nat.mod_eq_mod, Nat.blt_eq, Nat.pos_iff_ne_zero, ne_eq,
      ← Nat.dvd_iff_mod_eq_zero] at divisors
    exact fun l hl₁ hl₂ ↦ divisors l hl₁ (by grind)
  · rwa [← R_def, ← r_def, mul_comm 2]
  · rwa [← R_def, ← r_def, ← s_def, mul_comm 8, ← Nat.div_eq_zero_iff_lt (by grind), ← s_def]
