/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve
import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Correctness of the mod-6 wheel sieve

Relates the bitset computed by `PrimeCert.Sieve.sieveK` to a `testBit`-level specification.
The optimized kernel defs use raw `Nat.rec`/`Nat.*` operations; the Mathlib bit lemmas are phrased
with `<<<`/`|||`/`&&&` notation (definitionally equal), so the proofs relate the two forms.

Layered:
* **Layer 1** – `bitVal` equals `testBit`, the index↔number encoding `num`, the bits of `initK`.
* **Layer 2** – `buildMaskK` sets exactly the two stride-`2p` progressions (`testBit_buildMaskK`).
* **Layer 3a** – `markMaskK` clears exactly the bits set in `buildMaskK` (`testBit_markMaskK`).
* **Layer 3b** – those bits are the coprime-to-6 multiples of `p` from `5p` on (`mask_iff`).
* **Layer 4** – the surviving bits are exactly the primes (`sieveK_testBit_iff`).
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Layer 1: bit reading and encoding -/

/-- `bitVal` reads bit `i` as a `Nat` (`0` or `1`); it agrees with `Nat.testBit`. -/
theorem bitVal_eq_testBit (b i : Nat) : bitVal b i = if b.testBit i then 1 else 0 := by
  change (b >>> i) &&& 1 = _
  rw [Nat.land_comm, Nat.one_and_eq_mod_two, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with h | h <;> simp [h]

public theorem bitVal_eq_one_iff {b i : Nat} : bitVal b i = 1 ↔ b.testBit i := by
  rw [bitVal_eq_testBit]; cases b.testBit i <;> simp

/-- `initK M = 2^(M+1) - 2` has bits `1 … M` set and bit `0` clear. -/
theorem testBit_initK (M t : Nat) :
    (initK M).testBit t = decide (1 ≤ t ∧ t ≤ M) := by
  have h : initK M = (2 ^ M - 1) <<< 1 := by
    change (1 <<< (M + 1)) - 2 = (2 ^ M - 1) <<< 1
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, pow_one, Nat.pow_succ]
    have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
    omega
  rw [h, Nat.testBit_shiftLeft]
  rcases t with _ | t
  · simp
  · simp only [Nat.succ_sub_one, Nat.testBit_two_pow_sub_one, ge_iff_le, Nat.le_add_left,
      decide_true, Bool.true_and, true_and, Nat.lt_iff_add_one_le]

/-! ## Layer 2: `buildMaskK` sets two stride-`2p` progressions

`dbl` generalizes `buildMaskK`'s hard-coded 32 doublings to a variable `n` so the doubling can be
inducted on; it is defeq to `buildMaskK` at `n = 32`. -/

/-- Disjoint OR equals ADD, for `Nat`; hence subtracting a submask acts as bitwise `ldiff`. -/
theorem and_add_ldiff (a b : Nat) : (a &&& b) + Nat.ldiff a b = a := by
  induction a using Nat.binaryRec generalizing b with
  | zero =>
    have : Nat.ldiff 0 b = 0 := Nat.eq_of_testBit_eq (fun k => by simp [Nat.testBit_ldiff])
    simp [this]
  | bit ba a' ih =>
    induction b using Nat.binaryRec with
    | zero =>
      have : Nat.ldiff (bit ba a') 0 = bit ba a' :=
        Nat.eq_of_testBit_eq (fun k => by simp [Nat.testBit_ldiff])
      simp [this]
    | bit bb b' _ =>
      rw [Nat.land_bit, Nat.ldiff_bit, Nat.bit_val, Nat.bit_val, Nat.bit_val]
      have h := ih b'
      cases ba <;> cases bb <;> simp [Bool.toNat] at h ⊢ <;> omega

theorem sub_and_eq_ldiff (a b : Nat) : a - (a &&& b) = Nat.ldiff a b := by
  have := and_add_ldiff a b; omega

/-- `buildMaskK` with the doubling count generalized from the literal 32 to a variable `n`. -/
def dbl (p M A B n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    ((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B))
    (fun i Mk =>
      ((p.shiftLeft i.succ).ble M).rec Mk
        (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
    n

theorem buildMaskK_eq (p M A B : Nat) : buildMaskK p M A B = dbl p M A B 32 := rfl

theorem dbl_zero (p M A B : Nat) : dbl p M A B 0 = (1 <<< A) ||| (1 <<< B) := rfl

theorem dbl_succ_raw (p M A B n : Nat) :
    dbl p M A B (n + 1)
      = Bool.rec (dbl p M A B n)
          (Nat.lor (dbl p M A B n)
            (Nat.shiftLeft (dbl p M A B n) (Nat.shiftLeft p (Nat.succ n))))
          (Nat.ble (Nat.shiftLeft p (Nat.succ n)) M) := rfl

theorem dbl_succ (p M A B n : Nat) :
    dbl p M A B (n + 1)
      = if 2 * p * 2 ^ n ≤ M
        then dbl p M A B n ||| (dbl p M A B n) <<< (2 * p * 2 ^ n)
        else dbl p M A B n := by
  have hs : Nat.shiftLeft p (Nat.succ n) = 2 * p * 2 ^ n :=
    (Nat.shiftLeft_eq p (n + 1)).trans (by ring)
  rw [dbl_succ_raw, hs]
  cases h : Nat.ble (2 * p * 2 ^ n) M with
  | true =>
      rw [if_pos (Nat.le_of_ble_eq_true h)]
      rfl
  | false =>
      have hlt : ¬ 2 * p * 2 ^ n ≤ M := by
        intro hle; rw [Nat.ble_eq_true_of_le hle] at h; exact Bool.noConfusion h
      rw [if_neg hlt]

/-- Splitting a stride-`s` progression of length `2q` into the low half (`j < q`) and the shifted
high half (`q ≤ j < 2q`, reachable only when `s*q ≤ t`). -/
theorem prog_succ (c t s q : Nat) :
    (∃ j < 2 * q, t = c + s * j) ↔
      (∃ j < q, t = c + s * j) ∨ (s * q ≤ t ∧ ∃ j < q, t - s * q = c + s * j) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases lt_or_ge j q with h | h
    · exact Or.inl ⟨j, h, rfl⟩
    · have hsplit : s * j = s * q + s * (j - q) := by
        rw [← Nat.mul_add]; congr 1; omega
      exact Or.inr ⟨by omega, j - q, by omega, by omega⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨hle, j, hj, he⟩)
    · exact ⟨j, by omega, rfl⟩
    · refine ⟨q + j, by omega, ?_⟩
      have : s * (q + j) = s * q + s * j := by rw [Nat.mul_add]
      omega

theorem testBit_one_shiftLeft (s t : Nat) : (1 <<< s).testBit t = decide (s = t) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

/-- `dbl` after `n` doublings sets exactly the bits of the two stride-`2p` progressions
`A + 2p·j` and `B + 2p·j` with `j < 2^n`. -/
theorem testBit_dbl (p M A B : Nat) :
    ∀ n t, t ≤ M →
      ((dbl p M A B n).testBit t ↔
        (∃ j < 2 ^ n, t = A + 2 * p * j) ∨ (∃ j < 2 ^ n, t = B + 2 * p * j)) := by
  intro n
  induction n with
  | zero =>
    intro t _
    rw [dbl_zero, Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft]
    simp only [pow_zero, Nat.lt_one_iff, exists_eq_left, Nat.mul_zero, Nat.add_zero,
      Bool.or_eq_true, decide_eq_true_eq]
    omega
  | succ n ih =>
    intro t ht
    rw [dbl_succ]
    have h2 : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    by_cases hg : 2 * p * 2 ^ n ≤ M
    · rw [if_pos hg, Nat.testBit_or, Nat.testBit_shiftLeft]
      simp only [ge_iff_le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih t ht, ih (t - 2 * p * 2 ^ n) (le_trans (Nat.sub_le _ _) ht), h2, prog_succ,
        prog_succ]
      constructor
      · rintro ((hP | hQ) | ⟨hR, hS | hU⟩)
        · exact Or.inl (Or.inl hP)
        · exact Or.inr (Or.inl hQ)
        · exact Or.inl (Or.inr ⟨hR, hS⟩)
        · exact Or.inr (Or.inr ⟨hR, hU⟩)
      · rintro ((hP | ⟨hR, hS⟩) | (hQ | ⟨hR, hU⟩))
        · exact Or.inl (Or.inl hP)
        · exact Or.inr ⟨hR, Or.inl hS⟩
        · exact Or.inl (Or.inr hQ)
        · exact Or.inr ⟨hR, Or.inr hU⟩
    · rw [if_neg hg, ih t ht]
      have hng : ¬ 2 * p * 2 ^ n ≤ t := by omega
      rw [h2, prog_succ, prog_succ]
      constructor
      · rintro (hP | hQ)
        · exact Or.inl (Or.inl hP)
        · exact Or.inr (Or.inl hQ)
      · rintro ((hP | ⟨hR, _⟩) | (hQ | ⟨hR, _⟩))
        · exact Or.inl hP
        · exact absurd hR hng
        · exact Or.inr hQ
        · exact absurd hR hng

/-- On the relevant range, membership in a stride-`2p` progression is divisibility. The count bound
`B` is non-binding because any witness `j` satisfies `2p·j ≤ t < 2p·B`. -/
theorem prog_iff_dvd (c t p B : Nat) (hB : t < 2 * p * B) :
    (∃ j < B, t = c + 2 * p * j) ↔ (c ≤ t ∧ 2 * p ∣ (t - c)) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Nat.le_add_right _ _, ⟨j, by omega⟩⟩
  · rintro ⟨hc, k, hk⟩
    refine ⟨k, ?_, by omega⟩
    have hlt : 2 * p * k < 2 * p * B := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt

/-- `buildMaskK p M A B` has bit `t` (for `t ≤ M < 2^32`) set iff `t` lies in one of the two
stride-`2p` progressions from `A`, `B`. -/
theorem testBit_buildMaskK (p M A B t : Nat) (hp : 0 < p) (hM : M < 2 ^ 32) (ht : t ≤ M) :
    (buildMaskK p M A B).testBit t ↔
      (A ≤ t ∧ 2 * p ∣ (t - A)) ∨ (B ≤ t ∧ 2 * p ∣ (t - B)) := by
  have hB : t < 2 * p * 2 ^ 32 := by
    have h1 : (2 : Nat) ^ 32 ≤ 2 * p * 2 ^ 32 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [buildMaskK_eq, testBit_dbl p M A B 32 t ht, prog_iff_dvd A t p (2 ^ 32) hB,
    prog_iff_dvd B t p (2 ^ 32) hB]

/-! ## Layer 3a: `markMaskK` clears exactly the mask bits -/

/-- `markMaskK bits p M` is bitwise `ldiff` of `bits` against `buildMaskK` (subtracting a
submask). -/
theorem markMaskK_eq_ldiff (bits p M : Nat) :
    markMaskK bits p M
      = Nat.ldiff bits (buildMaskK p M ((5 * p - 1) / 3) ((7 * p - 1) / 3)) := by
  unfold markMaskK
  rw [Nat.mul_comm 5 p, Nat.mul_comm 7 p]
  exact sub_and_eq_ldiff _ _

/-- `markMaskK` clears exactly the bits set in `buildMaskK`, keeping the rest of `bits`. -/
theorem testBit_markMaskK (bits p M t : Nat) :
    (markMaskK bits p M).testBit t
      = (bits.testBit t && ! (buildMaskK p M ((5 * p - 1) / 3) ((7 * p - 1) / 3)).testBit t) := by
  rw [markMaskK_eq_ldiff, Nat.testBit_ldiff]

/-! ## Layer 3b: the cleared bits are the coprime-to-6 multiples of `p`

`num` (the number at an index) grows by `6m` when the index grows by `2m` (parity preserved), and
the seeds `(5p−1)/3`, `(7p−1)/3` decode to `5p`, `7p` (for `p` coprime to 6). Hence the two `2p`
progressions are exactly the coprime-to-6 multiples `p·k` with `k ≥ 5`. -/

/-- Adding an even amount `2m` to the index adds `6m` to the number. -/
theorem num_add_two_mul (k m : Nat) : num (k + 2 * m) = num k + 6 * m := by
  unfold num; omega

theorem num_seedA (p : Nat) (hp : p % 6 = 1 ∨ p % 6 = 5) : num ((5 * p - 1) / 3) = 5 * p := by
  unfold num; rcases hp with h | h <;> omega

theorem num_seedB (p : Nat) (hp : p % 6 = 1 ∨ p % 6 = 5) : num ((7 * p - 1) / 3) = 7 * p := by
  unfold num; rcases hp with h | h <;> omega

/-- The `A` progression carries `num` to `p·(5 + 6j)` (numbers `≡ 5 mod 6`). -/
theorem numA (p t : Nat) (hp : p % 6 = 1 ∨ p % 6 = 5) (j : Nat)
    (h : t = (5 * p - 1) / 3 + 2 * (p * j)) : num t = p * (5 + 6 * j) := by
  subst h; rw [num_add_two_mul, num_seedA p hp]; ring

/-- The `B` progression carries `num` to `p·(7 + 6j)` (numbers `≡ 1 mod 6`). -/
theorem numB (p t : Nat) (hp : p % 6 = 1 ∨ p % 6 = 5) (j : Nat)
    (h : t = (7 * p - 1) / 3 + 2 * (p * j)) : num t = p * (7 + 6 * j) := by
  subst h; rw [num_add_two_mul, num_seedB p hp]; ring

/-- `num` is injective (strictly monotone), so the encoding can be inverted. -/
theorem num_inj {a b : Nat} (h : num a = num b) : a = b := by
  unfold num at h; omega

/-- The mask `markMaskK` uses (bits set in `buildMaskK` with seeds `(5p−1)/3`, `(7p−1)/3`) marks
index `t` iff `num t` is a coprime-to-6 multiple `p·k` with `k ≥ 5`: exactly the composite
multiples starting at `5p`. -/
theorem mask_iff (p M t : Nat) (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hp : 0 < p)
    (hM : M < 2 ^ 32) (ht : t ≤ M) :
    (buildMaskK p M ((5 * p - 1) / 3) ((7 * p - 1) / 3)).testBit t ↔
      ∃ k, 5 ≤ k ∧ (k % 6 = 1 ∨ k % 6 = 5) ∧ num t = p * k := by
  rw [testBit_buildMaskK p M _ _ t hp hM ht]
  constructor
  · rintro (⟨hle, c, hc⟩ | ⟨hle, c, hc⟩)
    · refine ⟨5 + 6 * c, by omega, Or.inr (by omega), ?_⟩
      apply numA p t hp6 c
      have : 2 * p * c = 2 * (p * c) := by ring
      omega
    · refine ⟨7 + 6 * c, by omega, Or.inl (by omega), ?_⟩
      apply numB p t hp6 c
      have : 2 * p * c = 2 * (p * c) := by ring
      omega
  · rintro ⟨k, hk5, hk6, hnum⟩
    rcases hk6 with h1 | h5
    · right
      obtain ⟨j, rfl⟩ : ∃ j, k = 7 + 6 * j := ⟨(k - 7) / 6, by omega⟩
      have ht2 : num t = num ((7 * p - 1) / 3 + 2 * (p * j)) := by
        rw [numB p _ hp6 j rfl, hnum]
      have hteq : t = (7 * p - 1) / 3 + 2 * (p * j) := num_inj ht2
      refine ⟨by omega, j, ?_⟩
      have : 2 * p * j = 2 * (p * j) := by ring
      omega
    · left
      obtain ⟨j, rfl⟩ : ∃ j, k = 5 + 6 * j := ⟨(k - 5) / 6, by omega⟩
      have ht2 : num t = num ((5 * p - 1) / 3 + 2 * (p * j)) := by
        rw [numA p _ hp6 j rfl, hnum]
      have hteq : t = (5 * p - 1) / 3 + 2 * (p * j) := num_inj ht2
      refine ⟨by omega, j, ?_⟩
      have : 2 * p * j = 2 * (p * j) := by ring
      omega

/-! ## Layer 4: the surviving bits are exactly the primes (sieve of Eratosthenes)

`markMaskK` only clears composite bits, so a prime bit is never cleared (completeness). For
soundness, a composite `num t` has a smallest prime factor `q ≤ √(num t) ≤ sqrtN`; it is processed,
own bit is still set (primes are preserved), so its `markMaskK` fires and clears `t`. -/

theorem num_mod6 (k : Nat) : num k % 6 = 1 ∨ num k % 6 = 5 := by unfold num; omega

theorem five_le_num (k : Nat) (hk : 1 ≤ k) : 5 ≤ num k := by unfold num; omega

/-- The loop's "is bit `j` set" test (`1 ≤ b &&& 2^j`) is `b.testBit j`. -/
theorem ble_one_and_eq (b j : Nat) :
    Nat.ble 1 (b &&& (1 <<< j)) = b.testBit j := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow]
  cases h : b.testBit j
  · simp only [Bool.toNat_false, Nat.zero_mul]; rfl
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact Nat.ble_eq_true_of_le Nat.one_le_two_pow

theorem sieveLoopK_succ_if (M bits start fuel : Nat) :
    sieveLoopK M bits start (fuel + 1)
      = if (sieveLoopK M bits start fuel).testBit (start + fuel)
        then markMaskK (sieveLoopK M bits start fuel) (num (start + fuel)) M
        else sieveLoopK M bits start fuel := by
  rw [sieveLoopK_succ, numK_eq_num, ble_one_and_eq]
  cases h : (sieveLoopK M bits start fuel).testBit (start + fuel) with
  | true => rw [if_pos rfl]
  | false => rw [if_neg (by simp)]

/-- `markMaskK` (sieving by a wheel candidate `p ≥ 5`) never clears a bit whose number is prime: the
mask only marks composite `num t = p·k` with `p, k ≥ 5`. -/
theorem markMaskK_preserves_prime (b p M t : Nat) (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hp5 : 5 ≤ p)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hprime : (num t).Prime) :
    (markMaskK b p M).testBit t = b.testBit t := by
  rw [testBit_markMaskK]
  suffices h : (buildMaskK p M ((5 * p - 1) / 3) ((7 * p - 1) / 3)).testBit t = false by
    rw [h]; simp
  by_contra hc
  rw [Bool.not_eq_false, mask_iff p M t hp6 (by omega) hM ht] at hc
  obtain ⟨k, hk5, _, hnum⟩ := hc
  rcases hprime.eq_one_or_self_of_dvd p ⟨k, hnum⟩ with h1 | hself
  · omega
  · have hpk : p * 1 = p * k := by rw [Nat.mul_one]; omega
    have : (1 : Nat) = k := Nat.eq_of_mul_eq_mul_left (by omega) hpk
    omega

/-- The loop preserves any prime bit: it stays at its initial value. -/
theorem sieveLoopK_preserves (M bits start fuel t : Nat) (hstart : 1 ≤ start)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hprime : (num t).Prime) :
    (sieveLoopK M bits start fuel).testBit t = bits.testBit t := by
  induction fuel with
  | zero => rfl
  | succ f ih =>
    rw [sieveLoopK_succ_if]
    split
    · rw [markMaskK_preserves_prime _ (num (start + f)) _ _ (num_mod6 _)
        (five_le_num _ (by omega)) hM ht hprime, ih]
    · exact ih

/-- Completeness: every prime bit in range survives the sieve. -/
theorem sieve_prime_set (n sqrtN t : Nat) (ht1 : 1 ≤ t) (htM : t ≤ (n - 1) / 3)
    (hM : (n - 1) / 3 < 2 ^ 32) (hprime : (num t).Prime) :
    (sieveK n sqrtN).testBit t = true := by
  unfold sieveK
  change (sieveLoopK ((n - 1) / 3) (initK ((n - 1) / 3)) 1 ((sqrtN - 1) / 3)).testBit t = true
  rw [sieveLoopK_preserves _ _ 1 _ t (le_refl 1) hM htM hprime, testBit_initK]
  simp [ht1, htM]

/-- Soundness mechanism: if a prime index `j` in the processed range witnesses `num t = num j · m`
(`m ≥ 5` coprime to 6), the sieve clears bit `t`. When `j` is processed its bit is still set
(primes are preserved), so its `markMaskK` fires; earlier clears are kept because `markMaskK` only
clears. -/
theorem sieveLoopK_clears (M start t j m : Nat) (hstart : 1 ≤ start)
    (hM : M < 2 ^ 32) (ht : t ≤ M) (hjprime : (num j).Prime) (hjt : j ≤ t)
    (hm5 : 5 ≤ m) (hm6 : m % 6 = 1 ∨ m % 6 = 5) (hnum : num t = num j * m) (hj_lo : start ≤ j) :
    ∀ fuel, j < start + fuel → (sieveLoopK M (initK M) start fuel).testBit t = false := by
  intro fuel
  induction fuel with
  | zero => intro h; omega
  | succ f ih =>
    intro hj_hi
    rw [sieveLoopK_succ_if]
    rcases Nat.lt_or_ge j (start + f) with hlt | hge
    · have hprev := ih hlt
      split
      · rw [testBit_markMaskK, hprev]; simp
      · exact hprev
    · have hje : j = start + f := by omega
      have hset : (sieveLoopK M (initK M) start f).testBit (start + f) = true := by
        rw [sieveLoopK_preserves M (initK M) start f (start + f) hstart hM (by omega)
          (hje ▸ hjprime), testBit_initK]
        simp only [decide_eq_true_eq]; omega
      rw [if_pos hset, testBit_markMaskK]
      have hmask : (buildMaskK (num (start + f)) M ((5 * num (start + f) - 1) / 3)
          ((7 * num (start + f) - 1) / 3)).testBit t = true := by
        rw [mask_iff (num (start + f)) M t (num_mod6 _)
          (by have := five_le_num (start + f) (by omega); omega) hM ht]
        exact ⟨m, hm5, hm6, by rw [← hje]; exact hnum⟩
      rw [hmask]; simp

/-! ### Soundness number theory -/

theorem num_le (a b : Nat) (h : a ≤ b) : num a ≤ num b := by unfold num; omega

theorem num_wheel (q : Nat) (hq : q % 6 = 1 ∨ q % 6 = 5) : num ((q - 1) / 3) = q := by
  unfold num; rcases hq with h | h <;> omega

theorem num_coprime6 (t : Nat) : Nat.Coprime (num t) 6 := by
  have h := num_mod6 t
  change Nat.gcd (num t) 6 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases h with h | h <;> rw [h] <;> decide

theorem coprime6_mod (m : Nat) (h : Nat.Coprime m 6) : m % 6 = 1 ∨ m % 6 = 5 := by
  have hg : Nat.gcd (m % 6) 6 = 1 := by rw [← Nat.gcd_rec, Nat.gcd_comm]; exact h
  have hlt : m % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases (m % 6) <;> revert hg <;> decide

theorem prime_ge5_mod6 (q : Nat) (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  have h2 : q % 2 = 1 := Nat.odd_iff.mp (hq.eq_two_or_odd'.resolve_left (by omega))
  have h3 : q % 3 ≠ 0 := by
    intro hh
    rcases hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hh) with h' | h' <;> omega
  omega

/-- **Correctness**: for `1 ≤ t ≤ (n−1)/3` with `num t ≤ n ≤ sqrtN²`, bit `t` of the sieve is set
iff `num t` is prime. -/
public theorem sieveK_testBit_iff (n sqrtN t : Nat) (ht1 : 1 ≤ t) (htM : t ≤ (n - 1) / 3)
    (hM : (n - 1) / 3 < 2 ^ 32) (hbound : num t ≤ n) (hsqrt : n ≤ sqrtN * sqrtN) :
    (sieveK n sqrtN).testBit t ↔ (num t).Prime := by
  refine ⟨fun hset => ?_, sieve_prime_set n sqrtN t ht1 htM hM⟩
  by_contra hnp
  have h5 : 5 ≤ num t := five_le_num t ht1
  have hnt2 : num t % 2 = 1 := by have := num_mod6 t; omega
  have hnt3 : num t % 3 ≠ 0 := by have := num_mod6 t; omega
  obtain ⟨q, hqprime, hqdvd, hqsq⟩ : ∃ q, q.Prime ∧ q ∣ num t ∧ q ^ 2 ≤ num t :=
    ⟨(num t).minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd _,
      Nat.minFac_sq_le_self (by omega) hnp⟩
  have hq2le : 2 ≤ q := hqprime.two_le
  have hq2 : q ≠ 2 := by rintro rfl; obtain ⟨c, hc⟩ := hqdvd; omega
  have hq3 : q ≠ 3 := by rintro rfl; obtain ⟨c, hc⟩ := hqdvd; omega
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hqprime.eq_two_or_odd'.resolve_left hq2)
  have hq5 : 5 ≤ q := by omega
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := prime_ge5_mod6 q hqprime hq5
  obtain ⟨m, hm⟩ := hqdvd
  have hqm : q ≤ m := Nat.le_of_mul_le_mul_left (by rw [← pow_two]; omega) (by omega)
  have hm5 : 5 ≤ m := by omega
  have hmdvd : m ∣ num t := ⟨q, by rw [hm]; ring⟩
  have hm6 : m % 6 = 1 ∨ m % 6 = 5 := coprime6_mod m ((num_coprime6 t).coprime_dvd_left hmdvd)
  have hnumjq : num ((q - 1) / 3) = q := num_wheel q hq6
  have hjq1 : 1 ≤ (q - 1) / 3 := by omega
  have hnum2 : num t = num ((q - 1) / 3) * m := by rw [hnumjq]; exact hm
  have hqlt : q < num t := by nlinarith
  have hjqt : (q - 1) / 3 ≤ t := by
    by_contra hc
    rw [not_le] at hc
    have := num_le t ((q - 1) / 3) (le_of_lt hc)
    rw [hnumjq] at this; omega
  have hqsqrt : q ≤ sqrtN := by nlinarith
  have hjqfuel : (q - 1) / 3 < 1 + (sqrtN - 1) / 3 := by
    have hnj := hnumjq; unfold num at hnj; omega
  have hcleared := sieveLoopK_clears ((n - 1) / 3) 1 t ((q - 1) / 3) m (le_refl 1) hM htM
    (by rw [hnumjq]; exact hqprime) hjqt hm5 hm6 hnum2 hjq1 ((sqrtN - 1) / 3) hjqfuel
  unfold sieveK at hset
  change (sieveLoopK ((n - 1) / 3) (initK ((n - 1) / 3)) 1 ((sqrtN - 1) / 3)).testBit t = true
    at hset
  rw [hcleared] at hset
  exact Bool.noConfusion hset

/-! ### Reading a prime off a cached sieve -/

/-- From the numeric side-conditions (each as `Nat.ble … = true`), "bit `t` of the sieve literal
`lit` is set", and `numK t = p`, conclude `p` is prime. The kernel reads the bit from `lit`, and
`hEq : sieveK n sqrtN = lit`, the equation `run_sieve` proves, carries it back to the sieve. -/
public theorem prime_of_sieve_eq (n sqrtN t lit p : Nat) (hEq : sieveK n sqrtN = lit)
    (h1 : Nat.ble 1 t)
    (h2 : t.ble ((n.sub 1).div 3))
    (h3 : (((n.sub 1).div 3).add 1).ble (Nat.pow 2 32))
    (h4 : (numK t).ble n)
    (h5 : n.ble (sqrtN.mul sqrtN))
    (hbit : (bitVal lit t).beq 1)
    (hp : (numK t).beq p) :
    Nat.Prime p := by
  rw [← Nat.eq_of_beq_eq_true hp, numK_eq_num]
  refine (sieveK_testBit_iff n sqrtN t (Nat.le_of_ble_eq_true h1) (Nat.le_of_ble_eq_true h2)
    (Nat.le_of_ble_eq_true h3) (Nat.le_of_ble_eq_true h4) (Nat.le_of_ble_eq_true h5)).mp ?_
  rw [← bitVal_eq_one_iff, hEq]
  exact Nat.eq_of_beq_eq_true hbit

end PrimeCert.Sieve
