/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Wolstenholme.Harmonic

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# The binomial coefficient `(2p - 1).choose (p - 1)` modulo `p ^ 2` and `p ^ 3`

In `ZMod (p ^ n)` we write
`(2p - 1).choose (p - 1) = ∏_{0 < k < p} (p + k) / k = ∏_{0 < k < p} (1 + p * k⁻¹)`.

* Modulo `p ^ 2` the product is `1 + p * ∑ k⁻¹`, and pairing `k` with `p - k` shows that
  `p * ∑ k⁻¹` vanishes for every odd prime. This is Babbage's theorem.
* Modulo `p ^ 3`, call the product `P`. Pairing the factors for `k` and `p - k` gives
  `P ^ 2 = 1 + p ^ 2 * ∑ 2 / (k (p - k))`. The sum is a multiple of `p` when `p ≥ 5`,
  so `P ^ 2 = 1`. Since `P = 1 + p * b` and `p` is odd, this forces `P = 1`.

## Main results

* `Wolstenholme.choose_mul_factorial_eq_prod`: `C(2p - 1, p - 1) * (p - 1)! = ∏ (p + k)`.
* `Wolstenholme.natCast_choose_eq_prod_one_add`: the product formula in `ZMod (p ^ n)`.
* `Wolstenholme.natCast_choose_eq_one_zmod_sq`: Babbage's theorem in `ZMod (p ^ 2)`.
* `Wolstenholme.natCast_choose_eq_one_zmod_cube`: Wolstenholme's theorem in `ZMod (p ^ 3)`.
-/

public section

namespace Wolstenholme

open Finset
open scoped Nat

variable {p : ℕ}

section CommSemiring

variable {R ι : Type*} [CommSemiring R]

/-- A product of factors `1 + c * f i` has the form `1 + c * b`. -/
theorem exists_prod_one_add_mul (s : Finset ι) (c : R) (f : ι → R) :
    ∃ b, ∏ i ∈ s, (1 + c * f i) = 1 + c * b := by
  refine prod_induction _ (fun x ↦ ∃ b, x = 1 + c * b) ?_ ⟨0, by simp⟩ fun i _ ↦ ⟨f i, rfl⟩
  rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
  exact ⟨b + b' + c * b * b', by ring⟩

/-- If `c ^ 2 = 0`, then `∏ (1 + c * f i) = 1 + c * ∑ f i`. -/
theorem prod_one_add_mul_of_sq_eq_zero (s : Finset ι) {c : R} (hc : c ^ 2 = 0) (f : ι → R) :
    ∏ i ∈ s, (1 + c * f i) = 1 + c * ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, sum_cons, ih]
    calc (1 + c * f a) * (1 + c * ∑ i ∈ s, f i)
        = 1 + c * (f a + ∑ i ∈ s, f i) + c ^ 2 * (f a * ∑ i ∈ s, f i) := by ring
      _ = 1 + c * (f a + ∑ i ∈ s, f i) := by rw [hc, zero_mul, add_zero]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- In a ring where `2` is a unit, an element `y` with `y ^ 3 = 0` and `(1 + y) ^ 2 = 1`
is zero. -/
theorem eq_zero_of_one_add_sq_eq_one (h2 : IsUnit (2 : R)) {y : R} (hy : y ^ 3 = 0)
    (h : (1 + y) ^ 2 = 1) : y = 0 := by
  have hy2 : y ^ 2 = 0 := h2.mul_right_eq_zero.1 (by linear_combination y * h - hy)
  exact h2.mul_right_eq_zero.1 (by linear_combination h - hy2)

end CommRing

/-- The binomial coefficient as a product: `C(2p - 1, p - 1) * (p - 1)! = ∏_{0 < k < p} (p + k)`.
-/
theorem choose_mul_factorial_eq_prod (p : ℕ) :
    (2 * p - 1).choose (p - 1) * (p - 1)! = ∏ k ∈ Ioo 0 p, (p + k) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  rw [show 2 * p - 1 = p + (p - 1) by omega, mul_comm, ← Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.ascFactorial_eq_prod_range]
  refine prod_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_ <;>
    intro i hi <;> simp only [mem_range, mem_Ioo] at hi ⊢ <;> omega

/-- In `ZMod (p ^ n)`, `C(2p - 1, p - 1) = ∏_{0 < k < p} (1 + p * k⁻¹)`. -/
theorem natCast_choose_eq_prod_one_add (hp : p.Prime) (n : ℕ) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) =
      ∏ k ∈ Ioo 0 p, (1 + p * (k : ZMod (p ^ n))⁻¹) := by
  have hfac : ∏ k ∈ Ioo 0 p, (k : ZMod (p ^ n)) = ((p - 1)! : ℕ) := by
    rw [← prod_Ico_id_eq_factorial, Nat.cast_prod]
    refine prod_congr ?_ fun _ _ ↦ rfl
    ext k
    simp only [mem_Ioo, mem_Ico]
    omega
  have hunit : IsUnit ((p - 1)! : ZMod (p ^ n)) :=
    (ZMod.unitOfCoprime _ ((coprime_factorial_sub_one hp).symm.pow_right n)).isUnit
  have hprod : ∏ k ∈ Ioo 0 p, ((p : ZMod (p ^ n)) + k) =
      ((p - 1)! : ZMod (p ^ n)) * ∏ k ∈ Ioo 0 p, (1 + p * (k : ZMod (p ^ n))⁻¹) := by
    rw [← hfac, ← prod_mul_distrib]
    refine prod_congr rfl fun k hk ↦ ?_
    rw [mem_Ioo] at hk
    linear_combination (-(p : ZMod (p ^ n))) * natCast_mul_inv_cancel hp hk.1 hk.2 n
  have h := congrArg (Nat.cast : ℕ → ZMod (p ^ n)) (choose_mul_factorial_eq_prod p)
  push_cast at h
  rw [hprod, mul_comm] at h
  exact hunit.mul_left_cancel h

/-- **Babbage's theorem** in `ZMod (p ^ 2)`: for an odd prime `p`,
`C(2p - 1, p - 1) = 1`. -/
theorem natCast_choose_eq_one_zmod_sq (hp : p.Prime) (hp2 : p ≠ 2) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 2)) = 1 := by
  have hodd : Odd (p ^ 2) := (hp.odd_of_ne_two hp2).pow
  have hc : (p : ZMod (p ^ 2)) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have h := two_mul_sum_Ioo_inv hp 2
  have key : (p : ZMod (p ^ 2)) * ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ +
      (p : ZMod (p ^ 2)) * ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ = 0 := by
    linear_combination (p : ZMod (p ^ 2)) * h +
      (∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) * hc
  rw [natCast_choose_eq_prod_one_add hp 2, prod_one_add_mul_of_sq_eq_zero _ hc,
    (ZMod.add_self_eq_zero_iff_eq_zero hodd).1 key, add_zero]

/-- **Wolstenholme's theorem** in `ZMod (p ^ 3)`: for a prime `p ≥ 5`,
`C(2p - 1, p - 1) = 1`. -/
theorem natCast_choose_eq_one_zmod_cube (hp : p.Prime) (h5 : 5 ≤ p) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := by
  have h2 : IsUnit (2 : ZMod (p ^ 3)) := by
    simpa using (ZMod.isUnit_iff_coprime 2 (p ^ 3)).2
      (Nat.coprime_two_left.2 (hp.odd_of_ne_two (by omega)).pow)
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hp4 : ((p : ZMod (p ^ 3)) ^ 2) ^ 2 = 0 := by
    rw [← pow_mul]
    exact pow_eq_zero_of_le (by norm_num) hp3
  have hW : (p : ZMod (p ^ 3)) ^ 2 *
      ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ = 0 :=
    pow_mul_sum_Ioo_inv_mul_inv_sub_eq_zero hp h5 2
  have hrefl : ∏ k ∈ Ioo 0 p, (1 + p * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) =
      ∏ k ∈ Ioo 0 p, (1 + p * (k : ZMod (p ^ 3))⁻¹) :=
    prod_Ioo_reflect p fun k ↦ 1 + p * (k : ZMod (p ^ 3))⁻¹
  -- Pairing the factors for `k` and `p - k` shows that the product squares to `1`.
  have hsq : (∏ k ∈ Ioo 0 p, (1 + p * (k : ZMod (p ^ 3))⁻¹)) ^ 2 = 1 := by
    have hpair : ∀ k ∈ Ioo 0 p,
        (1 + p * (k : ZMod (p ^ 3))⁻¹) * (1 + p * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) =
          1 + (p : ZMod (p ^ 3)) ^ 2 *
            (2 * ((k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹)) := by
      intro k hk
      rw [mem_Ioo] at hk
      linear_combination (p : ZMod (p ^ 3)) * inv_add_inv_sub hp hk.1 hk.2 3
    rw [sq]
    nth_rw 2 [← hrefl]
    rw [← prod_mul_distrib, prod_congr rfl hpair, prod_one_add_mul_of_sq_eq_zero _ hp4,
      ← mul_sum, mul_left_comm, hW, mul_zero, add_zero]
  -- The product is `1 + p * b`, and `p` is odd, so it equals `1`.
  obtain ⟨b, hb⟩ : ∃ b, ∏ k ∈ Ioo 0 p, (1 + (p : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) =
      1 + p * b :=
    exists_prod_one_add_mul _ _ _
  rw [hb] at hsq
  rw [natCast_choose_eq_prod_one_add hp 3, hb,
    eq_zero_of_one_add_sq_eq_one h2 (by rw [mul_pow, hp3, zero_mul]) hsq, add_zero]

end Wolstenholme
