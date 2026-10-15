/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Wolstenholme.PowerSums

import Mathlib.Tactic.LinearCombination

/-!
# The harmonic sum `1 + 1/2 + ... + 1/(p - 1)` modulo `p ^ 2`

We pair `k` with `p - k` to show that, for a prime `p ≥ 5`,
`∑_{0 < k < p} k⁻¹ = 0` in `ZMod (p ^ 2)`. We also prove the transfer lemmas that
`Wolstenholme.Main` uses to move this congruence to the numerator of `harmonic (p - 1)`.

## Main results

* `Wolstenholme.two_mul_sum_Ioo_inv`: `2 * ∑ k⁻¹ = p * ∑ k⁻¹ (p - k)⁻¹` in `ZMod (p ^ n)`.
* `Wolstenholme.pow_mul_sum_Ioo_inv_mul_inv_sub_eq_zero`: the sum `∑ k⁻¹ (p - k)⁻¹` is a
  multiple of `p`, in the form `p ^ n * ∑ k⁻¹ (p - k)⁻¹ = 0` in `ZMod (p ^ (n + 1))`.
* `Wolstenholme.sum_Ioo_inv_eq_zero`: `∑_{0 < k < p} k⁻¹ = 0` in `ZMod (p ^ 2)` for `p ≥ 5`.
* `Wolstenholme.natCast_sum_factorial_div_pow`: clearing the denominators of `∑ 1 / k ^ m`.
* `Wolstenholme.dvd_sum_inv_pow_num`: if `M` is coprime to `(p - 1)!` and `∑ k⁻¹ ^ m`
  vanishes in `ZMod M`, then `M` divides the numerator of the rational number `∑ 1 / k ^ m`.
* `Wolstenholme.harmonic_den_dvd_factorial`: the denominator of `harmonic n` divides `n !`.
-/

public section

namespace Wolstenholme

open Finset
open scoped Nat

variable {p : ℕ}

/-- Pairing `k` with `p - k`: twice the inverse sum is `p` times `∑ k⁻¹ (p - k)⁻¹`. -/
theorem two_mul_sum_Ioo_inv (hp : p.Prime) (n : ℕ) :
    2 * ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ n))⁻¹ =
      p * ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ n))⁻¹ * ((p - k : ℕ) : ZMod (p ^ n))⁻¹ := by
  have h : ∑ k ∈ Ioo 0 p, ((p - k : ℕ) : ZMod (p ^ n))⁻¹ = ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ n))⁻¹ :=
    sum_Ioo_reflect p fun k ↦ (k : ZMod (p ^ n))⁻¹
  rw [two_mul]
  nth_rw 2 [← h]
  rw [← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_Ioo] at hk
  exact inv_add_inv_sub hp hk.1 hk.2 n

/-- For `p ≥ 5`, the sum `∑ k⁻¹ (p - k)⁻¹` in `ZMod (p ^ (n + 1))` is a multiple of `p`,
so multiplying it by `p ^ n` gives zero. -/
theorem pow_mul_sum_Ioo_inv_mul_inv_sub_eq_zero (hp : p.Prime) (h5 : 5 ≤ p) (n : ℕ) :
    (p : ZMod (p ^ (n + 1))) ^ n *
      ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ (n + 1)))⁻¹ * ((p - k : ℕ) : ZMod (p ^ (n + 1)))⁻¹ =
        0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine pow_mul_eq_zero_of_castHom_eq_zero ?_
  rw [map_sum]
  refine (sum_congr rfl fun k hk ↦ ?_).trans (sum_Ioo_inv_mul_inv_sub_eq_zero h5)
  rw [mem_Ioo] at hk
  rw [map_mul, castHom_inv_natCast hp hk.2, castHom_inv_natCast hp (Nat.sub_lt hp.pos hk.1)]

/-- **Wolstenholme's harmonic congruence**: for a prime `p ≥ 5`,
`1 + 1/2 + ... + 1/(p - 1) = 0` in `ZMod (p ^ 2)`. -/
theorem sum_Ioo_inv_eq_zero (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ = 0 := by
  have hodd : Odd (p ^ 2) := (hp.odd_of_ne_two (by omega)).pow
  have hW : (p : ZMod (p ^ 2)) ^ 1 *
      ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ = 0 :=
    pow_mul_sum_Ioo_inv_mul_inv_sub_eq_zero hp h5 1
  have h := two_mul_sum_Ioo_inv hp 2
  rw [pow_one] at hW
  rw [hW, two_mul] at h
  exact (ZMod.add_self_eq_zero_iff_eq_zero hodd).1 h

/-- The harmonic number `harmonic (p - 1)` as a sum over `0 < k < p`. -/
theorem harmonic_sub_one_eq_sum_Ioo (p : ℕ) :
    harmonic (p - 1) = ∑ k ∈ Ioo 0 p, (k : ℚ)⁻¹ := by
  rw [harmonic, range_eq_Ico, sum_Ico_add' (fun i : ℕ ↦ (i : ℚ)⁻¹) 0 (p - 1) 1]
  refine sum_congr ?_ fun _ _ ↦ rfl
  ext k
  simp only [mem_Ico, mem_Ioo]
  omega

/-- Clearing denominators: `(p - 1)! ^ m * ∑_{0 < k < p} 1 / k ^ m` is the natural number
`∑_{0 < k < p} ((p - 1)! / k) ^ m`. -/
theorem natCast_sum_factorial_div_pow (p m : ℕ) :
    ((∑ k ∈ Ioo 0 p, ((p - 1)! / k) ^ m : ℕ) : ℚ) =
      ((p - 1)! ^ m : ℕ) * ∑ k ∈ Ioo 0 p, ((k : ℚ) ^ m)⁻¹ := by
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_Ioo] at hk
  rw [Nat.cast_div (Nat.dvd_factorial hk.1 (by omega)) (by exact_mod_cast hk.1.ne'), div_pow,
    div_eq_mul_inv]

/-- The natural number `∑_{0 < k < p} ((p - 1)! / k) ^ m` in `ZMod M`, for `M` coprime
to `(p - 1)!`. -/
theorem natCast_sum_factorial_div_pow_zmod {M : ℕ} (hM : M.Coprime (p - 1)!) (m : ℕ) :
    ((∑ k ∈ Ioo 0 p, ((p - 1)! / k) ^ m : ℕ) : ZMod M) =
      ((p - 1)! : ZMod M) ^ m * ∑ k ∈ Ioo 0 p, (k : ZMod M)⁻¹ ^ m := by
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_Ioo] at hk
  have hdvd : k ∣ (p - 1)! := Nat.dvd_factorial hk.1 (by omega)
  have h1 : (((p - 1)! / k : ℕ) : ZMod M) * k = (p - 1)! := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have h2 : (k : ZMod M) * (k : ZMod M)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one k (Nat.Coprime.coprime_dvd_left hdvd hM.symm)
  rw [← mul_pow]
  congr 1
  linear_combination (k : ZMod M)⁻¹ * h1 - (((p - 1)! / k : ℕ) : ZMod M) * h2

/-- Transfer to rational numbers. Let `M` be coprime to `(p - 1)!`. If the inverse power
sum `∑_{0 < k < p} k⁻¹ ^ m` vanishes in `ZMod M`, then `M` divides the numerator of the
rational number `∑_{0 < k < p} 1 / k ^ m`. -/
theorem dvd_sum_inv_pow_num {M m : ℕ} (hM : M.Coprime (p - 1)!)
    (h : ∑ k ∈ Ioo 0 p, (k : ZMod M)⁻¹ ^ m = 0) :
    (M : ℤ) ∣ (∑ k ∈ Ioo 0 p, ((k : ℚ) ^ m)⁻¹).num := by
  refine dvd_num_of_intCast_eq_mul (hM.pow_right m)
    (N := (∑ k ∈ Ioo 0 p, ((p - 1)! / k) ^ m : ℕ)) ?_ ?_
  · exact_mod_cast natCast_sum_factorial_div_pow p m
  · rw [Int.natCast_dvd_natCast, ← ZMod.natCast_eq_zero_iff,
      natCast_sum_factorial_div_pow_zmod hM, h, mul_zero]

/-- The denominator of `harmonic n` divides `n !`. -/
theorem harmonic_den_dvd_factorial (n : ℕ) : (harmonic n).den ∣ n ! := by
  have h := natCast_sum_factorial_div_pow (n + 1) 1
  have hH : harmonic n = ∑ k ∈ Ioo 0 (n + 1), (k : ℚ)⁻¹ := by
    simpa using harmonic_sub_one_eq_sum_Ioo (n + 1)
  simp only [pow_one, Nat.add_sub_cancel] at h
  rw [← hH] at h
  exact den_dvd_of_intCast_eq_mul (N := (∑ k ∈ Ioo 0 (n + 1), n ! / k : ℕ)) (by exact_mod_cast h)

end Wolstenholme
