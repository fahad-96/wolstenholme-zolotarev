/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Wolstenholme.Basic

/-!
# Power sums of residues modulo a prime

For a prime `p` and `0 < m < p - 1` we show that `∑_{0 < k < p} k ^ m` and
`∑_{0 < k < p} k⁻¹ ^ m` vanish in `ZMod p`. The case `m = 2` gives the congruence
`∑ 1 / (k (p - k)) ≡ 0 (mod p)` for `p ≥ 5`, which drives both the harmonic and the
binomial parts of Wolstenholme's theorem.

## Main results

* `Wolstenholme.sum_Ioo_eq_sum_zmod`: a sum over `0 < k < p` is a sum over `ZMod p`
  when the summand vanishes at `0`.
* `Wolstenholme.sum_Ioo_pow_eq_zero` and `Wolstenholme.sum_Ioo_inv_pow_eq_zero`.
* `Wolstenholme.sum_Ioo_inv_mul_inv_sub_eq_zero`: `∑_{0 < k < p} 1 / (k (p - k)) = 0` in `ZMod p`.
-/

public section

namespace Wolstenholme

open Finset

variable {p : ℕ}

/-- A sum over the naturals `0 < k < p` equals the sum over all of `ZMod p`,
provided the summand vanishes at `0`. -/
theorem sum_Ioo_eq_sum_zmod [NeZero p] {M : Type*} [AddCommMonoid M] (f : ZMod p → M)
    (hf : f 0 = 0) :
    ∑ k ∈ Ioo 0 p, f k = ∑ x : ZMod p, f x := by
  rw [← sum_erase univ hf]
  refine sum_nbij' (fun k ↦ (k : ZMod p)) ZMod.val ?_ ?_ ?_ ?_ fun _ _ ↦ rfl
  · intro k hk
    rw [mem_Ioo] at hk
    simpa [ZMod.natCast_eq_zero_iff] using Nat.not_dvd_of_pos_of_lt hk.1 hk.2
  · intro x hx
    rw [mem_erase] at hx
    exact mem_Ioo.2 ⟨(ZMod.val_pos).2 hx.1, ZMod.val_lt x⟩
  · intro k hk
    exact ZMod.val_cast_of_lt (mem_Ioo.1 hk).2
  · intro x _
    exact ZMod.natCast_zmod_val x

variable [Fact p.Prime]

/-- For `0 < m < p - 1`, the power sum `∑_{0 < k < p} k ^ m` vanishes in `ZMod p`. -/
theorem sum_Ioo_pow_eq_zero {m : ℕ} (hm0 : m ≠ 0) (hmp : m < p - 1) :
    ∑ k ∈ Ioo 0 p, (k : ZMod p) ^ m = 0 := by
  rw [sum_Ioo_eq_sum_zmod (· ^ m) (zero_pow hm0)]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) m (by rwa [ZMod.card])

/-- For `0 < m < p - 1`, the inverse power sum `∑_{0 < k < p} k⁻¹ ^ m` vanishes in `ZMod p`. -/
theorem sum_Ioo_inv_pow_eq_zero {m : ℕ} (hm0 : m ≠ 0) (hmp : m < p - 1) :
    ∑ k ∈ Ioo 0 p, (k : ZMod p)⁻¹ ^ m = 0 := by
  rw [sum_Ioo_eq_sum_zmod (·⁻¹ ^ m) (by simp [zero_pow hm0]),
    Fintype.sum_bijective _ inv_involutive.bijective (·⁻¹ ^ m) (· ^ m) fun _ ↦ rfl]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) m (by rwa [ZMod.card])

/-- For `p ≥ 5`, the sum `∑_{0 < k < p} 1 / (k (p - k))` vanishes in `ZMod p`. -/
theorem sum_Ioo_inv_mul_inv_sub_eq_zero (h5 : 5 ≤ p) :
    ∑ k ∈ Ioo 0 p, (k : ZMod p)⁻¹ * ((p - k : ℕ) : ZMod p)⁻¹ = 0 := by
  have key : ∀ k ∈ Ioo 0 p,
      (k : ZMod p)⁻¹ * ((p - k : ℕ) : ZMod p)⁻¹ = -((k : ZMod p)⁻¹ ^ 2) := by
    intro k hk
    rw [Nat.cast_sub (mem_Ioo.1 hk).2.le, ZMod.natCast_self, zero_sub, inv_neg, mul_neg, sq]
  rw [sum_congr rfl key, sum_neg_distrib, sum_Ioo_inv_pow_eq_zero two_ne_zero (by omega),
    neg_zero]

end Wolstenholme
