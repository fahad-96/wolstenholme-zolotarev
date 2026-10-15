/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Wolstenholme.Binomial

import Mathlib.NumberTheory.Harmonic.Int

/-!
# Wolstenholme's theorem

This file states the headline results of the project.

For a prime `p ≥ 5`:

* `Wolstenholme.wolstenholmes_theorem`: `C(2p - 1, p - 1) ≡ 1 [MOD p ^ 3]`.
* `Wolstenholme.choose_two_mul_modEq_two`: `C(2p, p) ≡ 2 [MOD p ^ 3]`.
* `Wolstenholme.sq_dvd_harmonic_num`: `p ^ 2` divides the numerator of
  `harmonic (p - 1) = 1 + 1/2 + ... + 1/(p - 1)`.
* `Wolstenholme.two_le_padicValRat_harmonic`: the same fact as `2 ≤ v_p (harmonic (p - 1))`.
* `Wolstenholme.dvd_sum_inv_sq_num`: `p` divides the numerator of `∑_{0 < k < p} 1 / k ^ 2`.

For an odd prime `p`:

* `Wolstenholme.babbages_theorem`: `C(2p - 1, p - 1) ≡ 1 [MOD p ^ 2]`.

The bounds on `p` are sharp. `Wolstenholme.not_choose_modEq_one_three` and
`Wolstenholme.not_sq_dvd_harmonic_num_three` show that `p = 3` fails the binomial and the
harmonic congruences, and `Wolstenholme.not_choose_modEq_one_two` shows that `p = 2` fails
Babbage's congruence.
-/

public section

namespace Wolstenholme

open Finset

variable {p : ℕ}

/-- **Wolstenholme's theorem**: for a prime `p ≥ 5`, `C(2p - 1, p - 1) ≡ 1 [MOD p ^ 3]`. -/
theorem wolstenholmes_theorem (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact natCast_choose_eq_one_zmod_cube hp h5

/-- For a prime `p ≥ 5`, the central binomial coefficient satisfies
`C(2p, p) ≡ 2 [MOD p ^ 3]`. -/
theorem choose_two_mul_modEq_two (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p).choose p ≡ 2 [MOD p ^ 3] := by
  have key : (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by
    have h := Nat.add_one_mul_choose_eq (2 * p - 1) (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p), Nat.sub_add_cancel hp.one_le] at h
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [← h]
    ring
  rw [key]
  simpa using (wolstenholmes_theorem hp h5).mul_left 2

/-- **Babbage's theorem**: for an odd prime `p`, `C(2p - 1, p - 1) ≡ 1 [MOD p ^ 2]`. -/
theorem babbages_theorem (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact natCast_choose_eq_one_zmod_sq hp hp2

/-- **Wolstenholme's harmonic theorem**: for a prime `p ≥ 5`, `p ^ 2` divides the numerator
of `harmonic (p - 1) = 1 + 1/2 + ... + 1/(p - 1)`. -/
theorem sq_dvd_harmonic_num (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ (harmonic (p - 1)).num := by
  have h := dvd_sum_inv_pow_num (m := 1) ((coprime_factorial_sub_one hp).pow_left 2)
    (by simpa using sum_Ioo_inv_eq_zero hp h5)
  rw [harmonic_sub_one_eq_sum_Ioo]
  simpa using h

/-- The `p`-adic valuation of `harmonic (p - 1)` is at least `2` for a prime `p ≥ 5`. -/
theorem two_le_padicValRat_harmonic (hp : p.Prime) (h5 : 5 ≤ p) :
    2 ≤ padicValRat p (harmonic (p - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hnum : (harmonic (p - 1)).num ≠ 0 := Rat.num_ne_zero.2 (harmonic_pos (by omega)).ne'
  have hden : ¬p ∣ (harmonic (p - 1)).den := fun h ↦
    hp.coprime_iff_not_dvd.1 (coprime_factorial_sub_one hp)
      (h.trans (harmonic_den_dvd_factorial (p - 1)))
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden, Nat.cast_zero, sub_zero]
  exact_mod_cast ((padicValInt_dvd_iff 2 _).1 (sq_dvd_harmonic_num hp h5)).resolve_left hnum

/-- For a prime `p ≥ 5`, `p` divides the numerator of `∑_{0 < k < p} 1 / k ^ 2`. -/
theorem dvd_sum_inv_sq_num (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ∣ (∑ k ∈ Ioo 0 p, ((k : ℚ) ^ 2)⁻¹).num := by
  have : Fact p.Prime := ⟨hp⟩
  exact dvd_sum_inv_pow_num (coprime_factorial_sub_one hp)
    (sum_Ioo_inv_pow_eq_zero two_ne_zero (by omega))

/-- Wolstenholme's congruence fails for `p = 3`: `C(5, 2) = 10` is not `1` modulo `27`. -/
theorem not_choose_modEq_one_three : ¬(2 * 3 - 1).choose (3 - 1) ≡ 1 [MOD 3 ^ 3] := by
  decide

/-- The harmonic statement fails for `p = 3`: `harmonic 2 = 3 / 2`. -/
theorem not_sq_dvd_harmonic_num_three : ¬(3 : ℤ) ^ 2 ∣ (harmonic (3 - 1)).num := by
  have h : harmonic (3 - 1) = 3 / 2 := by
    rw [show 3 - 1 = 0 + 1 + 1 by norm_num, harmonic_succ, harmonic_succ, harmonic_zero]
    norm_num
  have hnum : (3 / 2 : ℚ).num = 3 := by
    simpa using Rat.num_div_eq_of_coprime (a := 3) (b := 2) (by norm_num) (by decide)
  rw [h, hnum]
  decide

/-- Babbage's congruence fails for `p = 2`: `C(3, 1) = 3` is not `1` modulo `4`. -/
theorem not_choose_modEq_one_two : ¬(2 * 2 - 1).choose (2 - 1) ≡ 1 [MOD 2 ^ 2] := by
  decide

end Wolstenholme
