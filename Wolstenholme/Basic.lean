/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Inverses of small naturals modulo prime powers

Let `p` be a prime and `0 < k < p`. Then `k` is a unit in `ZMod (p ^ n)` for every `n`.
This file collects the facts about these inverses that the rest of the project uses.

## Main results

* `Wolstenholme.natCast_mul_inv_cancel`: `k * k⁻¹ = 1` in `ZMod (p ^ n)`.
* `Wolstenholme.inv_add_inv_sub`: `k⁻¹ + (p - k)⁻¹ = p * (k⁻¹ * (p - k)⁻¹)`.
* `Wolstenholme.castHom_inv_natCast`: reducing `k⁻¹` modulo `p` gives `k⁻¹` in `ZMod p`.
* `Wolstenholme.pow_mul_eq_zero_of_castHom_eq_zero`: if `x` vanishes modulo `p`, then
  `p ^ n * x = 0` in `ZMod (p ^ (n + 1))`.
* `Wolstenholme.prod_Ioo_reflect`: reindexing a product over `0 < k < p` by `k ↦ p - k`.
* `Wolstenholme.dvd_num_of_intCast_eq_mul`: moving a divisibility from an integer `D * q`
  to the numerator of the rational number `q`.
* `Wolstenholme.den_dvd_of_intCast_eq_mul`: if `D * q` is an integer, then the denominator
  of `q` divides `D`.
-/

public section

namespace Wolstenholme

open Finset

variable {p : ℕ}

/-- Reindexing a product over `0 < k < p` by the involution `k ↦ p - k`. -/
@[to_additive /-- Reindexing a sum over `0 < k < p` by the involution `k ↦ p - k`. -/]
theorem prod_Ioo_reflect {M : Type*} [CommMonoid M] (p : ℕ) (f : ℕ → M) :
    ∏ k ∈ Ioo 0 p, f (p - k) = ∏ k ∈ Ioo 0 p, f k := by
  refine prod_nbij' (p - ·) (p - ·) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl <;>
    intro k hk <;> simp only [mem_Ioo] at hk ⊢ <;> omega

/-- A natural number `k` with `0 < k < p` is coprime to every power of the prime `p`. -/
theorem coprime_pow_of_pos_of_lt (hp : p.Prime) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) (n : ℕ) :
    k.Coprime (p ^ n) :=
  (Nat.coprime_of_lt_prime hk0.ne' hkp hp).symm.pow_right n

/-- The prime `p` is coprime to `(p - 1)!`. -/
theorem coprime_factorial_sub_one (hp : p.Prime) : p.Coprime (p - 1).factorial :=
  hp.coprime_factorial_of_lt (Nat.sub_lt hp.pos one_pos)

/-- For `0 < k < p`, the residue of `k` is invertible in `ZMod (p ^ n)`. -/
theorem natCast_mul_inv_cancel (hp : p.Prime) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) (n : ℕ) :
    (k : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one k (coprime_pow_of_pos_of_lt hp hk0 hkp n)

/-- The pairing identity `1 / k + 1 / (p - k) = p / (k (p - k))` in `ZMod (p ^ n)`. -/
theorem inv_add_inv_sub (hp : p.Prime) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) (n : ℕ) :
    (k : ZMod (p ^ n))⁻¹ + ((p - k : ℕ) : ZMod (p ^ n))⁻¹ =
      p * ((k : ZMod (p ^ n))⁻¹ * ((p - k : ℕ) : ZMod (p ^ n))⁻¹) := by
  have ha := natCast_mul_inv_cancel hp hk0 hkp n
  have hb := natCast_mul_inv_cancel hp (Nat.sub_pos_of_lt hkp) (Nat.sub_lt hp.pos hk0) n
  have hab : (k : ZMod (p ^ n)) + ((p - k : ℕ) : ZMod (p ^ n)) = p := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hkp.le]
  linear_combination (-((p - k : ℕ) : ZMod (p ^ n))⁻¹) * ha + (-(k : ZMod (p ^ n))⁻¹) * hb +
    ((k : ZMod (p ^ n))⁻¹ * ((p - k : ℕ) : ZMod (p ^ n))⁻¹) * hab

/-- Reducing the inverse of `k` modulo `p` gives the inverse of `k` in `ZMod p`. -/
theorem castHom_inv_natCast (hp : p.Prime) {k : ℕ} (hkp : k < p) {n : ℕ} (h : p ∣ p ^ n) :
    ZMod.castHom h (ZMod p) ((k : ZMod (p ^ n))⁻¹) = (k : ZMod p)⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [ZMod.inv_zero]
  have h1 := congrArg (ZMod.castHom h (ZMod p)) (natCast_mul_inv_cancel hp hk0 hkp n)
  rw [map_mul, map_natCast, map_one] at h1
  have h2 : (k : ZMod p) * (k : ZMod p)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one k (Nat.coprime_of_lt_prime hk0.ne' hkp hp).symm
  linear_combination (k : ZMod p)⁻¹ * h1 - ZMod.castHom h (ZMod p) (k : ZMod (p ^ n))⁻¹ * h2

/-- If `x` reduces to `0` modulo `p`, then `p ^ n * x = 0` in `ZMod (p ^ (n + 1))`. -/
theorem pow_mul_eq_zero_of_castHom_eq_zero {n : ℕ} {x : ZMod (p ^ (n + 1))}
    (hx : ZMod.castHom (dvd_pow_self p n.add_one_ne_zero) (ZMod p) x = 0) :
    (p : ZMod (p ^ (n + 1))) ^ n * x = 0 := by
  obtain ⟨y, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
  obtain ⟨c, rfl⟩ := hx
  push_cast
  rw [← mul_assoc, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- Let `q` be a rational number and `N = D * q` an integer, where `D` is coprime to `M`.
If `M` divides `N`, then `M` divides the numerator of `q`. -/
theorem dvd_num_of_intCast_eq_mul {q : ℚ} {M D : ℕ} {N : ℤ} (hMD : M.Coprime D)
    (hN : (N : ℚ) = D * q) (hM : (M : ℤ) ∣ N) : (M : ℤ) ∣ q.num := by
  have key : N * q.den = D * q.num := by
    have h : (N : ℚ) * q.den = D * q.num := by rw [hN, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast h
  have hcop : IsCoprime (M : ℤ) D := Nat.isCoprime_iff_coprime.2 hMD
  exact hcop.dvd_of_dvd_mul_left (key ▸ dvd_mul_of_dvd_left hM _)

/-- Let `q` be a rational number such that `N = D * q` is an integer. Then the denominator
of `q` divides `D`. -/
theorem den_dvd_of_intCast_eq_mul {q : ℚ} {D : ℕ} {N : ℤ} (hN : (N : ℚ) = D * q) :
    q.den ∣ D := by
  have key : N * q.den = D * q.num := by
    have h : (N : ℚ) * q.den = D * q.num := by rw [hN, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast h
  have hcop : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  exact Int.natCast_dvd_natCast.1 <|
    hcop.dvd_of_dvd_mul_right (key ▸ dvd_mul_left _ _)

end Wolstenholme
