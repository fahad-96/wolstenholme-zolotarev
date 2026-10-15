import Wolstenholme
import Zolotarev

/-!
# Axiom checks

Each headline theorem is restated below with its full statement, so that this file fails to
compile if a statement in the library drifts away from what the README claims. After each
restatement, `#print axioms` lists the axioms the proof depends on. Every line of output should
list only axioms from `propext`, `Classical.choice` and `Quot.sound`.

Run it with `lake env lean Checks.lean`.
-/

open Finset

section Wolstenholme

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] :=
  Wolstenholme.wolstenholmes_theorem hp h5
#print axioms Wolstenholme.wolstenholmes_theorem

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : (2 * p).choose p ≡ 2 [MOD p ^ 3] :=
  Wolstenholme.choose_two_mul_modEq_two hp h5
#print axioms Wolstenholme.choose_two_mul_modEq_two

example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2] :=
  Wolstenholme.babbages_theorem hp hp2
#print axioms Wolstenholme.babbages_theorem

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : (p : ℤ) ^ 2 ∣ (harmonic (p - 1)).num :=
  Wolstenholme.sq_dvd_harmonic_num hp h5
#print axioms Wolstenholme.sq_dvd_harmonic_num

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : 2 ≤ padicValRat p (harmonic (p - 1)) :=
  Wolstenholme.two_le_padicValRat_harmonic hp h5
#print axioms Wolstenholme.two_le_padicValRat_harmonic

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ∣ (∑ k ∈ Ioo 0 p, ((k : ℚ) ^ 2)⁻¹).num :=
  Wolstenholme.dvd_sum_inv_sq_num hp h5
#print axioms Wolstenholme.dvd_sum_inv_sq_num

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 :=
  Wolstenholme.natCast_choose_eq_one_zmod_cube hp h5
#print axioms Wolstenholme.natCast_choose_eq_one_zmod_cube

example {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ = 0 :=
  Wolstenholme.sum_Ioo_inv_eq_zero hp h5
#print axioms Wolstenholme.sum_Ioo_inv_eq_zero

example : ¬(2 * 3 - 1).choose (3 - 1) ≡ 1 [MOD 3 ^ 3] :=
  Wolstenholme.not_choose_modEq_one_three
#print axioms Wolstenholme.not_choose_modEq_one_three

example : ¬(3 : ℤ) ^ 2 ∣ (harmonic (3 - 1)).num :=
  Wolstenholme.not_sq_dvd_harmonic_num_three
#print axioms Wolstenholme.not_sq_dvd_harmonic_num_three

example : ¬(2 * 2 - 1).choose (2 - 1) ≡ 1 [MOD 2 ^ 2] :=
  Wolstenholme.not_choose_modEq_one_two
#print axioms Wolstenholme.not_choose_modEq_one_two

end Wolstenholme

section Zolotarev

example {p : ℕ} [Fact p.Prime] (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    (Equiv.Perm.sign (Equiv.mulLeft₀ (a : ZMod p) ha) : ℤ) = legendreSym p a :=
  Zolotarev.zolotarevs_lemma ha
#print axioms Zolotarev.zolotarevs_lemma

example {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    (Equiv.Perm.sign (Equiv.mulLeft₀ a ha) : ℤ) = quadraticChar (ZMod p) a :=
  Zolotarev.sign_mulLeft₀_eq_quadraticChar ha
#print axioms Zolotarev.sign_mulLeft₀_eq_quadraticChar

example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (Equiv.Perm.sign (Equiv.neg (ZMod p)) : ℤ) = ZMod.χ₄ p :=
  Zolotarev.sign_neg_eq_χ₄ hp2
#print axioms Zolotarev.sign_neg_eq_χ₄

end Zolotarev
