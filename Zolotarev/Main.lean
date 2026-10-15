/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Zolotarev.SignHom

/-!
# Zolotarev's lemma

For a prime `p` and an integer `a` not divisible by `p`, the Legendre symbol `(a / p)` is the
sign of the permutation `x ↦ a * x` of `ZMod p`.

## Main results

* `Zolotarev.zolotarevs_lemma`: `sign (x ↦ a * x) = legendreSym p a`.
* `Zolotarev.sign_mulLeft₀_eq_quadraticChar`: the same statement for `a : ZMod p`.
* `Zolotarev.sign_neg_eq_χ₄`: for an odd prime `p`, the sign of `x ↦ -x` on `ZMod p`
  is `χ₄ p`, that is `(-1) ^ ((p - 1) / 2)`.
-/

public section

namespace Zolotarev

open Equiv

variable {p : ℕ} [Fact p.Prime]

/-- Zolotarev's lemma for `a : ZMod p`, stated with the quadratic character. -/
theorem sign_mulLeft₀_eq_quadraticChar {a : ZMod p} (ha : a ≠ 0) :
    (Perm.sign (Equiv.mulLeft₀ a ha) : ℤ) = quadraticChar (ZMod p) a := by
  have h : mulSign p (Units.mk0 a ha) = Perm.sign (Equiv.mulLeft₀ a ha) :=
    mulSign_apply (Units.mk0 a ha)
  rw [← h]
  by_cases hsq : IsSquare a
  · rw [mulSign_of_isSquare (by simpa using hsq), (quadraticChar_one_iff_isSquare ha).2 hsq,
      Units.val_one]
  · rw [mulSign_of_not_isSquare (by simpa using hsq), quadraticChar_neg_one_iff_not_isSquare.2 hsq,
      Units.val_neg, Units.val_one]

/-- **Zolotarev's lemma**: for a prime `p` and an integer `a` with `p ∤ a`, the sign of the
permutation `x ↦ a * x` of `ZMod p` is the Legendre symbol `(a / p)`. -/
theorem zolotarevs_lemma {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    (Perm.sign (Equiv.mulLeft₀ (a : ZMod p) ha) : ℤ) = legendreSym p a :=
  sign_mulLeft₀_eq_quadraticChar ha

/-- For an odd prime `p`, the sign of negation on `ZMod p` is `χ₄ p`. -/
theorem sign_neg_eq_χ₄ (hp2 : p ≠ 2) : (Perm.sign (Equiv.neg (ZMod p)) : ℤ) = ZMod.χ₄ p := by
  have h1 : ((-1 : ℤ) : ZMod p) ≠ 0 := by simp
  have hneg : Equiv.neg (ZMod p) = Equiv.mulLeft₀ ((-1 : ℤ) : ZMod p) h1 := by
    ext x
    simp
  rw [hneg, zolotarevs_lemma, legendreSym.at_neg_one hp2]

end Zolotarev
