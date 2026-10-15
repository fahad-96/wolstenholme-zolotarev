/-
Copyright (c) 2026 Fahad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fahad
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The sign of multiplication by a unit of `ZMod p`

For a prime `p` and a unit `u` of `ZMod p`, the map `x ↦ u * x` is a permutation of `ZMod p`.
Taking its sign gives a group homomorphism `Zolotarev.mulSign p : (ZMod p)ˣ →* ℤˣ`.

We compute this homomorphism. It sends squares to `1`. For an odd prime, a generator `g` of
the cyclic group `(ZMod p)ˣ` acts as one cycle of length `p - 1` on the nonzero residues.
So its sign is `-(-1) ^ (p - 1) = -1`. Every non-square is an odd power of `g`, so it is sent
to `-1` as well.

## Main results

* `Zolotarev.mulSign_apply`: `mulSign p u` is the sign of `Equiv.mulLeft₀ u`.
* `Zolotarev.mulSign_of_isSquare`: squares have sign `1`.
* `Zolotarev.isCycle_toPerm_of_forall_mem_zpowers`: a generator acts as a single cycle.
* `Zolotarev.support_toPerm_of_ne_one`: a unit `g ≠ 1` moves exactly the nonzero residues.
* `Zolotarev.mulSign_of_not_isSquare`: non-squares have sign `-1`.
-/

public section

namespace Zolotarev

open Equiv

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The sign of the permutation `x ↦ u * x` of `ZMod p`, as a homomorphism on units. -/
@[expose] def mulSign : (ZMod p)ˣ →* ℤˣ :=
  Perm.sign.comp (MulAction.toPermHom (ZMod p)ˣ (ZMod p))

/-- `mulSign p u` is the sign of left multiplication by `u` on `ZMod p`. -/
theorem mulSign_apply (u : (ZMod p)ˣ) :
    mulSign p u = Perm.sign (Equiv.mulLeft₀ (u : ZMod p) u.ne_zero) := by
  rw [mulSign, MonoidHom.comp_apply]
  congr 1
  ext x
  simp [Units.smul_def]

/-- A square unit has sign `1`. -/
theorem mulSign_of_isSquare {u : (ZMod p)ˣ} (hu : IsSquare (u : ZMod p)) : mulSign p u = 1 := by
  obtain ⟨r, hr⟩ := hu
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hu' : u = Units.mk0 r hr0 * Units.mk0 r hr0 := Units.ext (by simpa using hr)
  rw [hu', map_mul, Int.units_mul_self]

/-- For an odd prime `p`, a generator of `(ZMod p)ˣ` is not `1`. -/
theorem ne_one_of_forall_mem_zpowers (hp2 : p ≠ 2) {g : (ZMod p)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : g ≠ 1 := by
  rintro rfl
  have : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)⟩
  have h := hg (-1)
  rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h
  exact ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)

/-- For an odd prime `p`, multiplication by a generator of `(ZMod p)ˣ` is a cycle. -/
theorem isCycle_toPerm_of_forall_mem_zpowers (hp2 : p ≠ 2) {g : (ZMod p)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (MulAction.toPerm g : Perm (ZMod p)).IsCycle := by
  have hg1 := ne_one_of_forall_mem_zpowers hp2 hg
  refine ⟨1, ?_, fun y hy ↦ ?_⟩
  · rw [MulAction.toPerm_apply, Units.smul_def, smul_eq_mul, mul_one]
    exact fun h ↦ hg1 (Units.ext h)
  · have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 y hy0))
    refine ⟨k, ?_⟩
    rw [← MulAction.toPermHom_apply, ← map_zpow, MulAction.toPermHom_apply, hk,
      MulAction.toPerm_apply, Units.smul_def, smul_eq_mul, mul_one, Units.val_mk0]

/-- Multiplication by a unit `g ≠ 1` fixes `0` and moves every nonzero residue. -/
theorem support_toPerm_of_ne_one {g : (ZMod p)ˣ} (hg : g ≠ 1) :
    (MulAction.toPerm g : Perm (ZMod p)).support = Finset.univ.erase 0 := by
  have hg1 : (g : ZMod p) ≠ 1 := fun h ↦ hg (Units.ext h)
  ext x
  rw [Perm.mem_support, Finset.mem_erase, MulAction.toPerm_apply, Units.smul_def, smul_eq_mul]
  refine ⟨fun h ↦ ⟨fun hx ↦ h (by rw [hx, mul_zero]), Finset.mem_univ x⟩, fun h ↦ ?_⟩
  rw [Ne, mul_eq_right₀ h.1]
  exact hg1

/-- For an odd prime `p`, a generator of `(ZMod p)ˣ` has sign `-1`. -/
theorem mulSign_of_forall_mem_zpowers (hp2 : p ≠ 2) {g : (ZMod p)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : mulSign p g = -1 := by
  have hp := (Fact.out : p.Prime)
  have heven : Even (p - 1) := Nat.Odd.sub_odd (hp.odd_of_ne_two hp2) odd_one
  rw [mulSign, MonoidHom.comp_apply, MulAction.toPermHom_apply,
    (isCycle_toPerm_of_forall_mem_zpowers hp2 hg).sign,
    support_toPerm_of_ne_one (ne_one_of_forall_mem_zpowers hp2 hg),
    Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card, heven.neg_one_pow]

/-- A unit that is not a square has sign `-1`. -/
theorem mulSign_of_not_isSquare {u : (ZMod p)ˣ} (hu : ¬IsSquare (u : ZMod p)) :
    mulSign p u = -1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : ∀ x : ZMod 2, x = x * x := by
      intro x
      fin_cases x <;> rfl
    exact hu ⟨u, h2 u⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg u)
  rw [map_zpow, mulSign_of_forall_mem_zpowers hp2 hg]
  obtain ⟨m, rfl⟩ | hk := k.even_or_odd
  · exact absurd ⟨((g ^ m : (ZMod p)ˣ) : ZMod p), by rw [zpow_add, Units.val_mul]⟩ hu
  · exact hk.neg_one_zpow

end Zolotarev
