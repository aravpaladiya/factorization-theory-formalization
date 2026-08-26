/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.Elasticity
public import Mathlib.RingTheory.Factorization.Transfer.Basic

/-!
# Elasticity and transfer homomorphisms

This file proves that transfer homomorphisms preserve maximal and minimal factorization lengths,
elementwise elasticity, and the elasticity of the whole monoid.

## Main results

* `IsTransferHom.maxFactorizationLength_eq` and
  `IsTransferHom.minFactorizationLength_eq`: the length extrema are preserved.
* `IsTransferHom.elasticity_eq`: elementwise elasticity is preserved.
* `IsTransferHom.monoid_elasticity_eq`: monoid elasticity is preserved.
-/

public section

assert_not_exists Ideal

variable {α β F : Type*}

section CommMonoidWithZero

variable [CommMonoidWithZero α] [CommMonoidWithZero β]
variable [FunLike F α β] [MonoidWithZeroHomClass F α β]
variable {θ : F}

namespace IsTransferHom

theorem maxFactorizationLength_eq (hθ : IsTransferHom θ) (a : α) :
    maxFactorizationLength (θ a) = maxFactorizationLength a := by
  rw [maxFactorizationLength_def, maxFactorizationLength_def, hθ.factorizationLengths_eq]

theorem minFactorizationLength_eq (hθ : IsTransferHom θ) (a : α) :
    minFactorizationLength (θ a) = minFactorizationLength a := by
  rw [minFactorizationLength_def, minFactorizationLength_def, hθ.factorizationLengths_eq]

/-- A transfer homomorphism preserves the elasticity of every element. -/
theorem elasticity_eq (hθ : IsTransferHom θ) (a : α) : elasticity (θ a) = elasticity a := by
  by_cases ha : IsUnit a
  · simp [ha, hθ.isUnit_map_iff.mpr ha]
  · simp [elasticity_def, ha, hθ.isUnit_map_iff.not.mpr ha,
      hθ.maxFactorizationLength_eq, hθ.minFactorizationLength_eq]

/-- A transfer homomorphism preserves the elasticity of the whole monoid. -/
theorem monoid_elasticity_eq (hθ : IsTransferHom θ) :
    Monoid.elasticity α = Monoid.elasticity β := by
  apply le_antisymm
  · rw [Monoid.elasticity_def]
    refine sup_le Monoid.one_le_elasticity <| iSup_le fun a ↦
      iSup_le fun ha ↦ iSup_le fun _ ↦ ?_
    rw [← hθ.elasticity_eq a]
    exact Monoid.le_elasticity (hθ.map_ne_zero ha)
  · rw [Monoid.elasticity_def]
    refine sup_le Monoid.one_le_elasticity <| iSup_le fun b ↦
      iSup_le fun hb ↦ iSup_le fun _ ↦ ?_
    obtain ⟨a, hab⟩ := hθ.exists_associated_map b
    have ha : a ≠ 0 := hθ.map_eq_zero_iff.not.mp (hab.ne_zero_iff.mpr hb)
    calc
      elasticity b = elasticity (θ a) := hab.elasticity_eq.symm
      _ = elasticity a := hθ.elasticity_eq a
      _ ≤ Monoid.elasticity α := Monoid.le_elasticity ha

end IsTransferHom

end CommMonoidWithZero
