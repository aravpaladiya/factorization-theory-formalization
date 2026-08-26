/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.Monoid
public import Mathlib.RingTheory.Factorization.Transfer.Basic

import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.Factorization.UniqueFactorizationMonoid

/-!
# Factorization properties and transfer homomorphisms

This file transports the standard factorization-monoid properties along transfer homomorphisms.
Atomicity, bounded factorization, and half-factoriality hold in the source if and only if they hold
in the target. Finite and unique factorization transfer only from the source to the target in this
generality, because a transfer homomorphism may identify distinct source factorizations.

## Main results

* `IsTransferHom.atomicMonoid_iff`: atomicity is preserved in both directions.
* `IsTransferHom.boundedFactorizationMonoid_iff`: bounded factorization is preserved in both
  directions.
* `IsTransferHom.halfFactorialMonoid_iff`: half-factoriality is preserved in both directions.
* `IsTransferHom.finiteFactorizationMonoid_of_source`: finite factorization transfers to the
  target.
* `IsTransferHom.uniqueFactorizationMonoid_of_source`: unique factorization transfers to a
  cancellative target.
-/

public section

assert_not_exists Field Ideal

variable {α β F : Type*}

section CommMonoidWithZero

variable [CommMonoidWithZero α] [CommMonoidWithZero β]
variable [FunLike F α β] [MonoidWithZeroHomClass F α β]
variable {θ : F}

namespace IsTransferHom

/-- If the target of a transfer homomorphism is atomic, so is its source. -/
theorem atomicMonoid (hθ : IsTransferHom θ) [AtomicMonoid β] : AtomicMonoid α := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨q, hq⟩ := AtomicMonoid.nonempty_factorizations (hθ.map_ne_zero ha)
  obtain ⟨p, hp, -⟩ := hθ.exists_factorizationMap_eq hq
  exact ⟨p, hp⟩

/-- If the source of a transfer homomorphism is atomic, so is its target. -/
theorem atomicMonoid_of_source (hθ : IsTransferHom θ) [AtomicMonoid α] : AtomicMonoid β := by
  refine ⟨fun b hb ↦ ?_⟩
  obtain ⟨a, hab⟩ := hθ.exists_associated_map b
  have ha : a ≠ 0 := hθ.map_eq_zero_iff.not.mp (hab.ne_zero_iff.mpr hb)
  obtain ⟨p, hp⟩ := AtomicMonoid.nonempty_factorizations ha
  refine ⟨hθ.factorizationMap p, ?_⟩
  rw [← hab.factorizations_eq]
  exact hθ.factorizationMap_mem hp

/-- Atomicity is equivalent in the source and target of a transfer homomorphism. -/
theorem atomicMonoid_iff (hθ : IsTransferHom θ) : AtomicMonoid α ↔ AtomicMonoid β := by
  constructor
  · intro h
    let _ : AtomicMonoid α := h
    exact hθ.atomicMonoid_of_source
  · intro h
    let _ : AtomicMonoid β := h
    exact hθ.atomicMonoid

/-- If the target of a transfer homomorphism is a bounded factorization monoid, so is its
source. -/
theorem boundedFactorizationMonoid (hθ : IsTransferHom θ) [BoundedFactorizationMonoid β] :
    BoundedFactorizationMonoid α where
  toAtomicMonoid := hθ.atomicMonoid
  bddAbove_factorizationLengths a ha := by
    rw [← hθ.factorizationLengths_eq]
    exact BoundedFactorizationMonoid.bddAbove_factorizationLengths (hθ.map_ne_zero ha)

/-- If the source of a transfer homomorphism is a bounded factorization monoid, so is its
target. -/
theorem boundedFactorizationMonoid_of_source (hθ : IsTransferHom θ)
    [BoundedFactorizationMonoid α] : BoundedFactorizationMonoid β := by
  refine
    { toAtomicMonoid := hθ.atomicMonoid_of_source
      bddAbove_factorizationLengths := fun b hb ↦ ?_ }
  obtain ⟨a, hab⟩ := hθ.exists_associated_map b
  have ha : a ≠ 0 := hθ.map_eq_zero_iff.not.mp (hab.ne_zero_iff.mpr hb)
  rw [← hab.factorizationLengths_eq, hθ.factorizationLengths_eq]
  exact BoundedFactorizationMonoid.bddAbove_factorizationLengths ha

/-- The bounded factorization property is equivalent in the source and target of a transfer
homomorphism. -/
theorem boundedFactorizationMonoid_iff (hθ : IsTransferHom θ) :
    BoundedFactorizationMonoid α ↔ BoundedFactorizationMonoid β := by
  constructor
  · intro h
    let _ : BoundedFactorizationMonoid α := h
    exact hθ.boundedFactorizationMonoid_of_source
  · intro h
    let _ : BoundedFactorizationMonoid β := h
    exact hθ.boundedFactorizationMonoid

/-- If the target of a transfer homomorphism is half-factorial, so is its source. This is
the usual direction for transferring half-factoriality from a simpler target. -/
theorem halfFactorialMonoid (hθ : IsTransferHom θ) [HalfFactorialMonoid β] :
    HalfFactorialMonoid α where
  toAtomicMonoid := hθ.atomicMonoid
  subsingleton_factorizationLengths a ha := by
    rw [← hθ.factorizationLengths_eq]
    exact HalfFactorialMonoid.subsingleton_factorizationLengths (hθ.map_ne_zero ha)

/-- If the source of a transfer homomorphism is half-factorial, so is its target. -/
theorem halfFactorialMonoid_of_source (hθ : IsTransferHom θ) [HalfFactorialMonoid α] :
    HalfFactorialMonoid β := by
  refine
    { toAtomicMonoid := hθ.atomicMonoid_of_source
      subsingleton_factorizationLengths := fun b hb ↦ ?_ }
  obtain ⟨a, hab⟩ := hθ.exists_associated_map b
  have ha : a ≠ 0 := hθ.map_eq_zero_iff.not.mp (hab.ne_zero_iff.mpr hb)
  rw [← hab.factorizationLengths_eq, hθ.factorizationLengths_eq]
  exact HalfFactorialMonoid.subsingleton_factorizationLengths ha

/-- Half-factoriality is equivalent in the source and target of a transfer homomorphism. -/
theorem halfFactorialMonoid_iff (hθ : IsTransferHom θ) :
    HalfFactorialMonoid α ↔ HalfFactorialMonoid β := by
  constructor
  · intro h
    let _ : HalfFactorialMonoid α := h
    exact hθ.halfFactorialMonoid_of_source
  · intro h
    let _ : HalfFactorialMonoid β := h
    exact hθ.halfFactorialMonoid

/-- Finite factorization transfers from the source of a transfer homomorphism to its target.
The converse fails in general because distinct source factorizations may have the same image.
-/
theorem finiteFactorizationMonoid_of_source (hθ : IsTransferHom θ)
    [FiniteFactorizationMonoid α] : FiniteFactorizationMonoid β := by
  refine
    { toAtomicMonoid := hθ.atomicMonoid_of_source
      finite_factorizations := fun b hb ↦ ?_ }
  obtain ⟨a, hab⟩ := hθ.exists_associated_map b
  have ha : a ≠ 0 := hθ.map_eq_zero_iff.not.mp (hab.ne_zero_iff.mpr hb)
  refine ((FiniteFactorizationMonoid.finite_factorizations ha).image hθ.factorizationMap).subset ?_
  intro q hq
  have hq' : q ∈ factorizations (θ a) := by
    rw [hab.factorizations_eq]
    exact hq
  obtain ⟨p, hp, rfl⟩ := hθ.exists_factorizationMap_eq hq'
  exact ⟨p, hp, rfl⟩

/-- Unique factorization transfers from the source of a transfer homomorphism to a target
which is already cancellative. The converse is false in general because the transfer map may
identify distinct source factorizations; cancellativity also cannot be inferred from the
transfer axioms. -/
theorem uniqueFactorizationMonoid_of_source (hθ : IsTransferHom θ)
    [UniqueFactorizationMonoid α] [IsCancelMulZero β] : UniqueFactorizationMonoid β := by
  rw [uniqueFactorizationMonoid_iff]
  refine ⟨hθ.atomicMonoid_of_source, fun b hb ↦ ?_⟩
  intro q₁ hq₁ q₂ hq₂
  obtain ⟨a, hab⟩ := hθ.exists_associated_map b
  have ha : a ≠ 0 := hθ.map_eq_zero_iff.not.mp (hab.ne_zero_iff.mpr hb)
  have hq₁' : q₁ ∈ factorizations (θ a) := by
    rw [hab.factorizations_eq]
    exact hq₁
  have hq₂' : q₂ ∈ factorizations (θ a) := by
    rw [hab.factorizations_eq]
    exact hq₂
  obtain ⟨p₁, hp₁, hp₁map⟩ := hθ.exists_factorizationMap_eq hq₁'
  obtain ⟨p₂, hp₂, hp₂map⟩ := hθ.exists_factorizationMap_eq hq₂'
  have hsource := (uniqueFactorizationMonoid_iff.mp
    (inferInstance : UniqueFactorizationMonoid α)).2 ha hp₁ hp₂
  exact hp₁map.symm.trans (congrArg hθ.factorizationMap hsource) |>.trans hp₂map

end IsTransferHom

end CommMonoidWithZero
