/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Divisor homomorphisms

A divisor homomorphism is a homomorphism of commutative monoids that reflects divisibility.
This file records its basic consequences: reflection of units, zero, and irreducibility.

## Main definitions

* `IsDivisorHom φ`: the homomorphism `φ` reflects divisibility.

## Main results

* `isDivisorHom_iff`: the characterization used to construct a divisor homomorphism.
* `IsDivisorHom.map_dvd_iff`: a divisor homomorphism preserves and reflects divisibility.
* `IsDivisorHom.isUnit_map_iff`: a divisor homomorphism reflects units.
* `IsDivisorHom.map_eq_zero_iff`: a divisor homomorphism reflects zero.
* `IsDivisorHom.associated_of_map_eq`: equality after a divisor homomorphism implies
  association in the source when the target is cancellative away from zero.
* `IsDivisorHom.irreducible_of_map`: a divisor homomorphism reflects irreducibility.
-/

public section

assert_not_exists IsOrderedMonoid Multiset Ring

variable {α β F : Type*}

section CommMonoid

variable [CommMonoid α] [CommMonoid β]
variable [FunLike F α β] [MonoidHomClass F α β] {φ : F}

/-- A divisor homomorphism is a homomorphism of commutative monoids which reflects
divisibility. Preservation of divisibility is automatic for every monoid homomorphism. -/
def IsDivisorHom (φ : F) : Prop :=
  ∀ ⦃a b : α⦄, φ a ∣ φ b → a ∣ b

omit [MonoidHomClass F α β] in
theorem isDivisorHom_iff : IsDivisorHom φ ↔ ∀ ⦃a b : α⦄, φ a ∣ φ b → a ∣ b :=
  Iff.rfl

theorem IsDivisorHom.map_dvd_iff (hφ : IsDivisorHom φ) {a b : α} :
    φ a ∣ φ b ↔ a ∣ b :=
  ⟨fun h ↦ hφ h, map_dvd φ⟩

omit [MonoidHomClass F α β] in
theorem IsDivisorHom.dvd_of_map_dvd (hφ : IsDivisorHom φ) {a b : α}
    (h : φ a ∣ φ b) : a ∣ b :=
  hφ h

/-- A divisor homomorphism is a local homomorphism: it reflects units. -/
theorem IsDivisorHom.isLocalHom (hφ : IsDivisorHom φ) : IsLocalHom φ := by
  refine ⟨fun a ha ↦ isUnit_iff_dvd_one.mpr ?_⟩
  apply hφ
  rw [map_one]
  exact isUnit_iff_dvd_one.mp ha

/-- A divisor homomorphism reflects units. -/
theorem IsDivisorHom.isUnit_map_iff (hφ : IsDivisorHom φ) {a : α} :
    IsUnit (φ a) ↔ IsUnit a := by
  let _ := hφ.isLocalHom
  exact _root_.isUnit_map_iff φ a

/-- A divisor homomorphism reflects irreducibility. -/
theorem IsDivisorHom.irreducible_of_map (hφ : IsDivisorHom φ)
    {a : α} (ha : Irreducible (φ a)) : Irreducible a := by
  let _ := hφ.isLocalHom
  exact ha.of_map

end CommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α] [CommMonoidWithZero β]
variable [FunLike F α β] [MonoidWithZeroHomClass F α β] {φ : F}

/-- A divisor homomorphism reflects zero. -/
theorem IsDivisorHom.map_eq_zero_iff (hφ : IsDivisorHom φ) {a : α} :
    φ a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have : (0 : α) ∣ a := hφ <| by rw [map_zero, ha]
    simpa only [zero_dvd_iff] using this
  · rintro rfl
    exact map_zero φ

theorem IsDivisorHom.map_ne_zero (hφ : IsDivisorHom φ) {a : α} (ha : a ≠ 0) :
    φ a ≠ 0 :=
  hφ.map_eq_zero_iff.not.mpr ha

/-- Equality after a divisor homomorphism implies association in the source. The target's
cancellation turns the reflected divisibility witness into a unit; no cancellation assumption
on the source is needed. -/
theorem IsDivisorHom.associated_of_map_eq [IsCancelMulZero β]
    (hφ : IsDivisorHom φ) {a b : α} (h : φ a = φ b) : Associated a b := by
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := hφ.map_eq_zero_iff.mp <| by simpa using h.symm
    subst b
    exact Associated.rfl
  have hd : φ a ∣ φ b := by rw [h]
  obtain ⟨c, hc⟩ := hφ hd
  have hφc : φ c = 1 := by
    apply mul_left_cancel₀ (hφ.map_ne_zero ha)
    calc
      φ a * φ c = φ (a * c) := (map_mul φ a c).symm
      _ = φ b := congrArg φ hc.symm
      _ = φ a := h.symm
      _ = φ a * 1 := (mul_one _).symm
  have hcunit : IsUnit c := hφ.isUnit_map_iff.mp <| hφc ▸ isUnit_one
  exact (associated_mul_unit_right a c hcunit).trans (Associated.of_eq hc.symm)

end CommMonoidWithZero
