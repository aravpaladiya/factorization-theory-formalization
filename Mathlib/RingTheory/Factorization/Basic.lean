/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Factorizations into irreducibles

This file defines formal factorizations into irreducibles, their evaluation, and the sets of
factorizations and factorization lengths of an element.

## Main definitions

* `Associates.Factorization`: a multiset of irreducible elements of `Associates α`.
* `Associates.Factorization.prod`: the associate class represented by a factorization.
* `factorizations`: the set of factorizations of an element.
* `factorizationLengths`: the set of lengths of factorizations of an element.

## Main results

* `factorizations_of_isUnit`, `factorizations_zero`, and `factorizations_of_irreducible` compute
  the factorizations of units, zero in a nontrivial monoid without zero divisors, and irreducible
  elements.
* `add_subset_factorizationLengths_mul` shows that concatenating factorizations adds their
  lengths.

## Implementation notes

`Associates.Factorization α` is the free commutative monoid on the irreducible elements of the
reduced monoid `Associates α`. It is the finite branch of `Associates.FactorSet`, without the
extra top element used there to represent the factorization of zero. It is intentionally an
abbreviation, so that the `Multiset` API is directly available for formal factorizations.

The fiber `factorizations a` is a `Set`, since it need not be finite. It is defined uniformly,
including at zero when the ambient monoid has a zero. Its membership predicate simplifies to
`f.prod = Associates.mk a`.
-/

public section

assert_not_exists Field Ideal

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace Associates

variable [CommMonoid α]

private theorem irreducible_mk_iff {a : α} :
    Irreducible (Associates.mk a) ↔ Irreducible a := by
  simp only [irreducible_iff, isUnit_mk, forall_associated, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := a)]
  apply Iff.rfl.and
  constructor
  · rintro h x y rfl
    exact h _ _ <| .refl _
  · rintro h x y ⟨u, rfl⟩
    simpa using h (mul_assoc _ _ _)

/-- A formal factorization of an element of `α`, represented as a multiset of irreducible
associate classes. -/
abbrev Factorization.{u} (α : Type u) [CommMonoid α] : Type u :=
  Multiset {p : Associates α // Irreducible p}

namespace Factorization

/-- Evaluate a factorization by multiplying its irreducible associate classes. -/
def prod (f : Associates.Factorization α) : Associates α :=
  (f.map ((↑) : {p : Associates α // Irreducible p} → Associates α)).prod

theorem prod_def (f : Associates.Factorization α) :
    prod f = (f.map ((↑) : {p : Associates α // Irreducible p} → Associates α)).prod := by
  rfl

@[simp]
theorem prod_zero : prod (0 : Associates.Factorization α) = 1 := by
  simp [prod]

@[simp]
theorem prod_singleton (p : {p : Associates α // Irreducible p}) :
    prod ({p} : Associates.Factorization α) = p := by
  simp [prod]

@[simp]
theorem prod_cons (p : {p : Associates α // Irreducible p})
    (f : Associates.Factorization α) : prod (p ::ₘ f) = p * prod f := by
  simp [prod]

@[simp]
theorem prod_add (f g : Associates.Factorization α) : prod (f + g) = prod f * prod g := by
  simp [prod]

@[simp]
theorem prod_eq_one_iff {f : Associates.Factorization α} : prod f = 1 ↔ f = 0 := by
  constructor
  · exact fun h ↦ Multiset.eq_zero_of_forall_notMem fun p hp ↦ p.property.ne_one <|
      Associates.prod_eq_one_iff.mp h p (Multiset.mem_map_of_mem _ hp)
  · rintro rfl
    exact prod_zero

/-- Turn a multiset of irreducible elements of `α` into a factorization by passing to associate
classes. -/
def ofMultiset (f : Multiset α) (hf : ∀ p ∈ f, Irreducible p) : Associates.Factorization α :=
  f.pmap (p := Irreducible)
    (fun p hp ↦ ⟨Associates.mk p, irreducible_mk_iff.mpr hp⟩) hf

@[simp]
theorem map_coe_ofMultiset (f : Multiset α) (hf : ∀ p ∈ f, Irreducible p) :
    (ofMultiset f hf).map ((↑) : {p : Associates α // Irreducible p} → Associates α) =
      f.map Associates.mk := by
  simp [ofMultiset, Multiset.map_pmap, Multiset.pmap_eq_map]

@[simp]
theorem prod_ofMultiset (f : Multiset α) (hf : ∀ p ∈ f, Irreducible p) :
    prod (ofMultiset f hf) = Associates.mk f.prod := by
  rw [prod, map_coe_ofMultiset, Associates.prod_mk]

@[simp]
theorem card_ofMultiset (f : Multiset α) (hf : ∀ p ∈ f, Irreducible p) :
    (ofMultiset f hf).card = f.card := by
  simp [ofMultiset]

end Factorization

end Associates

section CommMonoid

variable [CommMonoid α] {a b : α}

/-- The set of factorizations of `a` into irreducibles, up to order and associates. -/
def factorizations (a : α) : Set (Associates.Factorization α) :=
  {f | f.prod = Associates.mk a}

/-- The set of lengths of factorizations of `a`. -/
def factorizationLengths (a : α) : Set ℕ :=
  Multiset.card '' factorizations a

theorem factorizationLengths_def :
    factorizationLengths a = Multiset.card '' factorizations a := by
  rfl

@[simp]
theorem mem_factorizations {f : Associates.Factorization α} :
    f ∈ factorizations a ↔ f.prod = Associates.mk a := by
  rfl

theorem mem_factorizationLengths {n : ℕ} :
    n ∈ factorizationLengths a ↔ ∃ f ∈ factorizations a, f.card = n := by
  exact Set.mem_image _ _ _

theorem card_mem_factorizationLengths {f : Associates.Factorization α}
    (hf : f ∈ factorizations a) : f.card ∈ factorizationLengths a := by
  exact Set.mem_image_of_mem _ hf

theorem Associated.factorizations_eq (h : a ~ᵤ b) : factorizations a = factorizations b := by
  simp only [factorizations, Associates.mk_eq_mk_iff_associated.mpr h]

theorem Associated.factorizationLengths_eq (h : a ~ᵤ b) :
    factorizationLengths a = factorizationLengths b := by
  rw [factorizationLengths, factorizationLengths, h.factorizations_eq]

/-- A multiset of irreducible elements whose product is associated to `a` determines a
factorization of `a`. -/
theorem ofMultiset_mem_factorizations {f : Multiset α} (hf : ∀ b ∈ f, Irreducible b)
    (hprod : f.prod ~ᵤ a) :
    Associates.Factorization.ofMultiset f hf ∈ factorizations a := by
  rw [mem_factorizations, Associates.Factorization.prod_ofMultiset]
  exact Associates.mk_eq_mk_iff_associated.mpr hprod

/-- Every factorization of `a` can be represented by a multiset of irreducible elements of `α`.
Passing that multiset back to associate classes recovers the original factorization. -/
theorem exists_multiset_of_mem_factorizations {f : Associates.Factorization α}
    (hf : f ∈ factorizations a) :
    ∃ g : Multiset α, ∃ hg : ∀ b ∈ g, Irreducible b,
      g.prod ~ᵤ a ∧ Associates.Factorization.ofMultiset g hg = f := by
  obtain ⟨g, hmap⟩ := Multiset.map_surjective_of_surjective Associates.mk_surjective
    (f.map ((↑) : {p : Associates α // Irreducible p} → Associates α))
  have hg : ∀ b ∈ g, Irreducible b := by
    intro b hb
    have hb' : Associates.mk b ∈ g.map Associates.mk := Multiset.mem_map_of_mem _ hb
    rw [hmap] at hb'
    obtain ⟨p, hp, heq⟩ := Multiset.mem_map.mp hb'
    exact Associates.irreducible_mk_iff.mp (heq ▸ p.property)
  refine ⟨g, hg, ?_, ?_⟩
  · apply Associates.mk_eq_mk_iff_associated.mp
    exact Associates.prod_mk.symm.trans <| by
      rw [hmap]
      exact hf
  · rw [← Multiset.map_eq_map Subtype.coe_injective,
      Associates.Factorization.map_coe_ofMultiset, hmap]

@[simp]
theorem factorizations_of_isUnit (ha : IsUnit a) : factorizations a = {0} := by
  ext f
  simp [Associates.mk_eq_one.mpr ha]

theorem factorizations_one : factorizations (1 : α) = {0} :=
  factorizations_of_isUnit isUnit_one

@[simp]
theorem factorizationLengths_of_isUnit (ha : IsUnit a) : factorizationLengths a = {0} := by
  rw [factorizationLengths, factorizations_of_isUnit ha, Set.image_singleton,
    Multiset.card_zero]

theorem factorizationLengths_one : factorizationLengths (1 : α) = {0} :=
  factorizationLengths_of_isUnit isUnit_one

/-- Zero is a factorization length of an element exactly when that element is a unit. -/
@[simp]
theorem zero_mem_factorizationLengths_iff : 0 ∈ factorizationLengths a ↔ IsUnit a := by
  simp [mem_factorizationLengths, Multiset.card_eq_zero, ← Associates.mk_eq_one, eq_comm]

@[simp]
theorem factorizations_of_irreducible (ha : Irreducible a) :
    factorizations a =
      {Associates.Factorization.ofMultiset {a} (by simpa using ha)} := by
  have hmk := Associates.irreducible_mk_iff.mpr ha
  let p : {p : Associates α // Irreducible p} := ⟨Associates.mk a, hmk⟩
  have h : factorizations a = {{p}} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨by simp [p], fun f hprod ↦ ?_⟩
    change f.prod = Associates.mk a at hprod
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero fun hf : f = 0 ↦
      hmk.ne_one (hprod.symm.trans <| by rw [hf, Associates.Factorization.prod_zero])
    obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem hx
    rw [Associates.Factorization.prod_cons] at hprod
    have hs : Associates.Factorization.prod s = 1 :=
      (hprod.symm ▸ hmk).eq_one_or_eq_one.resolve_left x.property.ne_one
    have hxmk : (x : Associates α) = Associates.mk a := by
      rw [hs, mul_one] at hprod
      exact hprod
    have hxp : x = p := Subtype.ext (by simpa [p] using hxmk)
    have hs0 : s = 0 := Associates.Factorization.prod_eq_one_iff.mp hs
    simp [hs0, hxp]
  rw [h]
  congr 2

@[simp]
theorem factorizationLengths_of_irreducible (ha : Irreducible a) :
    factorizationLengths a = {1} := by
  rw [factorizationLengths, factorizations_of_irreducible ha, Set.image_singleton,
    Associates.Factorization.card_ofMultiset, Multiset.card_singleton]

theorem add_mem_factorizations_mul {f g : Associates.Factorization α}
    (hf : f ∈ factorizations a) (hg : g ∈ factorizations b) :
    f + g ∈ factorizations (a * b) := by
  rw [mem_factorizations, Associates.Factorization.prod_add, hf, hg, Associates.mk_mul_mk]

open scoped Pointwise in
/-- Concatenating a factorization of `a` and a factorization of `b` gives a factorization of
`a * b`, so the pointwise sum of their length sets is contained in the length set of `a * b`. -/
theorem add_subset_factorizationLengths_mul :
    factorizationLengths a + factorizationLengths b ⊆ factorizationLengths (a * b) := by
  rw [Set.add_subset_iff]
  rintro n ⟨f, hf, rfl⟩ m ⟨g, hg, rfl⟩
  exact ⟨f + g, add_mem_factorizations_mul hf hg, Multiset.card_add f g⟩

end CommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- In a nontrivial monoid without zero divisors, zero has no factorization into irreducibles. -/
@[simp]
theorem factorizations_zero [NoZeroDivisors α] [Nontrivial α] :
    factorizations (0 : α) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨g, hg, hprod, -⟩ := exists_multiset_of_mem_factorizations hf
  exact Multiset.prod_ne_zero (fun hmem ↦ not_irreducible_zero (hg 0 hmem))
    (associated_zero_iff_eq_zero _ |>.mp hprod)

/-- In a nontrivial monoid without zero divisors, zero has no factorization lengths. -/
@[simp]
theorem factorizationLengths_zero [NoZeroDivisors α] [Nontrivial α] :
    factorizationLengths (0 : α) = ∅ := by
  rw [factorizationLengths_def, factorizations_zero, Set.image_empty]

end CommMonoidWithZero
