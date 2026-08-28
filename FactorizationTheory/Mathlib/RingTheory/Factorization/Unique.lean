/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import FactorizationTheory.Mathlib.RingTheory.Factorization.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Formal factorizations in unique factorization monoids

This file identifies the formal factorizations and factorization lengths of a nonzero element in a
unique factorization monoid with its canonical factorization.

## Main results

* `UniqueFactorizationMonoid.factorizations_eq_singleton` shows that the factorization set of a
  nonzero element is a singleton.
* `UniqueFactorizationMonoid.factorizationLengths_eq_singleton` computes its set of factorization
  lengths.
-/

public section

assert_not_exists Field Ideal

variable {α : Type*}

section UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a : α}

/-- In a unique factorization monoid, a nonzero element has only its canonical factorization. -/
theorem UniqueFactorizationMonoid.factorizations_eq_singleton (ha : a ≠ 0) :
    factorizations a =
      {Associates.Factorization.ofMultiset (UniqueFactorizationMonoid.factors a)
        irreducible_of_factor} := by
  have hmem := ofMultiset_mem_factorizations irreducible_of_factor (factors_prod ha)
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨hmem, fun f hf ↦ by
      rw [← Multiset.map_eq_map Subtype.coe_injective]
      apply Associates.unique'
      · intro p hp
        obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp hp
        exact q.property
      · intro p hp
        obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp hp
        exact q.property
      · simpa only [← Associates.Factorization.prod_def] using
          (mem_factorizations.mp hf).trans (mem_factorizations.mp hmem).symm⟩

/-- In a unique factorization monoid, the length set of a nonzero element is the singleton
containing the number of its canonical factors. -/
@[simp]
theorem UniqueFactorizationMonoid.factorizationLengths_eq_singleton (ha : a ≠ 0) :
    factorizationLengths a = {(UniqueFactorizationMonoid.factors a).card} := by
  rw [factorizationLengths_def, UniqueFactorizationMonoid.factorizations_eq_singleton ha,
    Set.image_singleton, Associates.Factorization.card_ofMultiset]

end UniqueFactorizationMonoid
