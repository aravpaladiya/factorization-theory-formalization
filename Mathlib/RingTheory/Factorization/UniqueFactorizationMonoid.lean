/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.Monoid
public import Mathlib.RingTheory.Factorization.Unique

/-!
# Unique factorization and the factorization hierarchy

This file relates unique factorization monoids to the factorization classes defined in
`Mathlib.RingTheory.Factorization.Monoid`.

## Main results

* A unique factorization monoid is both a finite factorization monoid and half-factorial.
* `uniqueFactorizationMonoid_iff` characterizes unique factorization by atomicity and uniqueness of
  formal factorizations.

## Implementation notes

The instances implementing the implications from unique factorization have low priority to avoid
competing with more direct instances.

-/

public section

assert_not_exists Field Ideal

variable {α : Type*}

section CommMonoidWithZero

variable [CommMonoidWithZero α]

-- see Note [lower instance priority]
instance (priority := 100) [UniqueFactorizationMonoid α] : FiniteFactorizationMonoid α where
  finite_factorizations _ ha := by
    simp [UniqueFactorizationMonoid.factorizations_eq_singleton ha]

-- see Note [lower instance priority]
instance (priority := 100) [UniqueFactorizationMonoid α] : HalfFactorialMonoid α where
  subsingleton_factorizationLengths _ ha := by
    rw [UniqueFactorizationMonoid.factorizationLengths_eq_singleton ha]
    exact Set.subsingleton_singleton

/-- A cancellative monoid with zero is a unique factorization monoid if and only if it is atomic
and every nonzero element has at most one factorization. -/
theorem uniqueFactorizationMonoid_iff [IsCancelMulZero α] :
    UniqueFactorizationMonoid α ↔
      AtomicMonoid α ∧ ∀ ⦃a : α⦄, a ≠ 0 → (factorizations a).Subsingleton := by
  refine ⟨fun h ↦ ⟨inferInstance, fun a ha ↦ by
    simp [UniqueFactorizationMonoid.factorizations_eq_singleton ha]⟩, fun ⟨hA, hU⟩ ↦ ?_⟩
  obtain h | h := subsingleton_or_nontrivial α
  · exact UniqueFactorizationMonoid.of_subsingleton α
  · exact .of_existsUnique_irreducible_factors AtomicMonoid.exists_factors
      fun f g hf hg hfg ↦ Associates.rel_associated_iff_map_eq_map.mpr <| by
        have hfac := hU (Multiset.prod_ne_zero fun h0 ↦ not_irreducible_zero (hf 0 h0))
          (ofMultiset_mem_factorizations hf Associated.rfl)
          (ofMultiset_mem_factorizations hg hfg.symm)
        simpa only [Associates.Factorization.map_coe_ofMultiset] using congrArg
          (Multiset.map
            ((↑) : {p : Associates α // Irreducible p} → Associates α)) hfac

end CommMonoidWithZero
