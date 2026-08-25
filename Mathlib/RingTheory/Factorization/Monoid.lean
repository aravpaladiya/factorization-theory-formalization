/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.Data.ENat.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Atomic, bounded, finite, and half-factorial monoids

This file defines atomic, bounded factorization, finite factorization, and half-factorial monoids,
and relates them to Mathlib's existing `WfDvdMonoid` class.

## Main definitions

* `AtomicMonoid`: every nonzero element has a factorization into irreducibles.
* `BoundedFactorizationMonoid`: factorization lengths of nonzero elements are bounded.
* `FiniteFactorizationMonoid`: nonzero elements have finitely many factorizations.
* `HalfFactorialMonoid`: factorizations of a nonzero element all have the same length.

## Main results

* A finite or half-factorial monoid is a bounded factorization monoid, and a bounded
  factorization monoid satisfies `WfDvdMonoid`.

## Implementation notes

The instances implementing the implication hierarchy have low priority to avoid competing with
more direct instances.

-/

public section

assert_not_exists Field Ideal

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section CommMonoidWithZero

variable [CommMonoidWithZero α] {a : α}

variable (α) in
/-- An atomic monoid is a commutative monoid with zero in which every nonzero element has a
factorization into irreducibles. -/
@[mk_iff] class AtomicMonoid : Prop where
  /-- Every nonzero element has a factorization into irreducibles. -/
  nonempty_factorizations : ∀ ⦃a : α⦄, a ≠ 0 → (factorizations a).Nonempty

/-- Every nonzero element of an atomic monoid is associated to a product of irreducibles. -/
theorem AtomicMonoid.exists_factors [AtomicMonoid α] (a : α) (ha : a ≠ 0) :
    ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a := by
  obtain ⟨f, hf⟩ := AtomicMonoid.nonempty_factorizations ha
  obtain ⟨g, hg, hprod, -⟩ := exists_multiset_of_mem_factorizations hf
  exact ⟨g, hg, hprod⟩

/-- A monoid in which every nonzero element is associated to a product of irreducibles is
atomic. -/
theorem AtomicMonoid.of_exists_factors
    (h : ∀ a : α, a ≠ 0 →
      ∃ f : Multiset α, (∀ b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a) :
    AtomicMonoid α :=
  ⟨fun a ha ↦ by
    obtain ⟨f, hf, hprod⟩ := h a ha
    exact ⟨Associates.Factorization.ofMultiset f hf, ofMultiset_mem_factorizations hf hprod⟩⟩

theorem nonempty_factorizationLengths [AtomicMonoid α] (ha : a ≠ 0) :
    (factorizationLengths a).Nonempty := by
  rw [factorizationLengths_def]
  exact (AtomicMonoid.nonempty_factorizations ha).image Multiset.card

variable (α) in
/-- A bounded factorization monoid is an atomic monoid in which the factorization lengths of every
nonzero element are bounded above. -/
@[mk_iff] class BoundedFactorizationMonoid : Prop extends AtomicMonoid α where
  /-- Factorization lengths of nonzero elements are bounded above. -/
  bddAbove_factorizationLengths : ∀ ⦃a : α⦄, a ≠ 0 → BddAbove (factorizationLengths a)

variable (α) in
/-- A finite factorization monoid is an atomic monoid in which every nonzero element has finitely
many factorizations up to order and associates. -/
@[mk_iff] class FiniteFactorizationMonoid : Prop extends AtomicMonoid α where
  /-- Every nonzero element has finitely many factorizations. -/
  finite_factorizations : ∀ ⦃a : α⦄, a ≠ 0 → (factorizations a).Finite

variable (α) in
/-- A half-factorial monoid is an atomic monoid in which all factorizations of a nonzero element
have the same length. -/
@[mk_iff] class HalfFactorialMonoid : Prop extends AtomicMonoid α where
  /-- Factorization lengths of a nonzero element form a subsingleton. -/
  subsingleton_factorizationLengths :
    ∀ ⦃a : α⦄, a ≠ 0 → (factorizationLengths a).Subsingleton

theorem HalfFactorialMonoid.exists_factorizationLengths_eq_singleton [HalfFactorialMonoid α]
    (ha : a ≠ 0) : ∃ n, factorizationLengths a = {n} := by
  obtain ⟨n, hn⟩ := nonempty_factorizationLengths ha
  exact ⟨n, (HalfFactorialMonoid.subsingleton_factorizationLengths ha).eq_singleton_of_mem hn⟩

/-! ### The implication hierarchy -/

-- see Note [lower instance priority]
instance (priority := 100) [WfDvdMonoid α] : AtomicMonoid α :=
  .of_exists_factors WfDvdMonoid.exists_factors

-- see Note [lower instance priority]
instance (priority := 100) [FiniteFactorizationMonoid α] : BoundedFactorizationMonoid α where
  bddAbove_factorizationLengths _ ha := by
    rw [factorizationLengths_def]
    exact ((FiniteFactorizationMonoid.finite_factorizations ha).image _).bddAbove

-- see Note [lower instance priority]
instance (priority := 100) [HalfFactorialMonoid α] : BoundedFactorizationMonoid α where
  bddAbove_factorizationLengths _ ha :=
    (HalfFactorialMonoid.subsingleton_factorizationLengths ha).finite.bddAbove

-- see Note [lower instance priority]
instance (priority := 100) [BoundedFactorizationMonoid α] : WfDvdMonoid α where
  wf := by
    -- Strict divisibility adds a nonunit factor of positive length, so it strictly increases the
    -- maximal factorization length.
    refine RelHomClass.wellFounded
      (RelHom.mk ?_ ?_ :
        (DvdNotUnit : α → α → Prop) →r ((· < ·) : ℕ∞ → ℕ∞ → Prop))
      wellFounded_lt
    · intro a
      by_cases h : a = 0
      · exact ⊤
      · exact ↑(sSup (factorizationLengths a))
    · rintro a b ⟨ha, x, hx, rfl⟩
      rw [dite_eq_right ha]
      by_cases hb : a * x = 0
      · simp [hb, lt_top_iff_ne_top]
      · rw [dite_eq_right hb, ENat.natCast_lt_natCast]
        have hx0 : x ≠ 0 := right_ne_zero_of_mul hb
        obtain ⟨g, hg⟩ := AtomicMonoid.nonempty_factorizations hx0
        have hgc : g.card ≠ 0 := fun h ↦
          hx (zero_mem_factorizationLengths_iff.mp (h ▸ card_mem_factorizationLengths hg))
        have hsup := Nat.sSup_mem (nonempty_factorizationLengths ha)
          (BoundedFactorizationMonoid.bddAbove_factorizationLengths ha)
        have hle := le_csSup (BoundedFactorizationMonoid.bddAbove_factorizationLengths hb)
          (add_subset_factorizationLengths_mul
            (Set.add_mem_add hsup (card_mem_factorizationLengths hg)))
        lia

end CommMonoidWithZero
