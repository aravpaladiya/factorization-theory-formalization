/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import FactorizationTheory.Mathlib.RingTheory.Factorization.Monoid

/-!
# Unions of sets of factorization lengths

This file defines the union `U_k(H)` of the sets of factorization lengths containing a given
length `k`, from Chapter 1.4 of
[Geroldinger and Halter-Koch][geroldingerhalterkoch2006].

It proves symmetry in `k` and the member lengths, compatibility with addition, and the
half-factorial bound `U_k(H) ⊆ {k}`. Only nonzero elements contribute to `U_k(H)`.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

variable {α : Type*}

section CommMonoidWithZero

variable [CommMonoidWithZero α] {a : α} {k l m : ℕ}

variable (α) in
/-- The union of the sets of lengths meeting `k`: the lengths of factorizations of the
nonzero elements of `α` that also admit a factorization of length `k`, denoted `U_k(H)`. -/
def unionOfLengths (k : ℕ) : Set ℕ :=
  {m | ∃ a : α, a ≠ 0 ∧ k ∈ factorizationLengths a ∧ m ∈ factorizationLengths a}

@[simp]
theorem mem_unionOfLengths :
    m ∈ unionOfLengths α k ↔
      ∃ a : α, a ≠ 0 ∧ k ∈ factorizationLengths a ∧ m ∈ factorizationLengths a := by
  rfl

/-- Membership in unions of sets of lengths is symmetric. -/
theorem mem_unionOfLengths_comm : m ∈ unionOfLengths α k ↔ k ∈ unionOfLengths α m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    · obtain ⟨a, ha, hk, hm⟩ := h
      exact ⟨a, ha, hm, hk⟩

theorem factorizationLengths_subset_unionOfLengths (ha : a ≠ 0)
    (hk : k ∈ factorizationLengths a) : factorizationLengths a ⊆ unionOfLengths α k :=
  fun _ hm ↦ ⟨a, ha, hk, hm⟩

theorem mem_unionOfLengths_self (ha : a ≠ 0) (hk : k ∈ factorizationLengths a) :
    k ∈ unionOfLengths α k :=
  ⟨a, ha, hk, hk⟩

theorem unionOfLengths_zero [Nontrivial α] : unionOfLengths α 0 = {0} := by
  ext m
  refine ⟨fun h ↦ ?_, fun hm ↦ ⟨1, one_ne_zero, ?_, ?_⟩⟩
  · obtain ⟨a, -, h0, hm⟩ := h
    rwa [factorizationLengths_of_isUnit (zero_mem_factorizationLengths_iff.mp h0)] at hm
  · rw [factorizationLengths_one]
    exact rfl
  · rw [factorizationLengths_one]
    exact hm

theorem unionOfLengths_one_subset : unionOfLengths α 1 ⊆ {1} := by
  rintro m ⟨a, -, h1, hm⟩
  obtain ⟨f, hf, hcard⟩ := mem_factorizationLengths.mp h1
  obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hcard
  have hxmk : (x : Associates α) = Associates.mk a := by
    simpa only [Associates.Factorization.prod_singleton] using mem_factorizations.mp hf
  have ha : Irreducible a := Associates.irreducible_mk.mp (hxmk ▸ x.property)
  rwa [factorizationLengths_of_irreducible ha] at hm

theorem unionOfLengths_one_of_irreducible (ha : Irreducible a) :
    unionOfLengths α 1 = {1} := by
  refine Set.Subset.antisymm unionOfLengths_one_subset fun m hm ↦ ⟨a, ha.ne_zero, ?_, ?_⟩
  · rw [factorizationLengths_of_irreducible ha]
    exact rfl
  · rw [factorizationLengths_of_irreducible ha]
    exact hm

open scoped Pointwise in
/-- Sets of lengths meeting `k` and `l` add into the set of lengths meeting `k + l`, by
concatenating factorizations. Zero divisors are excluded so that the product of the two
witnesses stays nonzero. -/
theorem add_subset_unionOfLengths_add [NoZeroDivisors α] :
    unionOfLengths α k + unionOfLengths α l ⊆ unionOfLengths α (k + l) := by
  rw [Set.add_subset_iff]
  rintro m ⟨a, ha, hka, hma⟩ n ⟨b, hb, hlb, hnb⟩
  exact ⟨a * b, mul_ne_zero ha hb,
    add_subset_factorizationLengths_mul (Set.add_mem_add hka hlb),
    add_subset_factorizationLengths_mul (Set.add_mem_add hma hnb)⟩

/-- In a half-factorial monoid, every member of the union at `k` is equal to `k`. -/
theorem HalfFactorialMonoid.unionOfLengths_subset_singleton [HalfFactorialMonoid α] :
    unionOfLengths α k ⊆ {k} := by
  rintro m ⟨a, ha, hk, hm⟩
  simpa only [Set.mem_singleton_iff] using
    HalfFactorialMonoid.subsingleton_factorizationLengths ha hm hk

theorem HalfFactorialMonoid.unionOfLengths_subsingleton [HalfFactorialMonoid α] :
    (unionOfLengths α k).Subsingleton :=
  Set.subsingleton_of_subset_singleton
    (HalfFactorialMonoid.unionOfLengths_subset_singleton (α := α) (k := k))

end CommMonoidWithZero
