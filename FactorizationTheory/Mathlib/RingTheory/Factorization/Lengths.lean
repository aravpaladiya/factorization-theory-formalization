/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Data.ENat.Lattice
public import FactorizationTheory.Mathlib.RingTheory.Factorization.Monoid

/-!
# Maximal and minimal factorization lengths

This file defines the `ℕ∞`-valued maximal and minimal factorization lengths of an element of a
commutative monoid, develops their elementary API, and characterizes bounded factorization monoids
in terms of the maximal length.

## Main results

* `boundedFactorizationMonoid_iff_forall_maxFactorizationLength_ne_top`: a monoid is a
  BF-monoid iff it is atomic and every nonzero element has finite maximal length.
* `maxFactorizationLength_eq_minFactorizationLength_iff`: for a nonempty set of factorization
  lengths, the two extrema agree exactly when the set is a subsingleton.

## Implementation notes

If `a` has no factorization, its maximal length is `0` and its minimal length is `⊤`. Taking
`sSup` and `sInf` after mapping into `ℕ∞` records an unbounded set of lengths as `⊤`, rather
than using the fallback value `0` of `Nat.sSup`.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public noncomputable section

assert_not_exists Field Ideal

variable {α : Type*}

section CommMonoid

variable [CommMonoid α] {a b : α}

/-- The maximal length of a factorization of `a` into irreducibles, as an element of `ℕ∞`.
If `a` has unbounded factorization lengths this is `⊤`; if `a` has no factorization it
is `0`. -/
def maxFactorizationLength (a : α) : ℕ∞ :=
  sSup (((↑) : ℕ → ℕ∞) '' factorizationLengths a)

theorem maxFactorizationLength_def :
    maxFactorizationLength a = sSup (((↑) : ℕ → ℕ∞) '' factorizationLengths a) := by
  rfl

/-- The minimal length of a factorization of `a` into irreducibles, as an element of `ℕ∞`.
If `a` has no factorization it is `⊤`. -/
def minFactorizationLength (a : α) : ℕ∞ :=
  sInf (((↑) : ℕ → ℕ∞) '' factorizationLengths a)

theorem minFactorizationLength_def :
    minFactorizationLength a = sInf (((↑) : ℕ → ℕ∞) '' factorizationLengths a) := by
  rfl

theorem Associated.maxFactorizationLength_eq (h : Associated a b) :
    maxFactorizationLength a = maxFactorizationLength b := by
  rw [maxFactorizationLength_def, maxFactorizationLength_def, h.factorizationLengths_eq]

theorem Associated.minFactorizationLength_eq (h : Associated a b) :
    minFactorizationLength a = minFactorizationLength b := by
  rw [minFactorizationLength_def, minFactorizationLength_def, h.factorizationLengths_eq]

theorem maxFactorizationLength_of_factorizations_eq_empty (h : factorizations a = ∅) :
    maxFactorizationLength a = 0 := by
  rw [maxFactorizationLength, factorizationLengths_def, h, Set.image_empty, Set.image_empty,
    sSup_empty, bot_eq_zero]

theorem minFactorizationLength_of_factorizations_eq_empty (h : factorizations a = ∅) :
    minFactorizationLength a = ⊤ := by
  rw [minFactorizationLength, factorizationLengths_def, h, Set.image_empty, Set.image_empty,
    sInf_empty]

@[simp]
theorem maxFactorizationLength_of_isUnit (h : IsUnit a) : maxFactorizationLength a = 0 := by
  rw [maxFactorizationLength, factorizationLengths_of_isUnit h, Set.image_singleton,
    sSup_singleton, Nat.cast_zero]

@[simp]
theorem minFactorizationLength_of_isUnit (h : IsUnit a) : minFactorizationLength a = 0 := by
  rw [minFactorizationLength, factorizationLengths_of_isUnit h, Set.image_singleton,
    sInf_singleton, Nat.cast_zero]

@[simp]
theorem maxFactorizationLength_of_irreducible (h : Irreducible a) :
    maxFactorizationLength a = 1 := by
  rw [maxFactorizationLength, factorizationLengths_of_irreducible h, Set.image_singleton,
    sSup_singleton, Nat.cast_one]

@[simp]
theorem minFactorizationLength_of_irreducible (h : Irreducible a) :
    minFactorizationLength a = 1 := by
  rw [minFactorizationLength, factorizationLengths_of_irreducible h, Set.image_singleton,
    sInf_singleton, Nat.cast_one]

theorem minFactorizationLength_le_maxFactorizationLength
    (h : (factorizationLengths a).Nonempty) :
    minFactorizationLength a ≤ maxFactorizationLength a :=
  sInf_le_sSup (h.image _)

theorem maxFactorizationLength_ne_top_iff :
    maxFactorizationLength a ≠ ⊤ ↔ BddAbove (factorizationLengths a) := by
  rw [maxFactorizationLength, Set.image_eq_range, sSup_range, ENat.iSup_natCast_ne_top,
    Subtype.range_coe]

/-- The maximal factorization length of an element with nonempty, bounded lengths is attained. -/
theorem exists_natCast_eq_maxFactorizationLength (hne : (factorizationLengths a).Nonempty)
    (hbdd : BddAbove (factorizationLengths a)) :
    ∃ n ∈ factorizationLengths a, (n : ℕ∞) = maxFactorizationLength a := by
  refine ⟨sSup (factorizationLengths a), Nat.sSup_mem hne hbdd, ?_⟩
  rw [maxFactorizationLength, sSup_image]
  exact ENat.natCast_sSup hbdd

/-- The minimal factorization length of an element with a factorization is attained. -/
theorem exists_natCast_eq_minFactorizationLength (hne : (factorizationLengths a).Nonempty) :
    ∃ n ∈ factorizationLengths a, (n : ℕ∞) = minFactorizationLength a := by
  refine ⟨sInf (factorizationLengths a), Nat.sInf_mem hne, ?_⟩
  rw [minFactorizationLength, sInf_image]
  exact ENat.natCast_sInf hne

/-- For a nonempty set of factorization lengths, its maximal and minimal lengths agree if and only
if it is a subsingleton. -/
theorem maxFactorizationLength_eq_minFactorizationLength_iff
    (hne : (factorizationLengths a).Nonempty) :
    maxFactorizationLength a = minFactorizationLength a ↔
      (factorizationLengths a).Subsingleton := by
  constructor
  · intro h m hm n hn
    apply ENat.natCast_inj.mp
    apply le_antisymm
    · calc
        (m : ℕ∞) ≤ maxFactorizationLength a := by
          rw [maxFactorizationLength_def]
          exact le_sSup ⟨m, hm, rfl⟩
        _ = minFactorizationLength a := h
        _ ≤ (n : ℕ∞) := by
          rw [minFactorizationLength_def]
          exact sInf_le ⟨n, hn, rfl⟩
    · calc
        (n : ℕ∞) ≤ maxFactorizationLength a := by
          rw [maxFactorizationLength_def]
          exact le_sSup ⟨n, hn, rfl⟩
        _ = minFactorizationLength a := h
        _ ≤ (m : ℕ∞) := by
          rw [minFactorizationLength_def]
          exact sInf_le ⟨m, hm, rfl⟩
  · intro h
    obtain ⟨n, hn⟩ := hne
    rw [maxFactorizationLength_def, minFactorizationLength_def,
      h.eq_singleton_of_mem hn, Set.image_singleton, sSup_singleton, sInf_singleton]

theorem one_le_minFactorizationLength_iff :
    1 ≤ minFactorizationLength a ↔ ¬IsUnit a := by
  rw [Order.one_le_iff_ne_zero, ne_eq, minFactorizationLength, ENat.sInf_eq_zero]
  simp [zero_mem_factorizationLengths_iff]

open scoped Pointwise in
theorem le_maxFactorizationLength_mul (ha : (factorizationLengths a).Nonempty)
    (hb : (factorizationLengths b).Nonempty) :
    maxFactorizationLength a + maxFactorizationLength b ≤ maxFactorizationLength (a * b) := by
  simp only [maxFactorizationLength, sSup_image]
  exact ENat.biSup_add_biSup_le ha hb fun m hm n hn ↦
    le_iSup₂_of_le (m + n) (add_subset_factorizationLengths_mul (Set.add_mem_add hm hn))
      (Nat.cast_add m n).ge

open scoped Pointwise in
theorem minFactorizationLength_mul_le (ha : (factorizationLengths a).Nonempty)
    (hb : (factorizationLengths b).Nonempty) :
    minFactorizationLength (a * b) ≤ minFactorizationLength a + minFactorizationLength b := by
  obtain ⟨m, hm, hm'⟩ := exists_natCast_eq_minFactorizationLength ha
  obtain ⟨n, hn, hn'⟩ := exists_natCast_eq_minFactorizationLength hb
  rw [minFactorizationLength, ← hm', ← hn', ← Nat.cast_add]
  exact sInf_le ⟨m + n, add_subset_factorizationLengths_mul (Set.add_mem_add hm hn), rfl⟩

end CommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- A commutative monoid with zero is a bounded factorization monoid if and only if it is atomic
and every nonzero element has finite maximal factorization length. -/
theorem boundedFactorizationMonoid_iff_forall_maxFactorizationLength_ne_top :
    BoundedFactorizationMonoid α ↔
      AtomicMonoid α ∧ ∀ ⦃a : α⦄, a ≠ 0 → maxFactorizationLength a ≠ ⊤ := by
  simp_rw [boundedFactorizationMonoid_iff, ← maxFactorizationLength_ne_top_iff]

end CommMonoidWithZero
