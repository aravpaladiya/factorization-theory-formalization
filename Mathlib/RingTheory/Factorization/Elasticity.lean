/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.RingTheory.Factorization.Lengths
public import Mathlib.RingTheory.Factorization.UniqueFactorizationMonoid

/-!
# Elasticity of factorizations

This file defines the elasticity of an element of a commutative monoid — the ratio of its maximal
and minimal factorization lengths, valued in `ℝ≥0∞`, with the standard elasticity-`1`
convention for the unit set of lengths `{0}`. It also defines the elasticity of a commutative
monoid with zero and characterizes half-factorial monoids using both notions of elasticity.

## Main results

* `halfFactorialMonoid_iff_forall_elasticity_eq_one`: a monoid is half-factorial iff it is
  atomic and every nonzero element has elasticity `1`.
* `halfFactorialMonoid_iff_monoidElasticity_eq_one`: a monoid is half-factorial iff it is atomic
  and its monoid elasticity is `1`.

## Implementation notes

Following Definition 1.4.1 of [Geroldinger and Halter-Koch][geroldingerhalterkoch2006], the set of
lengths `{0}` has elasticity `1`. An element with no factorization has elasticity `0`, and monoid
elasticity includes the unit contribution as a baseline `1`.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public noncomputable section

assert_not_exists Ideal

open scoped ENNReal

variable {α : Type*}

section CommMonoid

variable [CommMonoid α] {a b : α}

/-- The elasticity of `a`, as an element of `ℝ≥0∞`. A unit has elasticity `1`, following the
convention that the elasticity of the set of lengths `{0}` is `1`; otherwise this is the
ratio of the maximal and minimal factorization lengths. An element with no factorization
has elasticity `0`. -/
def elasticity (a : α) : ℝ≥0∞ := by
  classical
  exact if IsUnit a then 1 else
    (maxFactorizationLength a : ℝ≥0∞) / (minFactorizationLength a : ℝ≥0∞)

open scoped Classical in
theorem elasticity_def :
    elasticity a = if IsUnit a then 1 else
      (maxFactorizationLength a : ℝ≥0∞) / (minFactorizationLength a : ℝ≥0∞) := by
  rfl

@[simp]
theorem elasticity_of_isUnit (h : IsUnit a) : elasticity a = 1 := by
  simp [elasticity, h]

@[simp]
theorem elasticity_of_irreducible (h : Irreducible a) : elasticity a = 1 := by
  simp [elasticity, h, h.not_isUnit]

theorem Associated.elasticity_eq (h : Associated a b) : elasticity a = elasticity b := by
  by_cases ha : IsUnit a
  · rw [elasticity_of_isUnit ha, elasticity_of_isUnit (h.isUnit ha)]
  · have hb : ¬IsUnit b := fun hb ↦ ha (h.symm.isUnit hb)
    rw [elasticity_def, elasticity_def, ite_eq_right ha, ite_eq_right hb,
      h.maxFactorizationLength_eq, h.minFactorizationLength_eq]

end CommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α] {a : α}

variable (α) in
/-- The elasticity of a monoid: the join of `1` with the supremum of the elasticities of its
nonzero nonunits. The initial `1` accounts for units and makes the elasticity of a subsingleton
monoid with zero equal to `1`. -/
def Monoid.elasticity : ℝ≥0∞ :=
  1 ⊔ ⨆ (a : α) (_ : a ≠ 0) (_ : ¬IsUnit a), _root_.elasticity a

theorem Monoid.elasticity_def :
    Monoid.elasticity α =
      1 ⊔ ⨆ (a : α) (_ : a ≠ 0) (_ : ¬IsUnit a), _root_.elasticity a := by
  rfl

theorem one_le_elasticity [AtomicMonoid α] (ha : a ≠ 0) :
    1 ≤ elasticity a := by
  by_cases hu : IsUnit a
  · rw [elasticity_of_isUnit hu]
  obtain ⟨n, -, hn⟩ :=
    exists_natCast_eq_minFactorizationLength (nonempty_factorizationLengths ha)
  rw [elasticity, ite_eq_right hu, ENNReal.le_div_iff_mul_le
    (.inl <| ENat.toENNReal_eq_zero.not.mpr <| Order.one_le_iff_ne_zero.mp <|
      one_le_minFactorizationLength_iff.mpr hu)
    (.inl <| ENat.toENNReal_ne_top.mpr <| hn ▸ ENat.natCast_ne_top n), one_mul]
  exact ENat.toENNReal_le.mpr
    (minFactorizationLength_le_maxFactorizationLength (nonempty_factorizationLengths ha))

theorem elasticity_eq_one_iff [AtomicMonoid α] (ha : a ≠ 0) :
    elasticity a = 1 ↔ maxFactorizationLength a = minFactorizationLength a := by
  by_cases hu : IsUnit a
  · simp [hu]
  obtain ⟨n, -, hn⟩ :=
    exists_natCast_eq_minFactorizationLength (nonempty_factorizationLengths ha)
  rw [elasticity, ite_eq_right hu, ENNReal.div_eq_one_iff, ENat.toENNReal_inj]
  · simpa [Order.one_le_iff_ne_zero] using one_le_minFactorizationLength_iff.mpr hu
  · simp [← hn]

theorem Monoid.le_elasticity (ha : a ≠ 0) :
    _root_.elasticity a ≤ Monoid.elasticity α := by
  rw [Monoid.elasticity]
  by_cases hu : IsUnit a
  · rw [elasticity_of_isUnit hu]
    exact le_sup_left
  · exact le_sup_of_le_right <|
      le_iSup_of_le a <| le_iSup_of_le ha <| le_iSup_of_le hu le_rfl

theorem Monoid.one_le_elasticity : 1 ≤ Monoid.elasticity α := by
  rw [Monoid.elasticity]
  exact le_sup_left

/-- Every nonzero element of a half-factorial monoid has elasticity `1`. -/
theorem HalfFactorialMonoid.elasticity_eq_one [HalfFactorialMonoid α] (ha : a ≠ 0) :
    elasticity a = 1 := by
  rw [elasticity_eq_one_iff ha,
    maxFactorizationLength_eq_minFactorizationLength_iff (nonempty_factorizationLengths ha)]
  exact HalfFactorialMonoid.subsingleton_factorizationLengths ha

/-- A monoid is half-factorial if and only if it is atomic and every nonzero element has
elasticity `1`. -/
theorem halfFactorialMonoid_iff_forall_elasticity_eq_one :
    HalfFactorialMonoid α ↔
      AtomicMonoid α ∧ ∀ ⦃a : α⦄, a ≠ 0 → elasticity a = 1 := by
  constructor
  · intro h
    let _ : HalfFactorialMonoid α := h
    exact ⟨inferInstance, fun _ ha ↦ HalfFactorialMonoid.elasticity_eq_one ha⟩
  · rintro ⟨hAtomic, hElasticity⟩
    let _ : AtomicMonoid α := hAtomic
    refine
      { toAtomicMonoid := hAtomic
        subsingleton_factorizationLengths := fun _ ha ↦
          (maxFactorizationLength_eq_minFactorizationLength_iff
            (nonempty_factorizationLengths ha)).mp ((elasticity_eq_one_iff ha).mp
              (hElasticity ha)) }

/-- A commutative monoid with zero is half-factorial if and only if it is atomic and its monoid
elasticity is `1`. -/
theorem halfFactorialMonoid_iff_monoidElasticity_eq_one :
    HalfFactorialMonoid α ↔ AtomicMonoid α ∧ Monoid.elasticity α = 1 := by
  constructor
  · intro hHalfFactorial
    let _ : HalfFactorialMonoid α := hHalfFactorial
    refine ⟨inferInstance, le_antisymm ?_ Monoid.one_le_elasticity⟩
    rw [Monoid.elasticity]
    exact sup_le le_rfl <| iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun _ ↦
      (HalfFactorialMonoid.elasticity_eq_one ha).le
  · rintro ⟨hAtomic, hElasticity⟩
    let _ : AtomicMonoid α := hAtomic
    rw [halfFactorialMonoid_iff_forall_elasticity_eq_one]
    refine ⟨hAtomic, fun _ ha ↦ le_antisymm ?_ (one_le_elasticity ha)⟩
    exact hElasticity ▸ Monoid.le_elasticity ha

theorem UniqueFactorizationMonoid.elasticity_eq_one [UniqueFactorizationMonoid α]
    (ha : a ≠ 0) : elasticity a = 1 :=
  HalfFactorialMonoid.elasticity_eq_one ha

end CommMonoidWithZero

section CommGroupWithZero

variable [CommGroupWithZero α]

@[simp]
theorem Monoid.elasticity_eq_one_of_commGroupWithZero : Monoid.elasticity α = 1 := by
  refine le_antisymm ?_ Monoid.one_le_elasticity
  rw [Monoid.elasticity]
  refine sup_le le_rfl <| iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun hu ↦ ?_
  exact (hu (isUnit_iff_ne_zero.mpr ha)).elim

end CommGroupWithZero
