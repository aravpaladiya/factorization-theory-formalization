/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import FactorizationTheory.Mathlib.RingTheory.Factorization.DivisorTheory.ClassGroup
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

import FactorizationTheory.Mathlib.RingTheory.Factorization.DivisorTheory.Finite

/-!
# Divisor theories and unique factorization

This file constructs the canonical divisor theory of a unique factorization monoid and proves
the converse class-group criterion: an explicit divisor theory with trivial class group gives
unique factorization.

## Main results

* `UniqueFactorizationMonoid.divisorTheory`: the canonical divisor theory by irreducible
  associate classes.
* `UniqueFactorizationMonoid.divisorTheory_apply_of_ne_zero` and
  `UniqueFactorizationMonoid.divisorTheory_surjective`: its value and surjectivity laws.
* `UniqueFactorizationMonoid.divisorTheory_classGroup_subsingleton`: its class group is trivial.
* `DivisorTheory.uniqueFactorizationMonoid_of_classGroup_subsingleton`: a trivial explicit
  class group gives unique factorization.
-/

public section

assert_not_exists FractionalIdeal Ideal

universe u v

variable {α : Type u} {P : Type v} [CommMonoidWithZero α]

/-! ### Canonical divisor theory -/

private def factorSetToDivisor : Associates.FactorSet α →
    DivisorMonoid {p : Associates α // Irreducible p}
  | none => none
  | some s => some (Multiplicative.ofAdd s)

private def divisorToFactorSet : DivisorMonoid {p : Associates α // Irreducible p} →
    Associates.FactorSet α
  | none => none
  | some s => some s.toAdd

private theorem factorSetToDivisor_add (s t : Associates.FactorSet α) :
    factorSetToDivisor (s + t) = factorSetToDivisor s * factorSetToDivisor t := by
  cases s <;> cases t <;> rfl

private theorem divisorToFactorSet_factorSetToDivisor (s : Associates.FactorSet α) :
    divisorToFactorSet (factorSetToDivisor s) = s := by
  cases s <;> rfl

private theorem factorSetToDivisor_divisorToFactorSet
    (s : DivisorMonoid {p : Associates α // Irreducible p}) :
    factorSetToDivisor (divisorToFactorSet s) = s := by
  cases s <;> rfl

private theorem factorSetToDivisor_injective :
    Function.Injective (factorSetToDivisor (α := α)) :=
  Function.LeftInverse.injective divisorToFactorSet_factorSetToDivisor

private noncomputable def canonicalDivisorHom [Nontrivial α] [UniqueFactorizationMonoid α] :
    α →*₀ DivisorMonoid {p : Associates α // Irreducible p} :=
  { toFun := fun a ↦ factorSetToDivisor (Associates.mk a).factors
    map_one' := by
      rw [Associates.mk_one, Associates.factors_one]
      rfl
    map_mul' := fun a b ↦ by
      rw [← Associates.mk_mul_mk, Associates.factors_mul, factorSetToDivisor_add]
    map_zero' := by
      rw [Associates.mk_zero, Associates.factors_zero]
      rfl }

private theorem canonicalDivisorHom_surjective [Nontrivial α]
    [UniqueFactorizationMonoid α] :
    Function.Surjective (canonicalDivisorHom (α := α)) := by
  intro x
  let s : Associates.FactorSet α := divisorToFactorSet x
  obtain ⟨a, ha⟩ := Associates.mk_surjective s.prod
  refine ⟨a, ?_⟩
  change factorSetToDivisor (Associates.mk a).factors = x
  rw [ha, Associates.prod_factors]
  exact factorSetToDivisor_divisorToFactorSet x

/-- The canonical divisor theory of a nontrivial unique factorization monoid, sending an
element to its multiset of prime factors indexed by irreducible associate classes. -/
noncomputable def UniqueFactorizationMonoid.divisorTheory [Nontrivial α]
    [UniqueFactorizationMonoid α] :
    DivisorTheory α {p : Associates α // Irreducible p} := by
  refine
    { toMonoidWithZeroHom := canonicalDivisorHom
      isDivisorTheory := IsDivisorTheory.of_exists_isGCD ?_ ?_ }
  · refine isDivisorHom_iff.mpr fun ⦃a b⦄ hab ↦ ?_
    apply Associates.dvd_of_mk_le_mk
    rw [← Associates.factors_le]
    obtain ⟨d, hd⟩ := hab
    have hd' : (Associates.mk b).factors =
        (Associates.mk a).factors + divisorToFactorSet d := by
      apply factorSetToDivisor_injective
      rw [factorSetToDivisor_add, factorSetToDivisor_divisorToFactorSet]
      exact hd
    rw [hd']
    exact le_add_of_nonneg_right bot_le
  · intro x hx
    obtain ⟨a, ha⟩ := canonicalDivisorHom_surjective x
    refine ⟨{a}, Finset.singleton_nonempty a, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_singleton.mp hb with rfl
      rw [ha]
    · intro y hy
      rw [← ha]
      exact hy a (Finset.mem_singleton_self a)

/-- On a nonzero element, the canonical divisor theory records its multiset of irreducible
associate factors. -/
theorem UniqueFactorizationMonoid.divisorTheory_apply_of_ne_zero [Nontrivial α]
    [UniqueFactorizationMonoid α] (a : α) (ha : a ≠ 0) :
    UniqueFactorizationMonoid.divisorTheory (α := α) a =
      ((Multiplicative.ofAdd (Associates.factors' a) :
        FreeDivisorMonoid {p : Associates α // Irreducible p}) :
          DivisorMonoid {p : Associates α // Irreducible p}) := by
  simp only [UniqueFactorizationMonoid.divisorTheory, canonicalDivisorHom]
  change
    (match (Associates.mk a).factors with
      | none => (0 : DivisorMonoid {p : Associates α // Irreducible p})
      | some s => ((Multiplicative.ofAdd s :
          FreeDivisorMonoid {p : Associates α // Irreducible p}) :
            DivisorMonoid {p : Associates α // Irreducible p})) = _
  rw [Associates.factors_mk a ha]

/-- The canonical divisor theory of a unique factorization monoid is onto the free divisor
monoid with zero. -/
theorem UniqueFactorizationMonoid.divisorTheory_surjective [Nontrivial α]
    [UniqueFactorizationMonoid α] :
    Function.Surjective
      (UniqueFactorizationMonoid.divisorTheory (α := α) :
        α → DivisorMonoid {p : Associates α // Irreducible p}) := by
  change Function.Surjective (canonicalDivisorHom (α := α))
  exact canonicalDivisorHom_surjective

/-! ### Class-group criteria -/

private theorem divisorClassGroup_subsingleton_of_surjective
    (D : DivisorTheory α P)
    (hsurj : ∀ s : FreeDivisorMonoid P, ∃ a : α, D a = (s : DivisorMonoid P)) :
    Subsingleton D.ClassGroup := by
  let H := principalDivisors D.toMonoidWithZeroHom
  have hgen (p : P) :
      Multiplicative.ofAdd (FreeAbelianGroup.of p) ∈ H := by
    obtain ⟨a, ha⟩ := hsurj (FreeDivisorMonoid.of p)
    simpa only [H, FreeDivisorMonoid.toDivisorGroup_of] using
      (mem_principalDivisors_of_eq ha)
  have hall (z : FreeAbelianGroup P) : Multiplicative.ofAdd z ∈ H := by
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact H.one_mem
    | of p => exact hgen p
    | neg p hp => exact H.inv_mem hp
    | add x y hx hy => exact H.mul_mem hx hy
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := DivisorClassGroup.mk_surjective D.toMonoidWithZeroHom x
  obtain ⟨y, rfl⟩ := DivisorClassGroup.mk_surjective D.toMonoidWithZeroHom y
  have hx : DivisorClassGroup.mk D.toMonoidWithZeroHom x = 1 :=
    (DivisorClassGroup.mk_eq_one_iff _ _).mpr (by simpa using hall x.toAdd)
  have hy : DivisorClassGroup.mk D.toMonoidWithZeroHom y = 1 :=
    (DivisorClassGroup.mk_eq_one_iff _ _).mpr (by simpa using hall y.toAdd)
  exact hx.trans hy.symm

/-- The class group of the canonical divisor theory of a unique factorization monoid is
trivial. -/
theorem UniqueFactorizationMonoid.divisorTheory_classGroup_subsingleton [Nontrivial α]
    [UniqueFactorizationMonoid α] :
    Subsingleton
      (UniqueFactorizationMonoid.divisorTheory (α := α)).ClassGroup := by
  apply divisorClassGroup_subsingleton_of_surjective
    (UniqueFactorizationMonoid.divisorTheory (α := α))
  intro s
  exact UniqueFactorizationMonoid.divisorTheory_surjective
    (s : DivisorMonoid {p : Associates α // Irreducible p})

private theorem dvd_iff_divisorMultiset_le (D : DivisorTheory α P)
    {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ∣ b ↔ D.divisorMultiset a ≤ D.divisorMultiset b := by
  refine ⟨D.divisorMultiset_le_of_dvd hb, fun h ↦ D.isDivisorHom.dvd_of_map_dvd ?_⟩
  rw [← D.coe_divisorMultiset a ha, ← D.coe_divisorMultiset b hb]
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h
  refine ⟨(Multiplicative.ofAdd u : FreeDivisorMonoid P), ?_⟩
  exact congrArg WithZero.coe (congrArg Multiplicative.ofAdd hu)

private theorem divisorMultiset_eq_zero_of_isUnit [Nontrivial α]
    (D : DivisorTheory α P) {a : α} (ha : IsUnit a) : D.divisorMultiset a = 0 := by
  have hle := D.divisorMultiset_le_of_dvd one_ne_zero (isUnit_iff_dvd_one.mp ha)
  rw [D.divisorMultiset_one] at hle
  exact Multiset.le_zero.mp hle

/-- If the class group of an explicit divisor theory is trivial, its source is a unique
factorization monoid. -/
theorem DivisorTheory.uniqueFactorizationMonoid_of_classGroup_subsingleton
    [IsCancelMulZero α] [Nontrivial α] (D : DivisorTheory α P)
    (hC : Subsingleton D.ClassGroup) : UniqueFactorizationMonoid α := by
  classical
  let _ : Subsingleton D.ClassGroup := hC
  let _ : FiniteFactorizationMonoid α := D.finiteFactorizationMonoid
  refine { irreducible_iff_prime := ?_ }
  intro a
  refine ⟨fun haI ↦ ?_, Prime.irreducible⟩
  refine ⟨haI.ne_zero, haI.not_isUnit, fun b c hab ↦ ?_⟩
  by_cases hb : b = 0
  · left
    rw [hb]
    exact dvd_zero a
  by_cases hc : c = 0
  · right
    rw [hc]
    exact dvd_zero a
  have hbc : b * c ≠ 0 := mul_ne_zero hb hc
  have hle : D.divisorMultiset a ≤
      D.divisorMultiset b + D.divisorMultiset c := by
    rw [← D.divisorMultiset_mul hb hc]
    exact D.divisorMultiset_le_of_dvd hbc hab
  -- Split the divisor of `a` into the part supported by `b` and its complement.
  let s := D.divisorMultiset a ∩ D.divisorMultiset b
  let t := D.divisorMultiset a - D.divisorMultiset b
  have hs : s ≤ D.divisorMultiset b := Multiset.inter_le_right
  have ht : t ≤ D.divisorMultiset c :=
    Multiset.sub_le_iff_le_add'.mpr hle
  have hst : D.divisorMultiset a = s + t := by
    dsimp only [s, t]
    rw [Multiset.add_comm, Multiset.sub_add_inter]
  have hclass (r : Multiset P) :
      DivisorClassGroup.mk D.toMonoidWithZeroHom
        (FreeDivisorMonoid.toDivisorGroup P (Multiplicative.ofAdd r)) = 1 :=
    Subsingleton.elim _ _
  -- Triviality of the class group realizes both pieces as divisors of source elements.
  obtain ⟨x, hx⟩ := D.exists_map_eq_of_class_eq_one
    (Multiplicative.ofAdd s) (hclass s)
  obtain ⟨y, hy⟩ := D.exists_map_eq_of_class_eq_one
    (Multiplicative.ofAdd t) (hclass t)
  have hx0 : x ≠ 0 := D.isDivisorHom.map_eq_zero_iff.not.mp <| by
    rw [hx]
    exact WithZero.coe_ne_zero
  have hy0 : y ≠ 0 := D.isDivisorHom.map_eq_zero_iff.not.mp <| by
    rw [hy]
    exact WithZero.coe_ne_zero
  have hxs : D.divisorMultiset x = s := by
    apply Multiplicative.ofAdd.injective
    apply WithZero.coe_injective
    rw [D.coe_divisorMultiset x hx0, hx]
  have hyt : D.divisorMultiset y = t := by
    apply Multiplicative.ofAdd.injective
    apply WithZero.coe_injective
    rw [D.coe_divisorMultiset y hy0, hy]
  have hmapxy : D (x * y) = D a := by
    rw [map_mul, hx, hy, ← D.coe_divisorMultiset a haI.ne_zero]
    exact congrArg WithZero.coe (congrArg Multiplicative.ofAdd hst.symm)
  have hxyI : Irreducible (x * y) :=
    (D.isDivisorHom.associated_of_map_eq hmapxy).symm.irreducible haI
  rcases hxyI.isUnit_or_isUnit rfl with hxunit | hyunit
  · right
    apply (dvd_iff_divisorMultiset_le D haI.ne_zero hc).mpr
    rw [hst, ← hxs, divisorMultiset_eq_zero_of_isUnit D hxunit, zero_add]
    exact ht
  · left
    apply (dvd_iff_divisorMultiset_le D haI.ne_zero hb).mpr
    rw [hst, ← hyt, divisorMultiset_eq_zero_of_isUnit D hyunit, add_zero]
    exact hs
