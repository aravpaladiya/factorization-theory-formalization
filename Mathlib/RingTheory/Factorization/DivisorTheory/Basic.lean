/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero.CancelMulZero
public import Mathlib.Data.Finset.Empty
public import Mathlib.RingTheory.Factorization.DivisorHom

import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.Finset.NAry

/-!
# Divisor theories

This file defines free divisor monoids and divisor theories for commutative monoids with zero.
A divisor theory maps into the free commutative monoid on a type of prime divisors, with an
absorbing zero adjoined. Its density condition says that each prime basis divisor is a greatest
common divisor of finitely many elements of the image.

## Main definitions

* `FreeDivisorMonoid P`: the free commutative monoid on `P`, written multiplicatively.
* `DivisorMonoid P`: `FreeDivisorMonoid P` with an absorbing zero adjoined.
* `IsDivisorTheory φ`: the divisor-theory property for `φ : α →*₀ DivisorMonoid P`.
* `DivisorTheory α P`: an explicit divisor homomorphism bundled with that property.

## Main results

* `IsDivisorTheory.of_exists_isGCD`: the all-divisor greatest-common-divisor condition
  constructs a divisor theory.
* `IsDivisorTheory.exists_dvd`: the image is cofinal for divisibility.
* `IsDivisorTheory.exists_isGCD_of_ne_zero`: every nonzero divisor is a greatest common divisor
  of finitely many image elements.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists FreeAbelianGroup Ring Ideal

universe u v

variable {α : Type u} {P : Type v}

/-- The free commutative monoid on a type `P` of prime divisors, realized as multisets written
multiplicatively. -/
abbrev FreeDivisorMonoid (P : Type u) : Type u := Multiplicative (Multiset P)

/-- The free divisor monoid over `P`, with an absorbing zero adjoined. -/
abbrev DivisorMonoid (P : Type u) : Type u := WithZero (FreeDivisorMonoid P)

namespace FreeDivisorMonoid

/-- The prime basis divisor associated to `p`. -/
def of (p : P) : FreeDivisorMonoid P :=
  Multiplicative.ofAdd {p}

/-- The underlying multiset of a prime basis divisor is the corresponding singleton. -/
@[simp]
theorem toAdd_of (p : P) : (of p).toAdd = ({p} : Multiset P) := by
  simp [of]

@[simp]
theorem of_mul (p : P) (s : Multiset P) :
    of p * Multiplicative.ofAdd s = Multiplicative.ofAdd (p ::ₘ s) := by
  rw [← Multiset.singleton_add]
  rfl

/-- Relabel the prime generators of a free divisor monoid along an equivalence. -/
def mapEquiv {P₁ P₂ : Type*} (e : P₁ ≃ P₂) :
    FreeDivisorMonoid P₁ ≃* FreeDivisorMonoid P₂ := by
  let E : Multiset P₁ ≃+ Multiset P₂ :=
    { toFun := Multiset.map e
      invFun := Multiset.map e.symm
      left_inv := fun s ↦ by simp [Multiset.map_map]
      right_inv := fun s ↦ by simp [Multiset.map_map]
      map_add' := Multiset.map_add e }
  exact AddEquiv.toMultiplicative E

/-- Relabelling a free divisor monoid maps each entry of its underlying multiset. -/
@[simp]
theorem mapEquiv_apply {P₁ P₂ : Type*} (e : P₁ ≃ P₂) (d : FreeDivisorMonoid P₁) :
    (mapEquiv e d).toAdd = d.toAdd.map e := by
  simp [mapEquiv]

@[simp]
theorem mapEquiv_of {P₁ P₂ : Type*} (e : P₁ ≃ P₂) (p : P₁) :
    mapEquiv e (of p) = of (e p) := by
  apply Multiplicative.toAdd.injective
  simp

end FreeDivisorMonoid

section DivisorTheory

variable [CommMonoidWithZero α] {φ : α →*₀ DivisorMonoid P}

/-- A divisor theory for `α` is a divisor homomorphism `φ : α →*₀ DivisorMonoid P` such that
every prime basis divisor is a greatest common divisor of the images of finitely many elements
of `α`. This is the with-zero form of Definition 2.4.1 in
[Geroldinger and Halter-Koch][geroldingerhalterkoch2006]. The
greatest common divisor condition is spelled out with divisibility rather than through
`GCDMonoid`. The finset `s` is required to be nonempty. -/
structure IsDivisorTheory (φ : α →*₀ DivisorMonoid P) : Prop where
  /-- A divisor theory is a divisor homomorphism. -/
  isDivisorHom : IsDivisorHom φ
  /-- Every prime basis divisor is the greatest common divisor of finitely many elements of
  the image of `φ`. -/
  exists_isGCD_of_prime : ∀ p : P, ∃ s : Finset α, s.Nonempty ∧
    (∀ a ∈ s, (FreeDivisorMonoid.of p : DivisorMonoid P) ∣ φ a) ∧
      ∀ y : DivisorMonoid P, (∀ a ∈ s, y ∣ φ a) →
        y ∣ (FreeDivisorMonoid.of p : DivisorMonoid P)

/-- Construct a divisor theory from the stronger condition that every nonzero divisor is a
greatest common divisor of finitely many elements of the image. -/
theorem IsDivisorTheory.of_exists_isGCD (hφ : IsDivisorHom φ)
    (h : ∀ ⦃x : DivisorMonoid P⦄, x ≠ 0 → ∃ s : Finset α, s.Nonempty ∧
      (∀ a ∈ s, x ∣ φ a) ∧
        ∀ y : DivisorMonoid P, (∀ a ∈ s, y ∣ φ a) → y ∣ x) :
    IsDivisorTheory φ where
  isDivisorHom := hφ
  exists_isGCD_of_prime p := h (by simp [FreeDivisorMonoid.of])

/-- The image of a divisor theory is cofinal for divisibility: every divisor divides an
element of the image. -/
theorem IsDivisorTheory.exists_dvd (hφ : IsDivisorTheory φ) (x : DivisorMonoid P) :
    ∃ a : α, x ∣ φ a := by
  induction x using WithZero.recZeroCoe with
  | zero => exact ⟨0, by simp⟩
  | coe d =>
    change ∃ a : α,
      ((Multiplicative.ofAdd d.toAdd : FreeDivisorMonoid P) : DivisorMonoid P) ∣ φ a
    induction d.toAdd using Multiset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | @cons p s ih =>
      obtain ⟨t, ht, hpt, -⟩ := hφ.exists_isGCD_of_prime p
      obtain ⟨a, ha⟩ := ht
      obtain ⟨b, hb⟩ := ih
      refine ⟨a * b, ?_⟩
      rw [map_mul]
      convert mul_dvd_mul (hpt a ha) hb using 1
      rw [← Multiset.singleton_add]
      rfl

section AllDivisorGCD

private theorem divisorMonoid_coe_dvd_coe_iff (s t : Multiset P) :
    ((Multiplicative.ofAdd s : FreeDivisorMonoid P) : DivisorMonoid P) ∣
        ((Multiplicative.ofAdd t : FreeDivisorMonoid P) : DivisorMonoid P) ↔
      s ≤ t := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    induction z using WithZero.recZeroCoe with
    | zero => simp at hz
    | coe z =>
        apply Multiset.le_iff_exists_add.mpr
        refine ⟨z.toAdd, ?_⟩
        simpa using congrArg Multiplicative.toAdd (WithZero.coe_injective hz)
  · intro h
    obtain ⟨z, rfl⟩ := Multiset.le_iff_exists_add.mp h
    refine ⟨((Multiplicative.ofAdd z : FreeDivisorMonoid P) : DivisorMonoid P), ?_⟩
    rfl

private theorem restrict_isGCD_to_ne_zero
    {φ : α →*₀ DivisorMonoid P} {x : DivisorMonoid P} (hx : x ≠ 0)
    {s : Finset α} (hxdvd : ∀ a ∈ s, x ∣ φ a)
    (hgreat : ∀ y : DivisorMonoid P, (∀ a ∈ s, y ∣ φ a) → y ∣ x) :
    ∃ t : Finset α, t.Nonempty ∧ (∀ a ∈ t, φ a ≠ 0) ∧
      (∀ a ∈ t, x ∣ φ a) ∧
        ∀ y : DivisorMonoid P, (∀ a ∈ t, y ∣ φ a) → y ∣ x := by
  classical
  -- Zero images impose no restriction on common divisors, so discard them before taking
  -- multiplicative representatives.
  let t := s.filter fun a ↦ φ a ≠ 0
  have ht : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hzero : ∀ a ∈ s, φ a = 0 := by
      intro a ha
      by_contra ha0
      have : a ∈ t := Finset.mem_filter.mpr ⟨ha, ha0⟩
      rw [h] at this
      simp at this
    have hzero_dvd : (0 : DivisorMonoid P) ∣ x :=
      hgreat 0 fun a ha ↦ by simp [hzero a ha]
    exact hx (zero_dvd_iff.mp hzero_dvd)
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a ha
    exact hxdvd a (Finset.mem_filter.mp ha).1
  · intro y hy
    apply hgreat y
    intro a ha
    by_cases ha0 : φ a = 0
    · simp [ha0]
    · exact hy a (Finset.mem_filter.mpr ⟨ha, ha0⟩)

private theorem exists_count_eq_of_isGCD [DecidableEq P]
    {φ : α →*₀ DivisorMonoid P} {x : Multiset P} {s : Finset α}
    (hnz : ∀ a ∈ s, φ a ≠ 0)
    (hxdvd : ∀ a ∈ s,
      ((Multiplicative.ofAdd x : FreeDivisorMonoid P) : DivisorMonoid P) ∣ φ a)
    (hgreat : ∀ y : DivisorMonoid P, (∀ a ∈ s, y ∣ φ a) →
      y ∣ ((Multiplicative.ofAdd x : FreeDivisorMonoid P) : DivisorMonoid P))
    (q : P) :
    ∃ a, ∃ ha : a ∈ s, ((φ a).unzero (hnz a ha)).toAdd.count q = x.count q := by
  classical
  -- If no member realizes the coordinatewise minimum at `q`, adjoining one copy of `q`
  -- would produce a strictly larger common divisor.
  by_contra h
  push Not at h
  have hstrict (a : α) (ha : a ∈ s) : x.count q <
      ((φ a).unzero (hnz a ha)).toAdd.count q := by
    have hle : x.count q ≤
        ((φ a).unzero (hnz a ha)).toAdd.count q := by
      apply Multiset.le_iff_count.mp
        ((divisorMonoid_coe_dvd_coe_iff x ((φ a).unzero (hnz a ha)).toAdd).mp ?_)
      simpa only [ofAdd_toAdd, WithZero.coe_unzero] using hxdvd a ha
    exact lt_of_le_of_ne hle (h a ha).symm
  let y : DivisorMonoid P :=
    ((Multiplicative.ofAdd (q ::ₘ x) : FreeDivisorMonoid P) : DivisorMonoid P)
  have hydvd : ∀ a ∈ s, y ∣ φ a := by
    intro a ha
    rw [← WithZero.coe_unzero (hnz a ha)]
    change
      ((Multiplicative.ofAdd (q ::ₘ x) : FreeDivisorMonoid P) : DivisorMonoid P) ∣
        ((Multiplicative.ofAdd ((φ a).unzero (hnz a ha)).toAdd : FreeDivisorMonoid P) :
          DivisorMonoid P)
    apply (divisorMonoid_coe_dvd_coe_iff (q ::ₘ x) _).mpr
    apply Multiset.le_iff_count.mpr
    intro r
    by_cases hr : r = q
    · subst r
      simpa using Nat.succ_le_iff.mpr (hstrict a ha)
    · simpa [Multiset.count_cons, hr] using
        (Multiset.le_iff_count.mp
          ((divisorMonoid_coe_dvd_coe_iff x _).mp <| by
            simpa only [ofAdd_toAdd, WithZero.coe_unzero] using hxdvd a ha) r)
  have hyx := hgreat y hydvd
  have hle := (divisorMonoid_coe_dvd_coe_iff (q ::ₘ x) x).mp hyx
  have := Multiset.le_iff_count.mp hle q
  exact Nat.not_succ_le_self _ (by simpa using this)

private theorem exists_nonzero_isGCD_of_multiset
    {φ : α →*₀ DivisorMonoid P} (hφ : IsDivisorTheory φ) (d : Multiset P) :
    ∃ s : Finset α, s.Nonempty ∧ (∀ a ∈ s, φ a ≠ 0) ∧
      (∀ a ∈ s,
        ((Multiplicative.ofAdd d : FreeDivisorMonoid P) : DivisorMonoid P) ∣ φ a) ∧
      ∀ y : DivisorMonoid P, (∀ a ∈ s, y ∣ φ a) →
        y ∣ ((Multiplicative.ofAdd d : FreeDivisorMonoid P) : DivisorMonoid P) := by
  classical
  induction d using Multiset.induction_on with
  | empty =>
      refine ⟨{1}, by simp, ?_, ?_, ?_⟩
      · intro a ha
        simp only [Finset.mem_singleton] at ha
        subst a
        simp
      · intro a ha
        simp only [Finset.mem_singleton] at ha
        subst a
        simp
      · intro y hy
        simpa using hy 1 (by simp)
  | @cons p d ih =>
      -- First choose nonzero gcd families for the basis divisor `p` and for the tail `d`.
      obtain ⟨s, hs, hpdvd, hpgreat⟩ := hφ.exists_isGCD_of_prime p
      obtain ⟨s', hs', hsnz, hpdvd', hpgreat'⟩ :=
        restrict_isGCD_to_ne_zero (by simp [FreeDivisorMonoid.of]) hpdvd hpgreat
      obtain ⟨t, ht, htnz, hddvd, hdgreat⟩ := ih
      -- Their Cartesian-product family realizes the product of the two gcds.
      let u := Finset.image₂ (· * ·) s' t
      refine ⟨u, hs'.image₂ ht, ?_, ?_, ?_⟩
      · intro c hc
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hc
        rw [map_mul]
        exact mul_ne_zero (hsnz a ha) (htnz b hb)
      · intro c hc
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hc
        rw [map_mul]
        convert mul_dvd_mul (hpdvd' a ha) (hddvd b hb) using 1
        exact congrArg (fun z : FreeDivisorMonoid P ↦ (z : DivisorMonoid P))
          (FreeDivisorMonoid.of_mul p d).symm
      · intro y hy
        obtain ⟨a₀, ha₀⟩ := hs'
        obtain ⟨b₀, hb₀⟩ := ht
        have hab0 : φ (a₀ * b₀) ≠ 0 := by
          rw [map_mul]
          exact mul_ne_zero (hsnz a₀ ha₀) (htnz b₀ hb₀)
        have hy0 : y ≠ 0 :=
          ne_zero_of_dvd_ne_zero hab0
            (hy (a₀ * b₀) (Finset.mem_image₂_of_mem ha₀ hb₀))
        rw [← WithZero.coe_unzero hy0]
        change
          ((Multiplicative.ofAdd ((y.unzero hy0).toAdd) : FreeDivisorMonoid P) :
              DivisorMonoid P) ∣
            ((Multiplicative.ofAdd (p ::ₘ d) : FreeDivisorMonoid P) : DivisorMonoid P)
        apply (divisorMonoid_coe_dvd_coe_iff _ _).mpr
        -- For each coordinate, choose witnesses attaining both minima and use their product.
        apply Multiset.le_iff_count.mpr
        intro q
        obtain ⟨a, ha, haq⟩ := exists_count_eq_of_isGCD hsnz
          (fun a ha ↦ by simpa [FreeDivisorMonoid.of] using hpdvd' a ha)
          (fun z hz ↦ by
            simpa [FreeDivisorMonoid.of] using hpgreat' z hz) q
        obtain ⟨b, hb, hbq⟩ := exists_count_eq_of_isGCD htnz hddvd hdgreat q
        have hyab := hy (a * b) (Finset.mem_image₂_of_mem ha hb)
        rw [map_mul, ← WithZero.coe_unzero hy0, ← WithZero.coe_unzero (hsnz a ha),
          ← WithZero.coe_unzero (htnz b hb)] at hyab
        change
          ((Multiplicative.ofAdd ((y.unzero hy0).toAdd) : FreeDivisorMonoid P) :
              DivisorMonoid P) ∣
            ((Multiplicative.ofAdd
                (((φ a).unzero (hsnz a ha)).toAdd +
                  ((φ b).unzero (htnz b hb)).toAdd) : FreeDivisorMonoid P) :
              DivisorMonoid P) at hyab
        have hcount := Multiset.le_iff_count.mp
          ((divisorMonoid_coe_dvd_coe_iff _ _).mp hyab) q
        simpa [← Multiset.singleton_add, Multiset.count_add, haq, hbq] using hcount

/-- Every nonzero divisor is a greatest common divisor of finitely many elements of the image
of a divisor theory. -/
theorem IsDivisorTheory.exists_isGCD_of_ne_zero (hφ : IsDivisorTheory φ)
    {x : DivisorMonoid P} (hx : x ≠ 0) :
    ∃ s : Finset α, s.Nonempty ∧ (∀ a ∈ s, x ∣ φ a) ∧
      ∀ y : DivisorMonoid P, (∀ a ∈ s, y ∣ φ a) → y ∣ x := by
  induction x using WithZero.recZeroCoe with
  | zero => exact (hx rfl).elim
  | coe d =>
      obtain ⟨s, hs, -, hsdvd, hsgreat⟩ := exists_nonzero_isGCD_of_multiset hφ d.toAdd
      exact ⟨s, hs, hsdvd, hsgreat⟩

end AllDivisorGCD

/-- A bundled divisor theory for `α` over a type `P` of prime divisors. The bundle is
explicit data, not a typeclass: a monoid may admit many useful presentations by divisor
theories. -/
structure DivisorTheory (α : Type u) [CommMonoidWithZero α] (P : Type v)
    extends α →*₀ DivisorMonoid P where
  /-- The characteristic divisor-theory property. -/
  isDivisorTheory : IsDivisorTheory toMonoidWithZeroHom

namespace DivisorTheory

variable (D : DivisorTheory α P)

theorem toMonoidWithZeroHom_injective :
    Function.Injective
      (toMonoidWithZeroHom : DivisorTheory α P → α →*₀ DivisorMonoid P) := by
  rintro ⟨D₁, hD₁⟩ ⟨D₂, hD₂⟩ h
  dsimp only at h
  cases h
  rfl

instance : FunLike (DivisorTheory α P) α (DivisorMonoid P) where
  coe D := D.toMonoidWithZeroHom
  coe_injective := DFunLike.coe_injective.comp toMonoidWithZeroHom_injective

instance : MonoidWithZeroHomClass (DivisorTheory α P) α (DivisorMonoid P) where
  map_one D := D.toMonoidWithZeroHom.map_one
  map_mul D := D.toMonoidWithZeroHom.map_mul
  map_zero D := D.toMonoidWithZeroHom.map_zero

@[simp]
theorem toMonoidWithZeroHom_apply (a : α) : D.toMonoidWithZeroHom a = D a := rfl

@[ext]
theorem ext {D₁ D₂ : DivisorTheory α P} (h : ∀ a, D₁ a = D₂ a) : D₁ = D₂ :=
  DFunLike.ext _ _ h

theorem isDivisorHom : IsDivisorHom D :=
  isDivisorHom_iff.mpr fun ⦃_ _⦄ h ↦
    D.isDivisorTheory.isDivisorHom.dvd_of_map_dvd h

end DivisorTheory

end DivisorTheory
