/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated.Hom
public import Mathlib.RingTheory.Factorization.Basic

/-!
# Transfer homomorphisms

A transfer homomorphism is a monoid homomorphism which is surjective up to associates, reflects
units, and lifts factorizations in the target to the source. This file defines transfer
homomorphisms and proves that they preserve sets of factorization lengths. The definition follows
Section 3.2 of [Geroldinger and Halter-Koch][geroldingerhalterkoch2006].

## Main definitions

* `IsTransferHom θ`: the transfer-homomorphism predicate.
* `IsTransferHom.factorizationMap`: the induced additive homomorphism on formal factorizations.

## Main results

* `IsTransferHom.irreducible_iff`: transfer homomorphisms preserve and reflect atoms.
* `IsTransferHom.exists_multiset_rel`: the iterated factorization-lifting property.
* `IsTransferHom.exists_factorizationMap_eq`: the induced map is surjective on factorization
  fibers.
* `IsTransferHom.factorizationLengths_eq`: transfer homomorphisms preserve sets of lengths.

The usual transfer axioms are stated up to `Associated`. Since this file works with monoids with
zero, `IsTransferHom` also requires reflection of zero so that the nonzero source and target
elements correspond. It is an explicit structure rather than a typeclass because the map and its
transfer proof are noncanonical data.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

variable {α β γ F : Type*}

section CommMonoidWithZero

variable [CommMonoidWithZero α] [CommMonoidWithZero β] [CommMonoidWithZero γ]
variable [FunLike F α β] [MonoidWithZeroHomClass F α β]
variable {θ : F} {a : α} {b : β}

/-- A *transfer homomorphism* is a homomorphism represented by a
`MonoidWithZeroHomClass` between commutative monoids with zero which is surjective up to
associates, reflects units and zero, and lifts factorizations of `θ a` to factorizations of
`a`. These are conditions (T1) and (T2) of Definition 3.2.1 in
[Geroldinger and Halter-Koch][geroldingerhalterkoch2006], with reflection of zero added for
monoids with zero. -/
@[mk_iff] structure IsTransferHom (θ : F) : Prop where
  /-- (T1a) `θ` is surjective up to units: every element of `β` is associated to a value
  of `θ`. -/
  exists_associated_map (b : β) : ∃ a, Associated (θ a) b
  /-- (T1b) `θ` reflects units. Preservation of units is automatic for a monoid
  homomorphism, so this is exactly the existing `IsLocalHom` condition. -/
  isLocalHom : IsLocalHom θ
  /-- (T0) `θ` reflects zero. This condition has no analogue for zero-free monoids and
  makes the `a ≠ 0` hypotheses in source and target correspond. -/
  eq_zero_of_map_eq_zero ⦃a : α⦄ : θ a = 0 → a = 0
  /-- (T2) Every splitting of `θ a` in `β` lifts to a splitting of `a` in `α`, up to
  associates. -/
  exists_mul_eq_of_map_eq_mul ⦃a : α⦄ ⦃b₁ b₂ : β⦄ : θ a = b₁ * b₂ →
    ∃ a₁ a₂, a = a₁ * a₂ ∧ Associated (θ a₁) b₁ ∧ Associated (θ a₂) b₂

namespace IsTransferHom

/-! ### Elementary consequences of the axioms -/

theorem map_eq_zero_iff (hθ : IsTransferHom θ) : θ a = 0 ↔ a = 0 :=
  ⟨fun h ↦ hθ.eq_zero_of_map_eq_zero h, fun h ↦ h ▸ map_zero θ⟩

theorem map_ne_zero (hθ : IsTransferHom θ) (ha : a ≠ 0) : θ a ≠ 0 :=
  hθ.map_eq_zero_iff.not.mpr ha

/-- A transfer homomorphism reflects units; the forward implication is the
`IsLocalHom` field and the reverse implication holds for every monoid homomorphism. -/
theorem isUnit_map_iff (hθ : IsTransferHom θ) : IsUnit (θ a) ↔ IsUnit a := by
  let _ := hθ.isLocalHom
  exact _root_.isUnit_map_iff θ a

/-- A transfer homomorphism preserves nonunits, so the elements to which the arithmetic
applies correspond on the two sides. -/
theorem not_isUnit_map (hθ : IsTransferHom θ) (ha : ¬IsUnit a) : ¬IsUnit (θ a) :=
  hθ.isUnit_map_iff.not.mpr ha

/-- The identity homomorphism is a transfer homomorphism. -/
protected theorem id : IsTransferHom (MonoidWithZeroHom.id α) where
  exists_associated_map b := ⟨b, .rfl⟩
  isLocalHom := ⟨fun _ h ↦ h⟩
  eq_zero_of_map_eq_zero _ h := h
  exists_mul_eq_of_map_eq_mul _ _ _ h := ⟨_, _, h, .rfl, .rfl⟩

/-- Transfer homomorphisms are closed under composition. -/
protected theorem comp {F' : Type*} [FunLike F' β γ] [MonoidWithZeroHomClass F' β γ]
    {φ : F'} (hφ : IsTransferHom φ) (hθ : IsTransferHom θ) :
    IsTransferHom
      ((MonoidWithZeroHom.ofClass φ).comp (MonoidWithZeroHom.ofClass θ)) := by
  refine
    { exists_associated_map := fun c ↦ ?_
      isLocalHom := ?_
      eq_zero_of_map_eq_zero := ?_
      exists_mul_eq_of_map_eq_mul := ?_ }
  · obtain ⟨b, hbc⟩ := hφ.exists_associated_map c
    obtain ⟨a, hab⟩ := hθ.exists_associated_map b
    refine ⟨a, ?_⟩
    change Associated (φ (θ a)) c
    exact (hab.map φ).trans hbc
  · refine ⟨fun a ha ↦ ?_⟩
    exact hθ.isUnit_map_iff.mp (hφ.isUnit_map_iff.mp ha)
  · intro a ha
    exact hθ.eq_zero_of_map_eq_zero (hφ.eq_zero_of_map_eq_zero ha)
  · intro a c₁ c₂ h
    change φ (θ a) = c₁ * c₂ at h
    obtain ⟨b₁, b₂, hb, hb₁, hb₂⟩ := hφ.exists_mul_eq_of_map_eq_mul h
    obtain ⟨a₁, a₂, ha, ha₁, ha₂⟩ := hθ.exists_mul_eq_of_map_eq_mul hb
    refine ⟨a₁, a₂, ha, ?_, ?_⟩
    · change Associated (φ (θ a₁)) c₁
      exact (ha₁.map φ).trans hb₁
    · change Associated (φ (θ a₂)) c₂
      exact (ha₂.map φ).trans hb₂

/-! ### Atoms -/

/-- A transfer homomorphism reflects atoms: if `θ a` is associated to an atom of `β` then
`a` is an atom of `α`. -/
theorem irreducible_of_associated_map (hθ : IsTransferHom θ) (hab : Associated (θ a) b)
    (hb : Irreducible b) : Irreducible a := by
  let _ := hθ.isLocalHom
  exact (hab.symm.irreducible hb).of_map

/-- A transfer homomorphism maps atoms to atoms and reflects them: this is the reason sets of
lengths are preserved. -/
theorem irreducible_iff (hθ : IsTransferHom θ) : Irreducible (θ a) ↔ Irreducible a := by
  refine ⟨fun h ↦ hθ.irreducible_of_associated_map .rfl h, fun ha ↦ ?_⟩
  refine ⟨hθ.not_isUnit_map ha.not_isUnit, fun b₁ b₂ hmul ↦ ?_⟩
  obtain ⟨a₁, a₂, hprod, h₁, h₂⟩ := hθ.exists_mul_eq_of_map_eq_mul hmul
  exact (ha.isUnit_or_isUnit hprod).imp
    (fun hu ↦ h₁.isUnit (IsUnit.map θ hu))
    (fun hu ↦ h₂.isUnit (IsUnit.map θ hu))

/-! ### The induced map on formal factorizations -/

theorem irreducible_associates_map_iff (hθ : IsTransferHom θ) {p : Associates α} :
    Irreducible (Associates.map θ p) ↔ Irreducible p := by
  refine Quotient.inductionOn p ?_
  intro p
  simpa using hθ.irreducible_iff (a := p)

/-- The atom map induced by a transfer homomorphism. -/
def atomMap (hθ : IsTransferHom θ) :
    {p : Associates α // Irreducible p} → {p : Associates β // Irreducible p} :=
  fun p ↦ ⟨Associates.map θ p, hθ.irreducible_associates_map_iff.mpr p.property⟩

@[simp]
theorem coe_atomMap (hθ : IsTransferHom θ)
    (p : {p : Associates α // Irreducible p}) :
    (hθ.atomMap p : Associates β) = Associates.map θ p := by
  rfl

/-- Map a formal factorization termwise along a transfer homomorphism. -/
def factorizationMap (hθ : IsTransferHom θ) :
    Associates.Factorization α →+ Associates.Factorization β :=
  Multiset.mapAddMonoidHom hθ.atomMap

@[simp]
theorem factorizationMap_apply (hθ : IsTransferHom θ) (f : Associates.Factorization α) :
    hθ.factorizationMap f = f.map hθ.atomMap := by
  rfl

theorem card_factorizationMap (hθ : IsTransferHom θ) (f : Associates.Factorization α) :
    (hθ.factorizationMap f).card = f.card := by
  simp

theorem prod_factorizationMap (hθ : IsTransferHom θ) (f : Associates.Factorization α) :
    (hθ.factorizationMap f).prod = Associates.map θ f.prod := by
  simp only [Associates.Factorization.prod_def, hθ.factorizationMap_apply,
    Multiset.map_map, Function.comp_apply, hθ.coe_atomMap, map_multiset_prod]

/-- The induced additive homomorphism sends a factorization of `a` to a factorization of
`θ a`. -/
theorem factorizationMap_mem (hθ : IsTransferHom θ) {f : Associates.Factorization α}
    (hf : f ∈ factorizations a) : hθ.factorizationMap f ∈ factorizations (θ a) := by
  rw [mem_factorizations, prod_factorizationMap, mem_factorizations.mp hf, Associates.map_mk]

/-! ### Lifting factorizations -/

/-- The iterated form of the lifting condition (T2): a factorization of `θ a` in `β` lifts
to a factorization of `a` in `α` of the same length, termwise associated to the given one.
The conclusion uses `Associated` on both the product and the terms because the lifted
factors are only determined up to units. -/
theorem exists_multiset_rel (hθ : IsTransferHom θ) {g : Multiset β}
    (h : Associated (θ a) g.prod) :
    ∃ f : Multiset α, Associated a f.prod ∧
      Multiset.Rel (fun x y ↦ Associated (θ x) y) f g := by
  induction g using Multiset.induction_on generalizing a with
  | empty =>
      have hmapUnit : IsUnit (θ a) := by
        rw [← associated_one_iff_isUnit]
        simpa using h
      have haUnit : IsUnit a := hθ.isUnit_map_iff.mp hmapUnit
      refine ⟨0, ?_, Multiset.Rel.zero⟩
      rw [Multiset.prod_zero, associated_one_iff_isUnit]
      exact haUnit
  | @cons b g ih =>
      obtain ⟨u, hu⟩ := h
      have hsplit : θ a = (b * (↑(u⁻¹) : β)) * g.prod := by
        calc
          θ a = (θ a * (u : β)) * (↑(u⁻¹) : β) := by simp [mul_assoc]
          _ = (b * g.prod) * (↑(u⁻¹) : β) := by rw [hu, Multiset.prod_cons]
          _ = (b * (↑(u⁻¹) : β)) * g.prod := by ac_rfl
      obtain ⟨a₁, a₂, ha, h₁, h₂⟩ := hθ.exists_mul_eq_of_map_eq_mul hsplit
      obtain ⟨f, hf, hrel⟩ := ih h₂
      refine ⟨a₁ ::ₘ f, ?_, Multiset.Rel.cons ?_ hrel⟩
      · rw [Multiset.prod_cons]
        exact (Associated.of_eq ha).trans (hf.mul_left a₁)
      · exact h₁.trans <| associated_mul_unit_left b (↑(u⁻¹) : β) (Units.isUnit u⁻¹)

/-- Every formal factorization in the target fiber has a preimage in the source fiber under
the termwise additive homomorphism on atom classes. -/
theorem exists_factorizationMap_eq (hθ : IsTransferHom θ)
    {q : Associates.Factorization β} (hq : q ∈ factorizations (θ a)) :
    ∃ p ∈ factorizations a, hθ.factorizationMap p = q := by
  obtain ⟨g, hg, hprod, hgbundle⟩ := exists_multiset_of_mem_factorizations hq
  obtain ⟨f, hfprod, hrel⟩ := hθ.exists_multiset_rel hprod.symm
  have hf : ∀ c ∈ f, Irreducible c := by
    intro c hc
    obtain ⟨d, hd, hcd⟩ := Multiset.exists_mem_of_rel_of_mem hrel hc
    exact hθ.irreducible_of_associated_map hcd (hg d hd)
  refine ⟨Associates.Factorization.ofMultiset f hf,
    ofMultiset_mem_factorizations hf hfprod.symm, ?_⟩
  have hrelmk : Multiset.Rel
      (fun x y ↦ Associates.mk (θ x) = Associates.mk y) f g :=
    hrel.mono fun _ _ _ _ hxy ↦ Associates.mk_eq_mk_iff_associated.mpr hxy
  -- Replace termwise association by equality after passing to associate classes.
  have hmapped : f.map (fun x ↦ Associates.mk (θ x)) = g.map Associates.mk := by
    rw [← Multiset.rel_eq]
    exact Multiset.rel_map.mpr hrelmk
  have hleft :
      (Associates.Factorization.ofMultiset f hf).map
          (fun p : {p : Associates α // Irreducible p} ↦ Associates.map θ p.1) =
        f.map (fun x ↦ Associates.mk (θ x)) := by
    calc
      _ = ((Associates.Factorization.ofMultiset f hf).map Subtype.val).map
          (Associates.map θ) := by
            simp only [Multiset.map_map, Function.comp_apply]
      _ = (f.map Associates.mk).map (Associates.map θ) := by
        rw [Associates.Factorization.map_coe_ofMultiset]
      _ = _ := by simp [Multiset.map_map]
  rw [← hgbundle, ← Multiset.map_eq_map Subtype.coe_injective]
  rw [Associates.Factorization.map_coe_ofMultiset]
  have hfun :
      ((Subtype.val : {p : Associates β // Irreducible p} → Associates β) ∘ hθ.atomMap) =
        (fun p : {p : Associates α // Irreducible p} ↦ Associates.map θ p.1) := by
    funext p
    exact hθ.coe_atomMap p
  rw [factorizationMap_apply, Multiset.map_map, hfun]
  exact hleft.trans hmapped

/-- The forward direction: a factorization of `a` pushes forward to a factorization of
`θ a` of the same length, since `θ` maps atoms to atoms. -/
theorem factorizationLengths_subset (hθ : IsTransferHom θ) (a : α) :
    factorizationLengths a ⊆ factorizationLengths (θ a) := by
  intro n hn
  obtain ⟨f, hf, rfl⟩ := mem_factorizationLengths.mp hn
  simpa using card_mem_factorizationLengths (hθ.factorizationMap_mem hf)

/-- A transfer homomorphism preserves the set of factorization lengths of every element. -/
theorem factorizationLengths_eq (hθ : IsTransferHom θ) (a : α) :
    factorizationLengths (θ a) = factorizationLengths a := by
  apply Set.Subset.antisymm
  · intro n hn
    obtain ⟨q, hq, rfl⟩ := mem_factorizationLengths.mp hn
    obtain ⟨p, hp, hpq⟩ := hθ.exists_factorizationMap_eq hq
    rw [← hpq, card_factorizationMap]
    exact card_mem_factorizationLengths hp
  · exact hθ.factorizationLengths_subset a

end IsTransferHom

end CommMonoidWithZero
