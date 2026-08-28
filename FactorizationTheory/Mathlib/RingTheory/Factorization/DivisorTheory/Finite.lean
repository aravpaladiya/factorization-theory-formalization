/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import FactorizationTheory.Mathlib.RingTheory.Factorization.DivisorTheory.Basic
public import FactorizationTheory.Mathlib.RingTheory.Factorization.Monoid

import Mathlib.Data.ENat.Basic
import Mathlib.Data.Multiset.Interval

/-!
# Finite factorization from a divisor theory

This file proves that a commutative monoid with zero admitting an explicit divisor theory is a
finite factorization monoid. The proof controls each irreducible factor by its finite divisor
multiset and bounds factorization length by the divisor multiset of the element.

## Main result

* `DivisorTheory.finiteFactorizationMonoid`: an explicit divisor theory gives finite
  factorization.
-/

public section

assert_not_exists FreeAbelianGroup Field Ideal

universe u v

variable {α : Type u} {P : Type v} [CommMonoidWithZero α]

namespace DivisorTheory

private theorem divisorMultiset_ne_zero_of_not_isUnit (D : DivisorTheory α P)
    {a : α} (ha : a ≠ 0) (hau : ¬IsUnit a) : D.divisorMultiset a ≠ 0 := by
  intro h
  apply hau
  apply D.isDivisorHom.isUnit_map_iff.mp
  have hDa : D a = 1 := by
    rw [← D.coe_divisorMultiset a ha, h]
    rfl
  rw [hDa]
  exact isUnit_one

private theorem associated_of_divisorMultiset_eq (D : DivisorTheory α P)
    {a b : α} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : D.divisorMultiset a = D.divisorMultiset b) : Associated a b := by
  apply D.isDivisorHom.associated_of_map_eq
  rw [← D.coe_divisorMultiset a ha, ← D.coe_divisorMultiset b hb, hab]

private theorem wfDvdMonoid_of_divisorTheory (D : DivisorTheory α P) :
    WfDvdMonoid α :=
  ⟨by
    refine RelHomClass.wellFounded
      (RelHom.mk ?_ ?_ :
        (DvdNotUnit : α → α → Prop) →r ((· < ·) : ℕ∞ → ℕ∞ → Prop))
        wellFounded_lt
    · intro a
      by_cases ha : a = 0
      · exact ⊤
      exact ((D.divisorMultiset a).card : ℕ∞)
    rintro a b ⟨ha, ⟨c, hcu, hb_eq⟩⟩
    rw [dite_eq_right ha]
    by_cases hb : b = 0
    · simp [hb, lt_top_iff_ne_top]
    · rw [dite_eq_right hb, ENat.natCast_lt_natCast]
      have hc : c ≠ 0 := by
        intro hc
        subst c
        exact hb (by simpa only [mul_zero] using hb_eq)
      calc
        (D.divisorMultiset a).card <
            (D.divisorMultiset a).card + (D.divisorMultiset c).card :=
          lt_add_of_pos_right _
            (Multiset.card_pos.mpr
              (divisorMultiset_ne_zero_of_not_isUnit D hc hcu))
        _ = (D.divisorMultiset (a * c)).card := by
          rw [D.divisorMultiset_mul ha hc, Multiset.card_add]
        _ = (D.divisorMultiset b).card := by
          subst b
          rfl⟩

private theorem divisorMultiset_prod (D : DivisorTheory α P) (f : Multiset α)
    (hf : f.prod ≠ 0) :
    D.divisorMultiset f.prod = (f.map D.divisorMultiset).sum := by
  induction f using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero, Multiset.map_zero, Multiset.sum_zero,
      D.divisorMultiset_one]
  | @cons a f ih =>
    have haf : a * f.prod ≠ 0 := by
      simpa only [Multiset.prod_cons] using hf
    have ha : a ≠ 0 := left_ne_zero_of_mul haf
    have hfprod : f.prod ≠ 0 := right_ne_zero_of_mul haf
    rw [Multiset.prod_cons, D.divisorMultiset_mul ha hfprod,
      Multiset.map_cons, Multiset.sum_cons, ih hfprod]

private theorem card_le_card_sum_divisorMultiset (D : DivisorTheory α P)
    (g : Multiset α) (hgI : ∀ b ∈ g, Irreducible b) :
    g.card ≤ ((g.map D.divisorMultiset).sum).card := by
  induction g using Multiset.induction_on with
  | empty => simp
  | @cons b g ih =>
    have hbI : Irreducible b := hgI b (Multiset.mem_cons_self b g)
    have htail : ∀ c ∈ g, Irreducible c := fun c hc ↦
      hgI c (Multiset.mem_cons_of_mem hc)
    have hbcard : 0 < (D.divisorMultiset b).card :=
      Multiset.card_pos.mpr
        (divisorMultiset_ne_zero_of_not_isUnit D hbI.ne_zero hbI.not_isUnit)
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.card_add]
    have ihtail := ih htail
    omega

private theorem factorization_card_le (D : DivisorTheory α P) {a : α} (ha : a ≠ 0)
    {f : Associates.Factorization α} (hf : f ∈ factorizations a) :
    f.card ≤ (D.divisorMultiset a).card := by
  obtain ⟨g, hgI, hgprod, hgf⟩ := exists_multiset_of_mem_factorizations hf
  have hgprod0 : g.prod ≠ 0 := hgprod.ne_zero_iff.mpr ha
  have hle := card_le_card_sum_divisorMultiset D g hgI
  have hprodImage : D.divisorMultiset g.prod = D.divisorMultiset a :=
    le_antisymm
      (D.divisorMultiset_le_of_dvd ha hgprod.dvd)
      (D.divisorMultiset_le_of_dvd hgprod0 hgprod.symm.dvd)
  calc
    f.card = g.card := by rw [← hgf, Associates.Factorization.card_ofMultiset]
    _ ≤ ((g.map D.divisorMultiset).sum).card := hle
    _ = (D.divisorMultiset g.prod).card :=
      congrArg Multiset.card (divisorMultiset_prod D g hgprod0).symm
    _ = (D.divisorMultiset a).card := congrArg Multiset.card hprodImage

private theorem atomRep_ne_zero
    (p : {p : Associates α // Irreducible p}) : Quot.out p.1 ≠ 0 := by
  intro hp
  apply p.2.ne_zero
  rw [← Associates.quot_out p.1, hp, Associates.mk_zero]

private noncomputable def atomDivisor (D : DivisorTheory α P)
    (p : {p : Associates α // Irreducible p}) : Multiset P :=
  D.divisorMultiset (Quot.out p.1)

private theorem atomDivisor_injective (D : DivisorTheory α P) :
    Function.Injective (atomDivisor D) := by
  intro p q hpq
  apply Subtype.ext
  rw [← Associates.quot_out p.1, ← Associates.quot_out q.1]
  apply Associates.mk_eq_mk_iff_associated.mpr
  exact associated_of_divisorMultiset_eq D (atomRep_ne_zero p) (atomRep_ne_zero q) hpq

private theorem atomDivisor_le_of_mem_factorization (D : DivisorTheory α P)
    {a : α} (ha : a ≠ 0) {p : {p : Associates α // Irreducible p}}
    {f : Associates.Factorization α} (hf : f ∈ factorizations a) (hp : p ∈ f) :
    atomDivisor D p ≤ D.divisorMultiset a := by
  apply D.divisorMultiset_le_of_dvd ha
  rw [← Associates.mk_dvd_mk, Associates.quot_out]
  rw [← mem_factorizations.mp hf]
  exact Associates.Factorization.dvd_prod hp

/-- A monoid admitting an explicit divisor theory is a finite factorization monoid: every
factor in a factorization of `a` contributes a nonempty divisor of `D.divisorMultiset a`,
so both the possible factors and their multiplicities are bounded. This is the
with-zero form of Theorem 2.4.2 in Geroldinger and Halter-Koch. -/
theorem finiteFactorizationMonoid (D : DivisorTheory α P) :
    FiniteFactorizationMonoid α := by
  classical
  let _ : WfDvdMonoid α := wfDvdMonoid_of_divisorTheory D
  refine
    { toAtomicMonoid := inferInstance
      finite_factorizations := fun a ha ↦ ?_ }
  let A : Set {p : Associates α // Irreducible p} :=
    atomDivisor D ⁻¹' ↑(Finset.Iic (D.divisorMultiset a))
  have hA : A.Finite :=
    Set.Finite.preimage (atomDivisor_injective D).injOn
      (Finset.finite_toSet (Finset.Iic (D.divisorMultiset a)))
  let C : Multiset {p : Associates α // Irreducible p} :=
    hA.toFinset.1.bind fun p ↦ Multiset.replicate (D.divisorMultiset a).card p
  refine (Finset.finite_toSet (Finset.Iic C)).subset ?_
  intro f hf
  change f ∈ Finset.Iic C
  rw [Finset.mem_Iic, Multiset.le_iff_count]
  intro p
  by_cases hpf : p ∈ f
  · have hpA : p ∈ A := by
      exact Finset.mem_Iic.mpr (atomDivisor_le_of_mem_factorization D ha hf hpf)
    calc
      f.count p ≤ f.card := Multiset.count_le_card p f
      _ ≤ (D.divisorMultiset a).card := factorization_card_le D ha hf
      _ ≤ C.count p := by
        have hrep : Multiset.replicate (D.divisorMultiset a).card p ≤ C := by
          apply Multiset.le_bind hA.toFinset.1
          simpa using hA.mem_toFinset.mpr hpA
        simpa using Multiset.count_le_of_le p hrep
  · rw [Multiset.count_eq_zero.mpr hpf]
    exact Nat.zero_le _

end DivisorTheory
