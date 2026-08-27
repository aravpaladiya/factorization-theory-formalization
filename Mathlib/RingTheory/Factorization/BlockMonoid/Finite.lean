/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.BlockMonoid.Basic
public import Mathlib.RingTheory.Factorization.Lengths

import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# Finite factorizations in relative block monoids

Every relative block monoid is atomic and has only finitely many factorizations of each nonzero
element, without any finiteness assumption on the ambient additive commutative monoid. Every atom
in a factorization of a fixed block is represented by a nonempty submultiset of that block, so both
the available atoms and their multiplicities are bounded.

This file also shows that inclusion of supporting subsets preserves sets of factorization lengths.

## Main results

* `BlockMonoidOver.instAtomicMonoid` and
  `BlockMonoidOver.instFiniteFactorizationMonoid`.
* `BlockMonoidOver.maxFactorizationLength_le_card`.
* `BlockMonoidOver.factorizationLengths_inclusion`.
-/

public section

assert_not_exists Field Ideal

universe u

variable {G : Type u} [AddCommMonoid G]

namespace BlockMonoidOver

variable {G₀ : Set G}

private theorem card_prod (f : Multiset (BlockMonoidOver G₀))
    (hf : ∀ a ∈ f, a ≠ 0) :
    card f.prod = (f.map card).sum := by
  induction f using Multiset.induction_on with
  | empty => simp
  | @cons a f ih =>
    rw [Multiset.prod_cons, card_mul]
    · simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih]
      exact fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb)
    · exact hf a (Multiset.mem_cons_self a f)
    · exact Multiset.prod_ne_zero fun h ↦
        (hf 0 (Multiset.mem_cons.mpr (Or.inr h))) rfl

private theorem card_le_sum_card (f : Multiset (BlockMonoidOver G₀))
    (hf : ∀ a ∈ f, 0 < card a) : f.card ≤ (f.map card).sum := by
  induction f using Multiset.induction_on with
  | empty => simp
  | @cons a f ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have ha := hf a (Multiset.mem_cons_self a f)
    have ih' := ih fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb)
    omega

private theorem factorization_card_le (S : blockMonoidOver G₀)
    {f : Associates.Factorization (BlockMonoidOver G₀)}
    (hf : f ∈ factorizations (of S)) : f.card ≤ (S : Multiset G).card := by
  obtain ⟨g, hgI, hgprod, hgf⟩ := exists_multiset_of_mem_factorizations hf
  have hgprod' : g.prod = of S := associated_iff_eq.mp hgprod
  have hcardprod : card g.prod = (g.map card).sum :=
    card_prod g fun a ha ↦ (hgI a ha).ne_zero
  have hcard : (g.map card).sum = (S : Multiset G).card := by
    rw [← hcardprod, hgprod', card_of]
  have hle : g.card ≤ (g.map card).sum := card_le_sum_card g fun a ha ↦ by
    obtain ⟨T, hT, rfl⟩ := exists_isMinimalZeroSum_of_irreducible (hgI a ha)
    simpa using hT.card_pos
  calc
    f.card = g.card := by rw [← hgf, Associates.Factorization.card_ofMultiset]
    _ ≤ (g.map card).sum := hle
    _ = (S : Multiset G).card := hcard

private noncomputable def atomSequence
    (p : {p : Associates (BlockMonoidOver G₀) // Irreducible p}) :
    blockMonoidOver G₀ :=
  (atomEquiv.symm p).1

private theorem atomSequence_spec
    (p : {p : Associates (BlockMonoidOver G₀) // Irreducible p}) :
    p.1 = Associates.mk (of (atomSequence p)) := by
  simpa only [atomSequence] using (coe_atomEquiv_symm_apply p).symm

private theorem atomSequence_injective :
    Function.Injective
      (atomSequence :
        {p : Associates (BlockMonoidOver G₀) // Irreducible p} → blockMonoidOver G₀) := by
  intro p q hpq
  apply atomEquiv.symm.injective
  exact Subtype.ext hpq

private theorem atomSequence_le_of_mem_factorization (S : blockMonoidOver G₀)
    {p : {p : Associates (BlockMonoidOver G₀) // Irreducible p}}
    {f : Associates.Factorization (BlockMonoidOver G₀)}
    (hf : f ∈ factorizations (of S)) (hp : p ∈ f) :
    (atomSequence p : Multiset G) ≤ (S : Multiset G) := by
  have hpdiv : p.1 ∣ Associates.mk (of S) := by
    rw [← mem_factorizations.mp hf]
    exact Associates.Factorization.dvd_prod hp
  rw [atomSequence_spec p, Associates.mk_dvd_mk] at hpdiv
  exact (of_dvd_of_iff (atomSequence p) S).mp hpdiv

/-! ### Finiteness of factorizations -/

/-- Every relative block monoid is atomic. -/
instance instAtomicMonoid : AtomicMonoid (BlockMonoidOver G₀) := by
  apply AtomicMonoid.of_exists_factors
  intro a ha
  obtain ⟨S, rfl⟩ := ne_zero_iff_exists_of.mp ha
  have H : ∀ n : ℕ, ∀ S : blockMonoidOver G₀,
      (S : Multiset G).card = n →
        ∃ f : Multiset (BlockMonoidOver G₀),
          (∀ b ∈ f, Irreducible b) ∧ Associated f.prod (of S) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hSn
      by_cases hS0 : (S : Multiset G) = 0
      · refine ⟨0, by simp, ?_⟩
        rw [Multiset.prod_zero, ← of_zero]
        exact Associated.of_eq (congrArg of (Subtype.ext hS0).symm)
      have hnu : ¬IsUnit (of S) := by
        rw [isUnit_iff, of_eq_one_iff]
        exact fun h ↦ hS0 (congrArg Subtype.val h)
      rcases irreducible_or_factor hnu with hI | ⟨b, c, hbnu, hcnu, hfac⟩
      · refine ⟨{of S}, ?_, ?_⟩
        · simpa using hI
        · simp
      · have hb0 : b ≠ 0 := by
          intro hb
          rw [hb, zero_mul] at hfac
          exact of_ne_zero S hfac
        have hc0 : c ≠ 0 := by
          intro hc
          rw [hc, mul_zero] at hfac
          exact of_ne_zero S hfac
        obtain ⟨T, rfl⟩ := ne_zero_iff_exists_of.mp hb0
        obtain ⟨U, rfl⟩ := ne_zero_iff_exists_of.mp hc0
        have hTU : (S : Multiset G) = (T : Multiset G) + (U : Multiset G) :=
          congrArg Subtype.val (of_injective (hfac.trans (of_add T U).symm))
        have hT0 : (T : Multiset G) ≠ 0 := by
          intro hT
          apply hbnu
          rw [isUnit_iff, of_eq_one_iff]
          exact Subtype.ext hT
        have hU0 : (U : Multiset G) ≠ 0 := by
          intro hU
          apply hcnu
          rw [isUnit_iff, of_eq_one_iff]
          exact Subtype.ext hU
        have hTlt : (T : Multiset G).card < n := by
          have hc := congrArg Multiset.card hTU
          rw [Multiset.card_add, hSn] at hc
          have := Multiset.card_pos.mpr hU0
          omega
        have hUlt : (U : Multiset G).card < n := by
          have hc := congrArg Multiset.card hTU
          rw [Multiset.card_add, hSn] at hc
          have := Multiset.card_pos.mpr hT0
          omega
        obtain ⟨f, hfI, hfprod⟩ := ih _ hTlt T rfl
        obtain ⟨g, hgI, hgprod⟩ := ih _ hUlt U rfl
        refine ⟨f + g, ?_, ?_⟩
        · intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx
          · exact hfI x hx
          · exact hgI x hx
        · rw [Multiset.prod_add]
          exact (hfprod.mul_mul hgprod).trans (Associated.of_eq hfac.symm)
  exact H _ S rfl

/-- Every relative block monoid is a finite factorization monoid. -/
instance instFiniteFactorizationMonoid : FiniteFactorizationMonoid (BlockMonoidOver G₀) where
  finite_factorizations a ha := by
    classical
    obtain ⟨S, rfl⟩ := ne_zero_iff_exists_of.mp ha
    let A : Set {p : Associates (BlockMonoidOver G₀) // Irreducible p} :=
      (fun p ↦ ((atomSequence p : blockMonoidOver G₀) : Multiset G)) ⁻¹'
        {T | T ∈ (S : Multiset G).powerset}
    have hA : A.Finite :=
      Set.Finite.preimage
        (Subtype.val_injective.comp atomSequence_injective).injOn
        (Multiset.finite_toSet (S : Multiset G).powerset)
    let C : Multiset {p : Associates (BlockMonoidOver G₀) // Irreducible p} :=
      hA.toFinset.1.bind fun p ↦ Multiset.replicate (S : Multiset G).card p
    refine (Multiset.finite_toSet C.powerset).subset ?_
    intro f hf
    change f ∈ C.powerset
    rw [Multiset.mem_powerset, Multiset.le_iff_count]
    intro p
    by_cases hpf : p ∈ f
    · have hpA : p ∈ A :=
        Multiset.mem_powerset.mpr (atomSequence_le_of_mem_factorization S hf hpf)
      calc
        f.count p ≤ f.card := Multiset.count_le_card p f
        _ ≤ (S : Multiset G).card := factorization_card_le S hf
        _ ≤ C.count p := by
          have hrep : Multiset.replicate (S : Multiset G).card p ≤ C := by
            apply Multiset.le_bind hA.toFinset.1
            simpa using hA.mem_toFinset.mpr hpA
          simpa using Multiset.count_le_of_le p hrep
    · rw [Multiset.count_eq_zero.mpr hpf]
      exact Nat.zero_le _

/-- The maximal factorization length of a block is at most the number of its terms. -/
theorem maxFactorizationLength_le_card (a : BlockMonoidOver G₀) :
    maxFactorizationLength a ≤ (card a : ℕ∞) := by
  by_cases ha : a = 0
  · subst a
    rw [maxFactorizationLength_of_factorizations_eq_empty factorizations_zero, card_zero]
    exact le_rfl
  · obtain ⟨S, rfl⟩ := ne_zero_iff_exists_of.mp ha
    rw [card_of, maxFactorizationLength_def]
    refine sSup_le ?_
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨f, hf, rfl⟩ := mem_factorizationLengths.mp hn
    exact ENat.natCast_le_natCast.mpr (factorization_card_le S hf)

/-! ### Inclusions of supports -/

/-- Inclusion of supporting subsets preserves sets of factorization lengths. -/
@[simp]
theorem factorizationLengths_inclusion {G₀ G₁ : Set G} (h : G₀ ⊆ G₁)
    (a : BlockMonoidOver G₀) :
    factorizationLengths (inclusion h a) = factorizationLengths a := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  apply Set.Subset.antisymm
  · intro n hn
    obtain ⟨f, hf, rfl⟩ := mem_factorizationLengths.mp hn
    obtain ⟨g, hgI, hgprod, hgf⟩ := exists_multiset_of_mem_factorizations hf
    have hprod : g.prod = inclusion h a := associated_iff_eq.mp hgprod
    have hdvd (x : {b // b ∈ g}) : x.1 ∣ inclusion h a := by
      rw [← hprod]
      exact Multiset.dvd_prod x.2
    let lift (x : {b // b ∈ g}) : BlockMonoidOver G₀ :=
      Classical.choose (exists_dvd_of_dvd_inclusion h ha (hdvd x))
    have hlift (x : {b // b ∈ g}) : inclusion h (lift x) = x.1 :=
      (Classical.choose_spec (exists_dvd_of_dvd_inclusion h ha (hdvd x))).2
    let s : Multiset (BlockMonoidOver G₀) := g.attach.map lift
    have hsI : ∀ b ∈ s, Irreducible b := by
      intro b hb
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hb
      apply (irreducible_inclusion_iff h).mp
      rw [hlift x]
      exact hgI x.1 x.2
    have hmaps : s.map (inclusion h) = g := by
      change (g.attach.map lift).map (inclusion h) = g
      rw [Multiset.map_map]
      calc
        g.attach.map (inclusion h ∘ lift) = g.attach.map Subtype.val := by
          apply Multiset.map_congr rfl
          intro x _
          exact hlift x
        _ = g := Multiset.attach_map_val g
    have hsprod : s.prod = a := by
      apply inclusion_injective h
      rw [map_multiset_prod, hmaps, hprod]
    have hsmem := ofMultiset_mem_factorizations hsI (Associated.of_eq hsprod)
    apply mem_factorizationLengths.mpr
    refine ⟨Associates.Factorization.ofMultiset s hsI, hsmem, ?_⟩
    calc
      (Associates.Factorization.ofMultiset s hsI).card = s.card :=
        Associates.Factorization.card_ofMultiset _ _
      _ = g.card := by simp [s]
      _ = f.card := by rw [← Associates.Factorization.card_ofMultiset g hgI, hgf]
  · intro n hn
    obtain ⟨f, hf, rfl⟩ := mem_factorizationLengths.mp hn
    obtain ⟨g, hgI, hgprod, hgf⟩ := exists_multiset_of_mem_factorizations hf
    have hgi : ∀ b ∈ g.map (inclusion h), Irreducible b := by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
      exact irreducible_inclusion h (hgI c hc)
    have hgprod' : Associated (g.map (inclusion h)).prod (inclusion h a) := by
      rw [← map_multiset_prod]
      exact hgprod.map (inclusion h)
    have hmem := ofMultiset_mem_factorizations hgi hgprod'
    apply mem_factorizationLengths.mpr
    refine ⟨Associates.Factorization.ofMultiset (g.map (inclusion h)) hgi, hmem, ?_⟩
    rw [Associates.Factorization.card_ofMultiset, Multiset.card_map,
      ← Associates.Factorization.card_ofMultiset g hgI, hgf]

end BlockMonoidOver
