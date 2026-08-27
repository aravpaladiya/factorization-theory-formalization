/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.BlockMonoid.Basic
public import Mathlib.RingTheory.Factorization.Monoid
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.RingTheory.Factorization.BlockMonoid.Elasticity
import Mathlib.RingTheory.Factorization.BlockMonoid.Finite

/-!
# Half-factorial subsets of additive commutative monoids

A subset of an additive commutative monoid is half-factorial when its relative block monoid is
half-factorial. This file shows that half-factoriality descends along inclusions of supports and
proves it for subsets of a two-element support `{0, g}` when `g + g = 0`. For finite abelian
groups, the full-support result recovers the combinatorial form of Carlitz's criterion.

## Main results

* `IsHalfFactorialSet.mono`: half-factoriality descends to smaller supports.
* `isHalfFactorialSet_univ_iff`: a finite abelian group is half-factorial over its full support
  exactly when it has order at most two.
* `isHalfFactorialSet_of_subset_pair`: subsets of `{0, g}` are half-factorial when `g + g = 0`.
-/

public section

assert_not_exists Ideal

open scoped ENNReal

universe u

variable {G : Type u}

section AddCommMonoid

variable [AddCommMonoid G]

/-- A subset is half-factorial when its relative block monoid is half-factorial. -/
abbrev IsHalfFactorialSet (G₀ : Set G) : Prop :=
  HalfFactorialMonoid (BlockMonoidOver G₀)

/-- Half-factoriality passes to subsets. -/
theorem IsHalfFactorialSet.mono {G₀ G₁ : Set G} (h : G₀ ⊆ G₁)
    (h₁ : IsHalfFactorialSet G₁) : IsHalfFactorialSet G₀ := by
  let _ : HalfFactorialMonoid (BlockMonoidOver G₁) := h₁
  refine
    { toAtomicMonoid := inferInstance
      subsingleton_factorizationLengths := fun a ha m hm n hn ↦ ?_ }
  have hmapa : BlockMonoidOver.inclusion h a ≠ 0 :=
    (BlockMonoidOver.isDivisorHom_inclusion h).map_ne_zero ha
  exact HalfFactorialMonoid.subsingleton_factorizationLengths
    hmapa
      (by simpa only [BlockMonoidOver.factorizationLengths_inclusion] using hm)
      (by simpa only [BlockMonoidOver.factorizationLengths_inclusion] using hn)

noncomputable section PairSupport

private local instance : DecidableEq G := Classical.decEq G

private lemma minimalZeroSum_subset_pair {g : G} (hg : g + g = 0) {S : Multiset G}
    (hS : S.IsMinimalZeroSum) (hSupp : ∀ x ∈ S, x ∈ ({0, g} : Set G)) :
    S = {0} ∨ (S = {g, g} ∧ g ≠ 0) := by
  classical
  by_cases hz : (0 : G) ∈ S
  · exact Or.inl (hS.eq_singleton_of_zero_mem hz)
  · right
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hS.ne_zero
    have hxg : x = g := by
      rcases hSupp x hx with hx0 | hxg
      · exact (hz (hx0 ▸ hx)).elim
      · exact hxg
    have hgmem : g ∈ S := hxg ▸ hx
    have hg0 : g ≠ 0 := fun hzero ↦ hz (hzero ▸ hgmem)
    have hAll : ∀ y ∈ S, y = g := by
      intro y hy
      rcases hSupp y hy with hy0 | hyg
      · exact (hz (hy0 ▸ hy)).elim
      · exact hyg
    have hrep : S = Multiset.replicate S.card g :=
      Multiset.eq_replicate_card.mpr hAll
    have hcard_ne_one : S.card ≠ 1 := by
      intro hcard
      have hsingleton : S = {g} := by simpa [hcard] using hrep
      apply hg0
      exact Multiset.isZeroSum_singleton.mp (hsingleton ▸ hS.isZeroSum)
    have hcard_two : 2 ≤ S.card := by
      have := hS.card_pos
      omega
    have hpair_le : ({g, g} : Multiset G) ≤ S := by
      rw [hrep]
      simpa using (Multiset.replicate_le_replicate (a := g)).mpr hcard_two
    have hpair_zero : ({g, g} : Multiset G).IsZeroSum := by
      rw [Multiset.isZeroSum_iff, Multiset.sum_pair]
      exact hg
    have hpair_eq : ({g, g} : Multiset G) = S := by
      by_contra hne
      exact hS.not_isZeroSum hpair_le (by simp) hne hpair_zero
    exact ⟨hpair_eq.symm, hg0⟩

private noncomputable def pairWeight {g : G}
    (a : BlockMonoidOver ({0, g} : Set G)) : ℕ :=
  if ha : a = 0 then 0 else
    let S := Classical.choose (BlockMonoidOver.ne_zero_iff_exists_of.mp ha)
    2 * (S : Multiset G).count 0 + (S : Multiset G).count g

private lemma pairWeight_of {g : G} (S : blockMonoidOver ({0, g} : Set G)) :
    pairWeight (BlockMonoidOver.of S) =
      2 * (S : Multiset G).count 0 + (S : Multiset G).count g := by
  classical
  rw [pairWeight, dite_eq_right (BlockMonoidOver.of_ne_zero S)]
  let T := Classical.choose
    (BlockMonoidOver.ne_zero_iff_exists_of.mp (BlockMonoidOver.of_ne_zero S))
  have hT : BlockMonoidOver.of T = BlockMonoidOver.of S :=
    Classical.choose_spec
      (BlockMonoidOver.ne_zero_iff_exists_of.mp (BlockMonoidOver.of_ne_zero S))
  change 2 * (T : Multiset G).count 0 + (T : Multiset G).count g = _
  rw [BlockMonoidOver.of_injective hT]

private lemma pairWeight_mul {g : G} (a b : BlockMonoidOver ({0, g} : Set G))
    (ha : a ≠ 0) (hb : b ≠ 0) : pairWeight (a * b) = pairWeight a + pairWeight b := by
  classical
  obtain ⟨S, rfl⟩ := BlockMonoidOver.ne_zero_iff_exists_of.mp ha
  obtain ⟨T, rfl⟩ := BlockMonoidOver.ne_zero_iff_exists_of.mp hb
  rw [← BlockMonoidOver.of_add, pairWeight_of, pairWeight_of, pairWeight_of]
  simp only [AddSubmonoid.coe_add, Multiset.count_add]
  omega

private lemma pairWeight_prod {g : G}
    (f : Multiset (BlockMonoidOver ({0, g} : Set G)))
    (hf : ∀ a ∈ f, a ≠ 0) :
    pairWeight f.prod = (f.map pairWeight).sum := by
  induction f using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, ← BlockMonoidOver.of_zero, pairWeight_of]
    simp
  | @cons a f ih =>
    rw [Multiset.prod_cons, pairWeight_mul, Multiset.map_cons, Multiset.sum_cons, ih]
    · exact fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb)
    · exact hf a (Multiset.mem_cons_self a f)
    · exact Multiset.prod_ne_zero fun hzero ↦
        (hf 0 (Multiset.mem_cons.mpr (Or.inr hzero))) rfl

private lemma pairWeight_irreducible {g : G} (hg : g + g = 0)
    {a : BlockMonoidOver ({0, g} : Set G)} (ha : Irreducible a) :
    pairWeight a = if g = 0 then 3 else 2 := by
  classical
  obtain ⟨S, rfl⟩ := BlockMonoidOver.ne_zero_iff_exists_of.mp ha.ne_zero
  rw [pairWeight_of]
  have hmin := BlockMonoidOver.irreducible_of_iff.mp ha
  rcases minimalZeroSum_subset_pair hg hmin (mem_blockMonoidOver.mp S.property).2 with
    hS | ⟨hS, hg0⟩
  · rw [hS]
    by_cases hg0 : g = 0 <;> simp [hg0]
  · rw [hS]
    simp [hg0, Ne.symm hg0]

private lemma pair_length_weight {g : G} (hg : g + g = 0)
    {a : BlockMonoidOver ({0, g} : Set G)} {k : ℕ}
    (hk : k ∈ factorizationLengths a) :
    k * (if g = 0 then 3 else 2) = pairWeight a := by
  obtain ⟨f, hf, hfc⟩ := mem_factorizationLengths.mp hk
  obtain ⟨q, hq, hqprod, hqf⟩ := exists_multiset_of_mem_factorizations hf
  have hprod : q.prod = a := associated_iff_eq.mp hqprod
  have hsum_aux : ∀ (q : Multiset (BlockMonoidOver ({0, g} : Set G))),
      (∀ b ∈ q, Irreducible b) →
        (q.map pairWeight).sum = q.card * (if g = 0 then 3 else 2) := by
    intro q hq
    induction q using Multiset.induction_on with
    | empty => simp
    | @cons b q ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        pairWeight_irreducible hg (hq b (Multiset.mem_cons_self b q))]
      rw [ih (fun c hc ↦ hq c (Multiset.mem_cons_of_mem hc))]
      rw [Nat.succ_mul, Nat.add_comm]
  have hsum := hsum_aux q hq
  calc
    k * (if g = 0 then 3 else 2) = q.card * (if g = 0 then 3 else 2) := by
      congr 1
      rw [← Associates.Factorization.card_ofMultiset q hq, hqf, hfc]
    _ = (q.map pairWeight).sum := hsum.symm
    _ = pairWeight q.prod := (pairWeight_prod q fun b hb ↦ (hq b hb).ne_zero).symm
    _ = pairWeight a := congrArg pairWeight hprod

private theorem halfFactorial_pair (g : G) (hg : g + g = 0) :
    HalfFactorialMonoid (BlockMonoidOver ({0, g} : Set G)) := by
  refine
    { toAtomicMonoid := inferInstance
      subsingleton_factorizationLengths := fun a _ha m hm n hn ↦ ?_ }
  have hm' := pair_length_weight hg hm
  have hn' := pair_length_weight hg hn
  by_cases hg0 : g = 0
  · simp [hg0] at hm' hn'
    omega
  · simp [hg0] at hm' hn'
    omega

/-- A set contained in `{0, g}` is half-factorial when `g + g = 0`. If `g ≠ 0`, the atoms on
the full two-element support are `{0}` and `{g, g}`; if `g = 0`, the support is `{0}` and its only
atom is `{0}`. -/
theorem isHalfFactorialSet_of_subset_pair {G₀ : Set G} {g : G} (hg : g + g = 0)
    (h : G₀ ⊆ {0, g}) : IsHalfFactorialSet G₀ := by
  apply IsHalfFactorialSet.mono h
  exact halfFactorial_pair g hg

end PairSupport

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

private theorem isZeroSumFree_pair {g h : G} (hg : g ≠ 0) (hh : h ≠ 0)
    (hgh : g + h ≠ 0) : ({g, h} : Multiset G).IsZeroSumFree := by
  classical
  rw [Multiset.isZeroSumFree_iff]
  intro T hT hT0 hTsum
  have hcard_pos : 0 < T.card := Multiset.card_pos.mpr hT0
  have hcard_le : T.card ≤ 2 := by
    simpa using Multiset.card_le_card hT
  have hcases : T.card = 1 ∨ T.card = 2 := by omega
  rcases hcases with hcard | hcard
  · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hcard
    have hxmem : x ∈ ({g, h} : Multiset G) := by
      apply Multiset.mem_of_le hT
      rw [hx]
      exact Multiset.mem_singleton_self x
    rw [hx] at hTsum
    have hxmem' : x = g ∨ x = h := by simpa using hxmem
    have hxzero : x = 0 := Multiset.isZeroSum_singleton.mp hTsum
    rcases hxmem' with hxg | hxh
    · exact hg (hxg.symm.trans hxzero)
    · exact hh (hxh.symm.trans hxzero)
  · have hEq : T = ({g, h} : Multiset G) :=
      Multiset.eq_of_le_of_card_le hT (by simp [hcard])
    rw [hEq, Multiset.isZeroSum_iff] at hTsum
    apply hgh
    simpa using hTsum

private theorem three_le_davenportConstant_of_three_le_card [Finite G]
    (hG : 3 ≤ Nat.card G) : 3 ≤ AddMonoid.davenportConstant G := by
  let _ : Fintype G := Fintype.ofFinite G
  have hnontrivial : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa [Nat.card_eq_fintype_card] using (show 1 < Nat.card G by omega))
  let _ : Nontrivial G := hnontrivial
  obtain ⟨g, hg⟩ := exists_ne (0 : G)
  by_cases hgg : g + g = 0
  · have hcardE : 3 ≤ ENat.card G := by
      rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card]
      exact_mod_cast hG
    obtain ⟨h, h0, hg'⟩ := ENat.exists_ne_ne_of_three_le hcardE 0 g
    have hh : h ≠ 0 := h0
    have hgh : g + h ≠ 0 := by
      intro hsum
      have hgneg : g = -g := eq_neg_of_add_eq_zero_left hgg
      have hhneg : h = -g := eq_neg_of_add_eq_zero_right hsum
      exact hg' (hhneg.trans hgneg.symm)
    have hfree := isZeroSumFree_pair hg hh hgh
    simpa using hfree.isMinimalZeroSum_cons_neg_sum.card_le_davenportConstant
  · have hfree := isZeroSumFree_pair hg hg hgg
    simpa using hfree.isMinimalZeroSum_cons_neg_sum.card_le_davenportConstant

/-- A finite abelian group is half-factorial over its full support exactly when it has order at
most two. -/
theorem isHalfFactorialSet_univ_iff [Finite G] :
    IsHalfFactorialSet (Set.univ : Set G) ↔ Nat.card G ≤ 2 := by
  constructor
  · intro hHF
    by_contra hcard
    have hG3 : 3 ≤ Nat.card G := by omega
    let _ : HalfFactorialMonoid (BlockMonoid G) := hHF
    have hD3 := three_le_davenportConstant_of_three_le_card (G := G) hG3
    have hcast : (3 : ℝ≥0∞) ≤ (AddMonoid.davenportConstant G : ℝ≥0∞) :=
      ENat.toENNReal_le.mpr hD3
    have hfrac : (3 : ℝ≥0∞) / 2 ≤ 1 := by
      calc
        (3 : ℝ≥0∞) / 2 ≤ (AddMonoid.davenportConstant G : ℝ≥0∞) / 2 :=
          ENNReal.div_le_div_right hcast 2
        _ = Monoid.elasticity (BlockMonoid G) :=
          (BlockMonoid.monoid_elasticity_eq_davenportConstant_div_two
            (G := G) (by omega)).symm
        _ = 1 := (halfFactorialMonoid_iff_monoidElasticity_eq_one.mp inferInstance).2
    have h32 : (3 : ℝ≥0∞) ≤ 2 := by
      simpa using
        (ENNReal.div_le_iff (y := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp hfrac
    norm_num at h32
  · intro hG
    have hcard : Nat.card G = 1 ∨ Nat.card G = 2 := by
      have hpos := Nat.card_pos (α := G)
      omega
    rcases hcard with hcard | hcard
    · have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard).1
      apply isHalfFactorialSet_of_subset_pair (g := (0 : G)) (add_zero 0)
      intro x _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl (hsub.elim x 0)
    · obtain ⟨g, hg0, hunique⟩ := (Nat.card_eq_two_iff' (0 : G)).mp hcard
      have hgg : g + g = 0 := by
        by_contra hne
        have hsame : g + g = g := hunique (g + g) hne
        apply hg0
        exact add_left_cancel (hsame.trans (add_zero g).symm)
      apply isHalfFactorialSet_of_subset_pair hgg
      intro x _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (hunique x hx)

end AddCommGroup
