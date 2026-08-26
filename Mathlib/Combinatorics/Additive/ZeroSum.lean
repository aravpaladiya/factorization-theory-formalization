/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Zero-sum sequences

A sequence over an additive commutative monoid `G` is represented by a multiset of elements of
`G`. This file develops zero-sum sequences and their behavior under additive maps.

## Main declarations

* `Multiset.IsZeroSum`: the terms of a sequence sum to zero.
* `Multiset.IsZeroSumFree`: no nonempty subsequence sums to zero.
* `Multiset.IsMinimalZeroSum`: a nonempty zero-sum sequence with no proper nonempty zero-sum
  subsequence.

The predicates and their order-theoretic API require only an additive commutative monoid.
Constructions involving the negated sum of a sequence require an additive commutative group.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]

## Tags

additive combinatorics, zero-sum sequence
-/

public section

assert_not_exists Field Ideal

variable {G : Type*} {S T : Multiset G} {g : G}

namespace Multiset

/-! ### Zero-sum sequences -/

section AddCommMonoid

variable [AddCommMonoid G]

/-- A sequence over an additive commutative monoid is *zero-sum* if its terms sum to `0`. The
empty sequence is zero-sum. -/
def IsZeroSum (S : Multiset G) : Prop :=
  S.sum = 0

theorem isZeroSum_iff : IsZeroSum S ↔ S.sum = 0 := by
  rfl

@[simp]
theorem isZeroSum_zero : IsZeroSum (0 : Multiset G) :=
  Multiset.sum_zero

@[simp]
theorem isZeroSum_singleton : IsZeroSum ({g} : Multiset G) ↔ g = 0 := by
  rw [isZeroSum_iff, Multiset.sum_singleton]

theorem IsZeroSum.add (hS : IsZeroSum S) (hT : IsZeroSum T) : IsZeroSum (S + T) := by
  rw [isZeroSum_iff, Multiset.sum_add, hS, hT, add_zero]

/-- An additive monoid homomorphism carries zero-sum sequences to zero-sum sequences. -/
lemma IsZeroSum.map {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (hS : IsZeroSum S) (f : F) :
    IsZeroSum (S.map f) := by
  rw [isZeroSum_iff, ← map_multiset_sum, hS, _root_.map_zero]

lemma isZeroSum_map_iff_of_injective {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    IsZeroSum (S.map f) ↔ IsZeroSum S := by
  rw [isZeroSum_iff, isZeroSum_iff, ← map_multiset_sum, ← _root_.map_zero f, hf.eq_iff]

@[simp]
theorem isZeroSum_map_addEquiv_iff {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    IsZeroSum (S.map e) ↔ IsZeroSum S :=
  isZeroSum_map_iff_of_injective e.toAddMonoidHom e.injective

/-- If a concatenation is zero-sum and its left part is zero-sum, then its right part is
zero-sum. -/
theorem IsZeroSum.of_add_left (hST : IsZeroSum (S + T)) (hS : IsZeroSum S) : IsZeroSum T := by
  rw [isZeroSum_iff, Multiset.sum_add, hS, zero_add] at hST
  exact hST

theorem IsZeroSum.of_add_right (hST : IsZeroSum (S + T)) (hT : IsZeroSum T) : IsZeroSum S :=
  IsZeroSum.of_add_left (S := T) (by rwa [add_comm]) hT

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

theorem isZeroSum_cons_neg_sum (S : Multiset G) : IsZeroSum (-S.sum ::ₘ S) := by
  rw [isZeroSum_iff, Multiset.sum_cons, neg_add_cancel]

end AddCommGroup

/-! ### Zero-sum free sequences -/

section AddCommMonoid

variable [AddCommMonoid G]

/-- A sequence is *zero-sum free* if none of its nonempty subsequences is zero-sum. The empty
sequence is zero-sum free. -/
def IsZeroSumFree (S : Multiset G) : Prop :=
  ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → ¬IsZeroSum T

theorem isZeroSumFree_iff :
    IsZeroSumFree S ↔ ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → ¬IsZeroSum T := by
  rfl

@[simp]
lemma not_isZeroSumFree :
    ¬IsZeroSumFree S ↔ ∃ T ≤ S, T ≠ 0 ∧ IsZeroSum T := by
  simp [IsZeroSumFree]

@[simp]
theorem isZeroSumFree_zero : IsZeroSumFree (0 : Multiset G) := by
  intro T hT hT0
  exact (hT0 (Multiset.le_zero.mp hT)).elim

@[simp]
lemma isZeroSumFree_singleton : IsZeroSumFree ({g} : Multiset G) ↔ g ≠ 0 := by
  simp [IsZeroSumFree, IsZeroSum]

theorem IsZeroSumFree.mono (hS : IsZeroSumFree S) (hTS : T ≤ S) : IsZeroSumFree T :=
  fun _ hUT hU ↦ hS (hUT.trans hTS) hU

theorem IsZeroSumFree.notMem_zero (hS : IsZeroSumFree S) : (0 : G) ∉ S := fun h ↦
  hS (Multiset.singleton_le.mpr h) (Multiset.singleton_ne_zero _) (isZeroSum_singleton.mpr rfl)

lemma IsZeroSumFree.not_isZeroSum_of_ne_zero (hS : IsZeroSumFree S) (hne : S ≠ 0) :
    ¬IsZeroSum S :=
  hS le_rfl hne

private theorem exists_le_map_eq_of_le_map {α β : Type*} [Nonempty α] {f : α → β}
    (hf : Function.Injective f) {s : Multiset α} {t : Multiset β} (h : t ≤ s.map f) :
    ∃ u ≤ s, u.map f = t := by
  let u := t.map (Function.invFun f)
  have hu : u.map f = t := by
    change (t.map (Function.invFun f)).map f = t
    rw [Multiset.map_map]
    calc
      t.map (f ∘ Function.invFun f) = t.map id := by
        apply Multiset.map_congr rfl
        intro x hx
        obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le h hx)
        exact congrArg f (Function.leftInverse_invFun hf y)
      _ = t := Multiset.map_id t
  refine ⟨u, ?_, hu⟩
  apply (Multiset.map_le_map_iff hf).mp
  rw [hu]
  exact h

lemma isZeroSumFree_map_iff_of_injective {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    IsZeroSumFree (S.map f) ↔ IsZeroSumFree S := by
  constructor
  · intro hS T hTS hT hTsum
    exact hS (Multiset.map_le_map hTS) (by simpa using hT) (hTsum.map f)
  · intro hS T hTS hT hTsum
    obtain ⟨U, hUS, rfl⟩ := exists_le_map_eq_of_le_map hf hTS
    exact hS hUS (by simpa using hT) ((isZeroSum_map_iff_of_injective f hf).mp hTsum)

alias ⟨_, IsZeroSumFree.map⟩ := isZeroSumFree_map_iff_of_injective

@[simp]
theorem isZeroSumFree_map_addEquiv_iff {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    IsZeroSumFree (S.map e) ↔ IsZeroSumFree S :=
  isZeroSumFree_map_iff_of_injective e.toAddMonoidHom e.injective

/-! ### Minimal zero-sum sequences -/

/-- A sequence is *minimal zero-sum* if it is nonempty, is zero-sum, and none of its proper
nonempty subsequences is zero-sum. -/
def IsMinimalZeroSum (S : Multiset G) : Prop :=
  IsZeroSum S ∧ S ≠ 0 ∧
    ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → T ≠ S → ¬IsZeroSum T

theorem isMinimalZeroSum_iff :
    IsMinimalZeroSum S ↔ IsZeroSum S ∧ S ≠ 0 ∧
      ∀ ⦃T : Multiset G⦄, T ≤ S → T ≠ 0 → T ≠ S → ¬IsZeroSum T := by
  rfl

theorem IsMinimalZeroSum.isZeroSum (hS : IsMinimalZeroSum S) : IsZeroSum S :=
  hS.1

theorem IsMinimalZeroSum.ne_zero (hS : IsMinimalZeroSum S) : S ≠ 0 :=
  hS.2.1

theorem IsMinimalZeroSum.not_isZeroSum (hS : IsMinimalZeroSum S) (hTS : T ≤ S) (hT : T ≠ 0)
    (hne : T ≠ S) : ¬IsZeroSum T :=
  hS.2.2 hTS hT hne

theorem IsMinimalZeroSum.card_pos (hS : IsMinimalZeroSum S) : 0 < S.card :=
  Multiset.card_pos.mpr hS.ne_zero

theorem IsMinimalZeroSum.card_ne_zero (hS : IsMinimalZeroSum S) : S.card ≠ 0 :=
  hS.card_pos.ne'

lemma isMinimalZeroSum_map_iff_of_injective {H F : Type*} [AddCommMonoid H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    IsMinimalZeroSum (S.map f) ↔ IsMinimalZeroSum S := by
  constructor
  · intro hS
    refine ⟨(isZeroSum_map_iff_of_injective f hf).mp hS.isZeroSum, ?_, ?_⟩
    · simpa using hS.ne_zero
    · intro T hTS hT hTne hTsum
      apply hS.not_isZeroSum (Multiset.map_le_map hTS) (by simpa using hT)
      · exact fun h ↦ hTne (Multiset.map_injective hf h)
      · exact hTsum.map f
  · intro hS
    refine ⟨hS.isZeroSum.map f, by simpa using hS.ne_zero, ?_⟩
    intro T hTS hT hTne hTsum
    obtain ⟨U, hUS, rfl⟩ := exists_le_map_eq_of_le_map hf hTS
    apply hS.not_isZeroSum hUS (by simpa using hT)
    · exact fun h ↦ hTne (congrArg (Multiset.map f) h)
    · exact (isZeroSum_map_iff_of_injective f hf).mp hTsum

alias ⟨_, IsMinimalZeroSum.map⟩ := isMinimalZeroSum_map_iff_of_injective

@[simp]
theorem isMinimalZeroSum_map_addEquiv_iff {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    IsMinimalZeroSum (S.map e) ↔ IsMinimalZeroSum S :=
  isMinimalZeroSum_map_iff_of_injective e.toAddMonoidHom e.injective

/-- An additive equivalence carries minimal zero-sum sequences to minimal zero-sum sequences. -/
theorem IsMinimalZeroSum.map_addEquiv {H : Type*} [AddCommMonoid H]
    (hS : IsMinimalZeroSum S) (e : G ≃+ H) : IsMinimalZeroSum (S.map e) :=
  hS.map e.toAddMonoidHom e.injective

@[simp]
theorem isMinimalZeroSum_singleton : IsMinimalZeroSum ({g} : Multiset G) ↔ g = 0 := by
  refine ⟨fun hS ↦ isZeroSum_singleton.mp hS.isZeroSum, ?_⟩
  rintro rfl
  refine ⟨isZeroSum_singleton.mpr rfl, Multiset.singleton_ne_zero _, fun T hTS hT hne ↦ ?_⟩
  exact absurd ((Multiset.le_singleton.mp hTS).resolve_left hT) hne

/-- A minimal zero-sum sequence containing `0` is the singleton `{0}`: otherwise `{0}` would be a
proper nonempty zero-sum subsequence. -/
theorem IsMinimalZeroSum.eq_singleton_of_zero_mem (hS : IsMinimalZeroSum S) (h : (0 : G) ∈ S) :
    S = {0} := by
  by_contra hne
  exact hS.not_isZeroSum (Multiset.singleton_le.mpr h) (Multiset.singleton_ne_zero _)
    (Ne.symm hne) (isZeroSum_singleton.mpr rfl)

/-- Deleting one term of a minimal zero-sum sequence leaves a zero-sum free sequence. -/
theorem IsMinimalZeroSum.isZeroSumFree_of_cons (hS : IsMinimalZeroSum (g ::ₘ S)) :
    IsZeroSumFree S := by
  intro T hTS hT hTsum
  apply hS.not_isZeroSum (hTS.trans (Multiset.le_cons_self S g)) hT ?_ hTsum
  rintro rfl
  have hcard := Multiset.card_le_card hTS
  exact (Nat.not_succ_le_self S.card) (by simpa only [Multiset.card_cons] using hcard)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

/-- Appending the negated sum to a zero-sum free sequence produces a minimal zero-sum sequence. -/
theorem IsZeroSumFree.isMinimalZeroSum_cons_neg_sum (hS : IsZeroSumFree S) :
    IsMinimalZeroSum (-S.sum ::ₘ S) := by
  refine ⟨isZeroSum_cons_neg_sum S, Multiset.cons_ne_zero, ?_⟩
  intro T hT hT0 hTne hTsum
  classical
  -- If the new term occurs, its complement in the sequence contradicts zero-sum freeness;
  -- otherwise the subsequence itself does.
  by_cases hneg : -S.sum ∈ T
  · obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem hneg
    obtain ⟨U, hU⟩ := Multiset.le_iff_exists_add.mp hT
    have hU0 : U ≠ 0 := by
      rintro rfl
      simp at hU
      exact hTne (congrArg (fun V ↦ -S.sum ::ₘ V) hU.symm)
    have hTU : T' + U = S := by
      simpa [Multiset.cons_add] using hU.symm
    apply hS (Multiset.le_add_left U T' |>.trans hTU.le) hU0
    apply IsZeroSum.of_add_left (S := -S.sum ::ₘ T')
    · rw [← hU]
      exact isZeroSum_cons_neg_sum S
    · exact hTsum
  · exact hS ((Multiset.le_cons_of_notMem hneg).mp hT) hT0 hTsum

end AddCommGroup

end Multiset
