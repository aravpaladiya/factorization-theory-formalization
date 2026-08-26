/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Combinatorics.Additive.ZeroSum
public import Mathlib.Data.ENat.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The Davenport constant

The Davenport constant `D(G)` of an additive commutative monoid is the supremum in `ℕ∞` of the
lengths of its minimal zero-sum sequences. It is `⊤` when these lengths are unbounded.

## Main declarations

* `AddMonoid.davenportConstant G`: the supremum of the lengths of the minimal zero-sum sequences
  over `G`.
* `AddMonoid.davenportConstant_le_of_injective`: an injective additive homomorphism does not
  decrease the Davenport constant.
* `AddMonoid.davenportConstant_congr`: the Davenport constant is invariant under additive
  equivalence.
* `AddMonoid.exists_isMinimalZeroSum_card_eq_davenportConstant_of_ne_top`: a finite Davenport
  constant is attained.
* `AddMonoid.davenportConstant_eq_one_iff`: a group's Davenport constant is `1` exactly when it is
  trivial.
* `AddMonoid.davenportConstant_le_natCard`: `D(G) ≤ |G|` for finite cancellative additive
  commutative monoids.
* `AddMonoid.davenportConstant_le_enatCard`: `D(G)` is at most the extended cardinality of a
  cancellative additive commutative monoid.
* `AddMonoid.davenportConstant_le_iff_forall_exists_isZeroSum`: the Davenport constant as the
  least zero-sum threshold.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

variable {G : Type*} {S : Multiset G}

namespace AddMonoid

section AddCommMonoid

variable [AddCommMonoid G]

/-- The **Davenport constant** `D(G)` of an additive commutative monoid `G`: the supremum of
the lengths of its minimal zero-sum sequences over `G`.

The supremum is `⊤` when these lengths are unbounded. The indexing subtype is nonempty because
`{0}` is minimal zero-sum over every `G`. -/
noncomputable def davenportConstant (G : Type*) [AddCommMonoid G] : ℕ∞ :=
  ⨆ S : {S : Multiset G // S.IsMinimalZeroSum}, (S.1.card : ℕ∞)

theorem davenportConstant_def :
    davenportConstant G =
      ⨆ S : {S : Multiset G // S.IsMinimalZeroSum}, (S.1.card : ℕ∞) := by
  rfl

/-- An extended natural bounds the Davenport constant exactly when it bounds the length of every
minimal zero-sum sequence. -/
theorem davenportConstant_le_iff {n : ℕ∞} :
    davenportConstant G ≤ n ↔
      ∀ {S : Multiset G}, S.IsMinimalZeroSum → (S.card : ℕ∞) ≤ n := by
  constructor
  · intro h S hS
    exact (le_iSup (fun T : {T : Multiset G // T.IsMinimalZeroSum} ↦
      (T.1.card : ℕ∞)) ⟨S, hS⟩).trans h
  · intro h
    rw [davenportConstant_def]
    exact iSup_le fun S ↦ h S.2

theorem davenportConstant_le {n : ℕ∞}
    (h : ∀ {S : Multiset G}, S.IsMinimalZeroSum → (S.card : ℕ∞) ≤ n) :
    davenportConstant G ≤ n :=
  davenportConstant_le_iff.mpr h

end AddCommMonoid

end AddMonoid

theorem Multiset.IsMinimalZeroSum.card_le_davenportConstant [AddCommMonoid G]
    (hS : S.IsMinimalZeroSum) :
    (S.card : ℕ∞) ≤ AddMonoid.davenportConstant G := by
  rw [AddMonoid.davenportConstant_def]
  exact le_iSup (fun T : {T : Multiset G // T.IsMinimalZeroSum} ↦ (T.1.card : ℕ∞)) ⟨S, hS⟩

namespace AddMonoid

section AddCommMonoid

variable [AddCommMonoid G]

/-- An injective additive homomorphism does not decrease the Davenport constant. -/
theorem davenportConstant_le_of_injective {H F : Type*} [AddCommMonoid H]
    [FunLike F G H] [AddMonoidHomClass F G H] (f : F) (hf : Function.Injective f) :
    davenportConstant G ≤ davenportConstant H := by
  rw [davenportConstant_le_iff]
  intro S hS
  simpa using (hS.map f hf).card_le_davenportConstant

/-- The Davenport constant is invariant under additive equivalence. -/
theorem davenportConstant_congr {H : Type*} [AddCommMonoid H] (e : G ≃+ H) :
    davenportConstant G = davenportConstant H := by
  exact le_antisymm (davenportConstant_le_of_injective e e.injective)
    (davenportConstant_le_of_injective e.symm e.symm.injective)

theorem one_le_davenportConstant : 1 ≤ davenportConstant G := by
  simpa using
    (Multiset.isMinimalZeroSum_singleton (g := (0 : G))).mpr rfl |>.card_le_davenportConstant

theorem davenportConstant_ne_zero : davenportConstant G ≠ 0 := fun h ↦ by
  simpa [h] using one_le_davenportConstant (G := G)

/-- If the Davenport constant is finite, some minimal zero-sum sequence attains it. -/
theorem exists_isMinimalZeroSum_card_eq_davenportConstant_of_ne_top
    (hG : davenportConstant G ≠ ⊤) :
    ∃ S : Multiset G, S.IsMinimalZeroSum ∧ (S.card : ℕ∞) = davenportConstant G := by
  let _ : Nonempty {S : Multiset G // S.IsMinimalZeroSum} :=
    ⟨⟨{0}, Multiset.isMinimalZeroSum_singleton.mpr rfl⟩⟩
  have hlt : davenportConstant G < ⊤ := lt_top_iff_ne_top.mpr hG
  rw [davenportConstant_def] at hlt
  obtain ⟨S, hS⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  refine ⟨S.1, S.2, ?_⟩
  rw [davenportConstant_def]
  exact hS

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

theorem two_le_davenportConstant [Nontrivial G] : 2 ≤ davenportConstant G := by
  obtain ⟨g, hg⟩ := exists_ne (0 : G)
  have hfree : Multiset.IsZeroSumFree ({g} : Multiset G) :=
    Multiset.isZeroSumFree_singleton.mpr hg
  simpa using hfree.isMinimalZeroSum_cons_neg_sum.card_le_davenportConstant

/-- The Davenport constant of an additive commutative group is `1` if and only if the group is
trivial. -/
theorem davenportConstant_eq_one_iff : davenportConstant G = 1 ↔ Subsingleton G := by
  constructor
  · intro hD
    rw [← not_nontrivial_iff_subsingleton]
    intro hG
    let _ : Nontrivial G := hG
    have h := two_le_davenportConstant (G := G)
    rw [hD] at h
    simp_all
  · intro hG
    let _ : Subsingleton G := hG
    apply le_antisymm
    · apply davenportConstant_le
      intro S hS
      obtain ⟨g, hg⟩ := Multiset.exists_mem_of_ne_zero hS.ne_zero
      have h0 : g = 0 := Subsingleton.elim _ _
      subst g
      rw [hS.eq_singleton_of_zero_mem hg]
      simp
    · exact one_le_davenportConstant

end AddCommGroup

section AddCancelCommMonoid

variable [AddCancelCommMonoid G]

/-- For a finite cancellative additive commutative monoid `G`, the Davenport constant is at
most `|G|`. -/
theorem davenportConstant_le_natCard [Finite G] : davenportConstant G ≤ Nat.card G := by
  rw [davenportConstant_le_iff]
  intro S hS
  rw [ENat.natCast_le_natCast]
  induction S using Quotient.inductionOn with
  | _ L =>
      -- Equal partial sums would cut out a proper nonempty zero-sum subsequence of `L`.
      let f : Fin L.length → G := fun i ↦ (L.take i).sum
      have hcollision : ∀ i j : Fin L.length, i < j → f i ≠ f j := by
        intro i j hij heq
        let M := (L.drop i).take (j - i)
        have htake : L.take j = L.take i ++ M := by
          have h := List.take_add (l := L) (i := i) (j := j - i)
          rw [Nat.add_sub_of_le hij.le] at h
          exact h
        have hMsum : M.sum = 0 := by
          have heq' : (L.take i).sum = (L.take j).sum := heq
          rw [htake, List.sum_append] at heq'
          have hz : (L.take i).sum + 0 = (L.take i).sum + M.sum := by
            simpa using heq'
          exact (add_left_cancel hz).symm
        have hMcard : M.length = j - i := by
          dsimp [M]
          rw [List.length_take, List.length_drop, min_eq_left]
          exact Nat.sub_le_sub_right (Nat.le_of_lt j.isLt) i
        have hM0 : (↑M : Multiset G) ≠ 0 := by
          intro hM
          have hc := congrArg Multiset.card hM
          have : M.length = 0 := by simpa using hc
          exact (Nat.ne_of_gt (Nat.sub_pos_of_lt hij)) (hMcard ▸ this)
        have hMproper : (↑M : Multiset G) ≠ (↑L : Multiset G) := by
          intro hM
          have hc := congrArg Multiset.card hM
          have hlt : M.length < L.length := by
            calc
              M.length = j - i := hMcard
              _ ≤ j := Nat.sub_le _ _
              _ < L.length := j.isLt
          exact (Nat.ne_of_lt hlt) (by simpa using hc)
        have hMle : (↑M : Multiset G) ≤ (↑L : Multiset G) :=
          ((List.take_sublist _ _).trans (List.drop_sublist _ _)).subperm
        exact hS.not_isZeroSum hMle hM0 hMproper (Multiset.isZeroSum_iff.mpr hMsum)
      have hf : Function.Injective f := by
        intro i j heq
        by_contra hij
        rcases Fin.lt_or_lt_of_ne hij with hij | hji
        · exact hcollision i j hij heq
        · exact hcollision j i hji heq.symm
      simpa [f] using Nat.card_le_card_of_injective f hf

/-- The Davenport constant of a cancellative additive commutative monoid is at most its extended
cardinality. -/
theorem davenportConstant_le_enatCard : davenportConstant G ≤ ENat.card G := by
  cases finite_or_infinite G
  · let _ := Fintype.ofFinite G
    simpa [Nat.card_eq_fintype_card] using davenportConstant_le_natCard (G := G)
  · simp

/-- The Davenport constant of a finite cancellative additive commutative monoid is finite. -/
theorem davenportConstant_lt_top [Finite G] : davenportConstant G < ⊤ := by
  exact davenportConstant_le_natCard.trans_lt (ENat.natCast_lt_top _)

end AddCancelCommMonoid

end AddMonoid

/-! ### The Davenport constant as a zero-sum threshold -/

theorem Multiset.IsZeroSumFree.card_add_one_le_davenportConstant [AddCommGroup G]
    (hS : S.IsZeroSumFree) :
    (S.card : ℕ∞) + 1 ≤ AddMonoid.davenportConstant G := by
  simpa [add_comm] using hS.isMinimalZeroSum_cons_neg_sum.card_le_davenportConstant

namespace AddMonoid

section AddCommGroup

variable [AddCommGroup G]

/-- Every sequence of length at least `D(G)` has a nonempty zero-sum subsequence. When
`davenportConstant G = ⊤`, the hypothesis is impossible because `S.card` is finite. -/
theorem exists_isZeroSum_of_davenportConstant_le_card
    (h : davenportConstant G ≤ S.card) : ∃ T ≤ S, T ≠ 0 ∧ T.IsZeroSum := by
  by_contra hnone
  have hfree : S.IsZeroSumFree := by
    by_contra hfree
    exact hnone (Multiset.not_isZeroSumFree.mp hfree)
  have hbad := hfree.card_add_one_le_davenportConstant.trans h
  rw [ENat.add_one_le_iff (ENat.natCast_ne_top S.card)] at hbad
  exact hbad.false

end AddCommGroup

section AddCommMonoid

variable [AddCommMonoid G]

/-- Any natural length forcing a nonempty zero-sum subsequence is an upper bound for `D(G)`.
This direction requires only an additive commutative monoid; the converse threshold theorem
`exists_isZeroSum_of_davenportConstant_le_card` uses additive inverses. -/
theorem davenportConstant_le_of_forall_exists_isZeroSum {n : ℕ}
    (h : ∀ S : Multiset G, n ≤ S.card → ∃ T ≤ S, T ≠ 0 ∧ T.IsZeroSum) :
    davenportConstant G ≤ n := by
  rw [davenportConstant_le_iff]
  intro S hS
  obtain ⟨g, hg⟩ := Multiset.exists_mem_of_ne_zero hS.ne_zero
  obtain ⟨S', rfl⟩ := Multiset.exists_cons_of_mem hg
  have hlt : S'.card < n := by
    by_contra hn
    obtain ⟨T, hT, hT0, hTsum⟩ := h S' (Nat.le_of_not_gt hn)
    exact (hS.isZeroSumFree_of_cons.mono hT).not_isZeroSum_of_ne_zero hT0 hTsum
  rw [Multiset.card_cons, ENat.natCast_le_natCast]
  exact Nat.succ_le_iff.mpr hlt

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G]

/-- The Davenport constant is the least natural length forcing every sequence of that length or
greater to contain a nonempty zero-sum subsequence. -/
theorem davenportConstant_le_iff_forall_exists_isZeroSum {n : ℕ} :
    davenportConstant G ≤ n ↔
      ∀ S : Multiset G, n ≤ S.card → ∃ T ≤ S, T ≠ 0 ∧ T.IsZeroSum := by
  constructor
  · intro hD S hS
    apply exists_isZeroSum_of_davenportConstant_le_card
    exact hD.trans (by simpa using hS)
  · exact davenportConstant_le_of_forall_exists_isZeroSum

end AddCommGroup

end AddMonoid
