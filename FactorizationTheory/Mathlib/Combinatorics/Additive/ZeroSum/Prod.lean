/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import FactorizationTheory.Mathlib.Combinatorics.Additive.ZeroSum

/-!
# Zero-sum sequences over direct products

This file combines sequences over two additive commutative monoids by mapping them to the
coordinate axes of their direct product. The construction preserves zero-sum freeness. By
adjoining the pair of their distinguished heads, it also combines two headed minimal zero-sum
sequences into a minimal zero-sum sequence over the product.

## Main declarations

* `Multiset.IsZeroSumFree.map_inl_add_map_inr`: combine zero-sum-free sequences along the two
  coordinate axes.
* `Multiset.IsMinimalZeroSum.prod`: combine two headed minimal zero-sum sequences over a direct
  product.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

variable {G H : Type*} {S : Multiset G} {T : Multiset H} {g : G} {h : H}

namespace Multiset

private lemma isZeroSum_map_fst_of_le_map_inr [AddCommMonoid G] [AddCommMonoid H]
    {W : Multiset (G × H)} (hW : W ≤ T.map (AddMonoidHom.inr G H)) :
    (W.map Prod.fst).IsZeroSum := by
  rw [isZeroSum_iff]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨p, hpW, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hW hpW)
  rfl

private lemma isZeroSum_map_snd_of_le_map_inl [AddCommMonoid G] [AddCommMonoid H]
    {W : Multiset (G × H)} (hW : W ≤ S.map (AddMonoidHom.inl G H)) :
    (W.map Prod.snd).IsZeroSum := by
  rw [isZeroSum_iff]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨p, hpW, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hW hpW)
  rfl

/-- Mapping zero-sum-free sequences into the two coordinate axes of a product and concatenating
them gives a zero-sum-free sequence. -/
theorem IsZeroSumFree.map_inl_add_map_inr [AddCommMonoid G] [AddCommMonoid H]
    (hS : S.IsZeroSumFree) (hT : T.IsZeroSumFree) :
    (S.map (AddMonoidHom.inl G H) + T.map (AddMonoidHom.inr G H)).IsZeroSumFree := by
  rw [isZeroSumFree_iff]
  intro V hV hV0 hVsum
  classical
  let A := S.map (AddMonoidHom.inl G H)
  let B := T.map (AddMonoidHom.inr G H)
  let X := V ∩ A
  let Y := V - A
  have hXA : X ≤ A := Multiset.inter_le_right
  have hYB : Y ≤ B := by
    rw [Multiset.sub_le_iff_le_add]
    simpa only [A, B, Multiset.add_comm] using hV
  have hdecomp : Y + X = V := by
    simpa only [X, Y] using Multiset.sub_add_inter V A
  have hVfst := hVsum.map (AddMonoidHom.fst G H)
  rw [← hdecomp, Multiset.map_add] at hVfst
  have hXsum : (X.map Prod.fst).IsZeroSum :=
    hVfst.of_add_left (isZeroSum_map_fst_of_le_map_inr (by simpa only [B] using hYB))
  have hVsnd := hVsum.map (AddMonoidHom.snd G H)
  rw [← hdecomp, Multiset.map_add] at hVsnd
  have hYsum : (Y.map Prod.snd).IsZeroSum :=
    hVsnd.of_add_right (isZeroSum_map_snd_of_le_map_inl (by simpa only [A] using hXA))
  by_cases hX0 : X = 0
  · have hY0 : Y ≠ 0 := by
      intro hY
      apply hV0
      rw [← hdecomp, hX0, hY]
      simp
    apply isZeroSumFree_iff.mp hT (T := Y.map Prod.snd) ?_ (by simpa using hY0) hYsum
    simpa [B, Function.comp_def] using Multiset.map_le_map (f := Prod.snd) hYB
  · apply isZeroSumFree_iff.mp hS (T := X.map Prod.fst) ?_ (by simpa using hX0) hXsum
    simpa [A, Function.comp_def] using Multiset.map_le_map (f := Prod.fst) hXA

/-- Two headed minimal zero-sum sequences determine a minimal zero-sum sequence over the direct
product by combining their heads and mapping their tails to the coordinate axes. -/
theorem IsMinimalZeroSum.prod [AddCommMonoid G] [AddCommMonoid H]
    (hS : (g ::ₘ S).IsMinimalZeroSum) (hT : (h ::ₘ T).IsMinimalZeroSum) :
    ((g, h) ::ₘ (S.map (AddMonoidHom.inl G H) +
      T.map (AddMonoidHom.inr G H))).IsMinimalZeroSum := by
  let A := S.map (AddMonoidHom.inl G H)
  let B := T.map (AddMonoidHom.inr G H)
  let U := A + B
  -- The axis-supported tails are zero-sum free, while the combined heads make the full
  -- sequence zero-sum.
  have hUfree : U.IsZeroSumFree := hS.isZeroSumFree_of_cons.map_inl_add_map_inr
    hT.isZeroSumFree_of_cons
  have hsum : ((g, h) ::ₘ U).IsZeroSum := by
    rw [isZeroSum_iff]
    dsimp [U, A, B]
    rw [Multiset.sum_cons, Multiset.sum_add,
      ← AddMonoidHom.map_multiset_sum, ← AddMonoidHom.map_multiset_sum]
    simp only [AddMonoidHom.inl_apply, AddMonoidHom.inr_apply]
    apply Prod.ext
    · change g + (S.sum + 0) = 0
      simpa only [Multiset.sum_cons, add_zero] using isZeroSum_iff.mp hS.isZeroSum
    · change h + (0 + T.sum) = 0
      simpa only [Multiset.sum_cons, zero_add] using isZeroSum_iff.mp hT.isZeroSum
  rw [isMinimalZeroSum_iff]
  refine ⟨hsum, Multiset.cons_ne_zero, ?_⟩
  intro V hVU hV0 hVne hVsum
  classical
  -- A zero-sum subsequence omitting the combined head lies in the zero-sum-free tails.
  -- If it contains the head, each coordinate projection is forced to be the original sequence.
  by_cases hp : (g, h) ∈ V
  · obtain ⟨V', rfl⟩ := Multiset.exists_cons_of_mem hp
    have hV'U : V' ≤ U := (Multiset.cons_le_cons_iff _).mp hVU
    let X := V' ∩ A
    let Y := V' - A
    have hXA : X ≤ A := Multiset.inter_le_right
    have hYB : Y ≤ B := by
      rw [Multiset.sub_le_iff_le_add]
      simpa only [U, Multiset.add_comm] using hV'U
    have hdecomp : Y + X = V' := by
      simpa only [X, Y] using Multiset.sub_add_inter V' A
    have hVfst := hVsum.map (AddMonoidHom.fst G H)
    rw [← hdecomp, Multiset.map_cons, Multiset.map_add] at hVfst
    change (g ::ₘ (Y.map Prod.fst + X.map Prod.fst)).IsZeroSum at hVfst
    have hGXsum : (g ::ₘ X.map Prod.fst).IsZeroSum := by
      rw [isZeroSum_iff, Multiset.sum_cons]
      rw [isZeroSum_iff, Multiset.sum_cons, Multiset.sum_add] at hVfst
      have hYsum :=
        isZeroSum_map_fst_of_le_map_inr (by simpa only [B] using hYB)
      rw [isZeroSum_iff] at hYsum
      rwa [hYsum, zero_add] at hVfst
    have hGXle : g ::ₘ X.map Prod.fst ≤ g ::ₘ S := by
      apply Multiset.cons_le_cons
      simpa [A, Function.comp_def] using Multiset.map_le_map (f := Prod.fst) hXA
    have hGXeq : g ::ₘ X.map Prod.fst = g ::ₘ S := by
      by_contra hne
      exact hS.not_isZeroSum hGXle Multiset.cons_ne_zero hne hGXsum
    have hXmap : X.map Prod.fst = S := by simpa using hGXeq
    have hXAeq : X = A := by
      apply Multiset.eq_of_le_of_card_le hXA
      simpa [A] using (congrArg Multiset.card hXmap).ge
    have hVsnd := hVsum.map (AddMonoidHom.snd G H)
    rw [← hdecomp, Multiset.map_cons, Multiset.map_add] at hVsnd
    change (h ::ₘ (Y.map Prod.snd + X.map Prod.snd)).IsZeroSum at hVsnd
    have hHYsum : (h ::ₘ Y.map Prod.snd).IsZeroSum := by
      rw [isZeroSum_iff, Multiset.sum_cons]
      rw [isZeroSum_iff, Multiset.sum_cons, Multiset.sum_add] at hVsnd
      have hXsum :=
        isZeroSum_map_snd_of_le_map_inl (by simpa only [A] using hXA)
      rw [isZeroSum_iff] at hXsum
      simpa [hXsum, add_assoc, add_comm, add_left_comm] using hVsnd
    have hHYle : h ::ₘ Y.map Prod.snd ≤ h ::ₘ T := by
      apply Multiset.cons_le_cons
      simpa [B, Function.comp_def] using Multiset.map_le_map (f := Prod.snd) hYB
    have hHYeq : h ::ₘ Y.map Prod.snd = h ::ₘ T := by
      by_contra hne
      exact hT.not_isZeroSum hHYle Multiset.cons_ne_zero hne hHYsum
    have hYmap : Y.map Prod.snd = T := by simpa using hHYeq
    have hYBeq : Y = B := by
      apply Multiset.eq_of_le_of_card_le hYB
      simpa [B] using (congrArg Multiset.card hYmap).ge
    apply hVne
    congr 1
    rw [← hdecomp, hXAeq, hYBeq]
    exact Multiset.add_comm B A
  · exact isZeroSumFree_iff.mp hUfree ((Multiset.le_cons_of_notMem hp).mp hVU) hV0 hVsum

end Multiset
