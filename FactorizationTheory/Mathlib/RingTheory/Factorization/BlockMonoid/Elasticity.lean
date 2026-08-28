/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import FactorizationTheory.Mathlib.Combinatorics.Additive.DavenportConstant
public import FactorizationTheory.Mathlib.RingTheory.Factorization.BlockMonoid.Basic
public import FactorizationTheory.Mathlib.RingTheory.Factorization.Elasticity

import Mathlib.Algebra.BigOperators.Ring.Multiset
import FactorizationTheory.Mathlib.RingTheory.Factorization.BlockMonoid.Finite

/-!
# Elasticity of full block monoids

For a finite additive commutative group `G` of order at least two, the elasticity of its full
block monoid is half its Davenport constant.

## Main results

* `BlockMonoid.monoid_elasticity_eq_davenportConstant_div_two`: `ρ(B(G)) = D(G) / 2` for
  `2 ≤ Nat.card G`.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Ideal

open AddMonoid
open scoped ENNReal

universe u

variable {G : Type u} [AddCommGroup G]

namespace BlockMonoid

private noncomputable local instance : DecidableEq G := Classical.decEq G

-- Count `0` twice so that the exceptional atom `{0}` has weight `2`; atoms not containing
-- `0` have weight equal to their sequence length.
private noncomputable def weight (a : BlockMonoid G) : ℕ :=
  if ha : a = 0 then 0 else
    let S := Classical.choose (BlockMonoidOver.ne_zero_iff_exists_of.mp ha)
    (S : Multiset G).card + (S : Multiset G).count 0

private theorem weight_of (S : blockMonoid G) :
    weight (BlockMonoidOver.of S) =
      (S : Multiset G).card + (S : Multiset G).count 0 := by
  rw [weight, dite_eq_right (BlockMonoidOver.of_ne_zero S)]
  let T := Classical.choose
    (BlockMonoidOver.ne_zero_iff_exists_of.mp (BlockMonoidOver.of_ne_zero S))
  have hT : BlockMonoidOver.of T = BlockMonoidOver.of S := Classical.choose_spec
    (BlockMonoidOver.ne_zero_iff_exists_of.mp (BlockMonoidOver.of_ne_zero S))
  have hTS : T = S := BlockMonoidOver.of_injective hT
  simp [T, hTS]

private theorem weight_mul (a b : BlockMonoid G) (ha : a ≠ 0) (hb : b ≠ 0) :
    weight (a * b) = weight a + weight b := by
  obtain ⟨S, rfl⟩ := BlockMonoidOver.ne_zero_iff_exists_of.mp ha
  obtain ⟨T, rfl⟩ := BlockMonoidOver.ne_zero_iff_exists_of.mp hb
  rw [← BlockMonoidOver.of_add, weight_of, weight_of, weight_of]
  simp only [AddSubmonoid.coe_add, Multiset.card_add, Multiset.count_add]
  omega

private theorem weight_prod (f : Multiset (BlockMonoid G))
    (hf : ∀ a ∈ f, a ≠ 0) : weight f.prod = (f.map weight).sum := by
  induction f using Multiset.induction_on with
  | empty =>
    change weight (1 : BlockMonoid G) = 0
    rw [← BlockMonoidOver.of_zero, weight_of]
    simp
  | @cons a f ih =>
    rw [Multiset.prod_cons, weight_mul]
    · simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih]
      exact fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb)
    · exact hf a (Multiset.mem_cons_self a f)
    · exact Multiset.prod_ne_zero fun h ↦
        (hf 0 (Multiset.mem_cons.mpr (Or.inr h))) rfl

private theorem irreducible_weight_bounds [Nontrivial G] {d : ℕ}
    (hD : (d : ℕ∞) = davenportConstant G) {a : BlockMonoid G}
    (ha : Irreducible a) : 2 ≤ weight a ∧ weight a ≤ d := by
  obtain ⟨S, hS, rfl⟩ := BlockMonoidOver.exists_isMinimalZeroSum_of_irreducible ha
  rw [weight_of]
  by_cases hzero : (0 : G) ∈ (S : Multiset G)
  · have hSeq := hS.eq_singleton_of_zero_mem hzero
    rw [hSeq]
    simp only [Multiset.card_singleton, Multiset.count_singleton_self]
    constructor
    · omega
    · have hDtwo : (2 : ℕ∞) ≤ d := hD ▸ two_le_davenportConstant (G := G)
      exact ENat.natCast_le_natCast.mp hDtwo
  · rw [Multiset.count_eq_zero.mpr hzero, add_zero]
    have hcard_ne_one : (S : Multiset G).card ≠ 1 := by
      intro hcard
      obtain ⟨g, hg⟩ := Multiset.card_eq_one.mp hcard
      have hg0 : g = 0 := by
        rw [hg] at hS
        exact Multiset.isZeroSum_singleton.mp hS.isZeroSum
      apply hzero
      rw [hg, hg0]
      exact Multiset.mem_singleton_self (0 : G)
    constructor
    · have hpos := hS.card_pos
      omega
    · apply ENat.natCast_le_natCast.mp
      rw [hD]
      exact hS.card_le_davenportConstant

private theorem multiset_weight_bounds [Nontrivial G] {d : ℕ}
    (hD : (d : ℕ∞) = davenportConstant G) (g : Multiset (BlockMonoid G))
    (hgI : ∀ a ∈ g, Irreducible a) :
    2 * g.card ≤ (g.map weight).sum ∧ (g.map weight).sum ≤ d * g.card := by
  induction g using Multiset.induction_on with
  | empty => simp
  | @cons a g ih =>
    have haI : Irreducible a := hgI a (Multiset.mem_cons_self a g)
    have haBounds := irreducible_weight_bounds hD haI
    have ih' := ih fun b hb ↦ hgI b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    constructor
    · omega
    · rw [Nat.mul_add, Nat.mul_one]
      omega

private theorem factorization_weight_bounds [Nontrivial G] {d : ℕ}
    (hD : (d : ℕ∞) = davenportConstant G) (S : blockMonoid G)
    {f : Associates.Factorization (BlockMonoid G)}
    (hf : f ∈ factorizations (BlockMonoidOver.of S)) :
    2 * f.card ≤ (S : Multiset G).card + (S : Multiset G).count 0 ∧
      (S : Multiset G).card + (S : Multiset G).count 0 ≤ d * f.card := by
  obtain ⟨g, hgI, hgprod, hgf⟩ := exists_multiset_of_mem_factorizations hf
  have hgprod' : g.prod = BlockMonoidOver.of S := associated_iff_eq.mp hgprod
  have hweight : (g.map weight).sum =
      (S : Multiset G).card + (S : Multiset G).count 0 := by
    rw [← weight_prod g (fun a ha ↦ (hgI a ha).ne_zero), hgprod', weight_of]
  have hbounds := multiset_weight_bounds hD g hgI
  have hcard : f.card = g.card := by
    rw [← hgf, Associates.Factorization.card_ofMultiset]
  rw [hcard, ← hweight]
  exact hbounds

private theorem elasticity_le_davenport_div_two [Nontrivial G] {d : ℕ}
    (hD : (d : ℕ∞) = davenportConstant G) {a : BlockMonoid G}
    (ha : a ≠ 0) (hnu : ¬IsUnit a) :
    _root_.elasticity a ≤ (d : ℝ≥0∞) / 2 := by
  obtain ⟨S, rfl⟩ := BlockMonoidOver.ne_zero_iff_exists_of.mp ha
  have hne := nonempty_factorizationLengths (a := BlockMonoidOver.of S)
    (BlockMonoidOver.of_ne_zero S)
  have hbdd := BoundedFactorizationMonoid.bddAbove_factorizationLengths
    (a := BlockMonoidOver.of S) (BlockMonoidOver.of_ne_zero S)
  obtain ⟨m, hm, hmmax⟩ := exists_natCast_eq_maxFactorizationLength hne hbdd
  obtain ⟨n, hn, hnmin⟩ := exists_natCast_eq_minFactorizationLength hne
  obtain ⟨fm, hfm, hfmcard⟩ := mem_factorizationLengths.mp hm
  obtain ⟨fn, hfn, hfncard⟩ := mem_factorizationLengths.mp hn
  have hwm := (factorization_weight_bounds hD S hfm).1
  have hwn := (factorization_weight_bounds hD S hfn).2
  have hmn : 2 * m ≤ d * n := by
    rw [hfmcard] at hwm
    rw [hfncard] at hwn
    exact hwm.trans hwn
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hnu
    exact zero_mem_factorizationLengths_iff.mp (hn0 ▸ hn)
  rw [_root_.elasticity_def, ite_eq_right hnu, ← hmmax, ← hnmin]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp [hn0])) (Or.inl (by simp))]
  have hrhs : (d : ℝ≥0∞) / 2 * ((n : ℕ∞) : ℝ≥0∞) =
      ((d : ℝ≥0∞) * ((n : ℕ∞) : ℝ≥0∞)) / 2 := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hrhs, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  exact_mod_cast (by simpa [mul_comm] using hmn)

private def negBlock (S : blockMonoid G) : blockMonoid G :=
  ⟨(S : Multiset G).map (fun g ↦ -g),
    mem_blockMonoid.mpr <| by
      simpa using (mem_blockMonoid.mp S.property).map (AddEquiv.neg G).toAddMonoidHom⟩

private theorem negBlock_minimal {S : blockMonoid G}
    (hS : (S : Multiset G).IsMinimalZeroSum) :
    ((negBlock S : blockMonoid G) : Multiset G).IsMinimalZeroSum := by
  simpa [negBlock] using hS.map_addEquiv (AddEquiv.neg G)

private def pairBlock (g : G) : blockMonoid G :=
  ⟨{g, -g}, mem_blockMonoid.mpr <| by rw [Multiset.isZeroSum_iff]; simp⟩

private theorem pairBlock_minimal {g : G} (hg : g ≠ 0) :
    ((pairBlock g : blockMonoid G) : Multiset G).IsMinimalZeroSum := by
  have hfree : ({g} : Multiset G).IsZeroSumFree :=
    Multiset.isZeroSumFree_singleton.mpr hg
  have hmin := hfree.isMinimalZeroSum_cons_neg_sum
  simp only [Multiset.sum_singleton] at hmin
  change (-g ::ₘ g ::ₘ 0).IsMinimalZeroSum at hmin
  rw [Multiset.cons_swap] at hmin
  change (g ::ₘ -g ::ₘ 0).IsMinimalZeroSum
  exact hmin

private def symmBlock (S : Multiset G) : blockMonoid G :=
  ⟨S + S.map (fun g ↦ -g),
    mem_blockMonoid.mpr <| by
      rw [Multiset.isZeroSum_iff, Multiset.sum_add, Multiset.sum_map_neg]
      rw [Multiset.map_id', add_neg_cancel]⟩

private theorem prod_pairBlocks (S : Multiset G) :
    (S.map fun g ↦ BlockMonoidOver.of (pairBlock g)).prod =
      BlockMonoidOver.of (symmBlock S) := by
  induction S using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, ← BlockMonoidOver.of_zero]
    exact congrArg BlockMonoidOver.of (Subtype.ext (by simp [symmBlock]))
  | @cons g S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← BlockMonoidOver.of_add]
    apply congrArg BlockMonoidOver.of
    apply Subtype.ext
    rw [AddSubmonoid.coe_add]
    change
      ({g, -g} : Multiset G) + (S + S.map (fun g ↦ -g)) =
        (g ::ₘ S) + (g ::ₘ S).map (fun g ↦ -g)
    rw [Multiset.map_cons]
    simp only [← Multiset.singleton_add]
    ac_rfl

private theorem two_atom_product (S : blockMonoid G) :
    (Multiset.cons (BlockMonoidOver.of S)
      {BlockMonoidOver.of (negBlock S)}).prod =
        BlockMonoidOver.of (symmBlock (S : Multiset G)) := by
  simp only [Multiset.prod_cons, Multiset.prod_singleton]
  rw [← BlockMonoidOver.of_add]
  exact congrArg BlockMonoidOver.of (Subtype.ext rfl)

/-- The elasticity of the full block monoid is half the Davenport constant. The lower-cardinality
hypothesis excludes the trivial group, whose block monoid has elasticity `1`. -/
theorem monoid_elasticity_eq_davenportConstant_div_two [Finite G]
    (hG : 2 ≤ Nat.card G) :
    Monoid.elasticity (BlockMonoid G) = (davenportConstant G : ℝ≥0∞) / 2 := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa [Nat.card_eq_fintype_card] using (show 1 < Nat.card G by omega))
  obtain ⟨d, hD⟩ := ENat.ne_top_iff_exists.mp (davenportConstant_lt_top (G := G)).ne
  have hD' : (d : ℝ≥0∞) = (davenportConstant G : ℝ≥0∞) := by
    exact congrArg ENat.toENNReal hD
  rw [← hD']
  have hd : 2 ≤ d := by
    apply ENat.natCast_le_natCast.mp
    rw [hD]
    exact two_le_davenportConstant (G := G)
  apply le_antisymm
  · rw [Monoid.elasticity_def]
    -- Every atom has weight between `2` and `D(G)`, which bounds every factorization ratio.
    refine sup_le ?_ <| iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun hnu ↦
      elasticity_le_davenport_div_two hD ha hnu
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
    exact_mod_cast hd
  · obtain ⟨S, hS, hScardD⟩ :=
      exists_isMinimalZeroSum_card_eq_davenportConstant_of_ne_top
        (davenportConstant_lt_top (G := G)).ne
    -- The symmetric block `S + (-S)` factors into `S` and `-S`, and also into the pair
    -- blocks `{g, -g}` indexed by the terms of `S`.
    have hScard : S.card = d := by
      apply ENat.natCast_inj.mp
      exact hScardD.trans hD.symm
    have hzero : (0 : G) ∉ S := by
      intro h0
      have hSeq := hS.eq_singleton_of_zero_mem h0
      have hc := congrArg Multiset.card hSeq
      simp only [Multiset.card_singleton] at hc
      omega
    let Sb : blockMonoid G := ⟨S, mem_blockMonoid.mpr hS.isZeroSum⟩
    let a : BlockMonoid G := BlockMonoidOver.of (symmBlock S)
    let f₂ : Multiset (BlockMonoid G) :=
      {BlockMonoidOver.of Sb, BlockMonoidOver.of (negBlock Sb)}
    have hf₂I : ∀ b ∈ f₂, Irreducible b := by
      intro b hb
      dsimp [f₂] at hb
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact BlockMonoidOver.irreducible_of_iff.mpr hS
      · subst b
        exact BlockMonoidOver.irreducible_of_iff.mpr (negBlock_minimal hS)
    have hf₂ : Associates.Factorization.ofMultiset f₂ hf₂I ∈ factorizations a := by
      apply ofMultiset_mem_factorizations hf₂I
      apply Associated.of_eq
      exact two_atom_product Sb
    have hlen₂ : 2 ∈ factorizationLengths a := by
      have hmem := card_mem_factorizationLengths hf₂
      simpa [f₂, Associates.Factorization.card_ofMultiset] using hmem
    let fp : Multiset (BlockMonoid G) :=
      S.map fun g ↦ BlockMonoidOver.of (pairBlock g)
    have hfpI : ∀ b ∈ fp, Irreducible b := by
      intro b hb
      obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hb
      apply BlockMonoidOver.irreducible_of_iff.mpr
      exact pairBlock_minimal fun hg0 ↦ hzero (hg0 ▸ hg)
    have hfp : Associates.Factorization.ofMultiset fp hfpI ∈ factorizations a := by
      apply ofMultiset_mem_factorizations hfpI
      exact Associated.of_eq (prod_pairBlocks S)
    have hlend : d ∈ factorizationLengths a := by
      have hmem := card_mem_factorizationLengths hfp
      simpa [fp, Associates.Factorization.card_ofMultiset, hScard] using hmem
    have hsymm0 : (symmBlock S : blockMonoid G) ≠ 0 := by
      intro hs
      have hsv := congrArg Subtype.val hs
      change S + S.map (fun g ↦ -g) = 0 at hsv
      have hc := congrArg Multiset.card hsv
      simp only [Multiset.card_add, Multiset.card_map, Multiset.card_zero] at hc
      have hSpos := hS.card_pos
      omega
    have hanu : ¬IsUnit a := by
      rw [BlockMonoidOver.isUnit_iff]
      change BlockMonoidOver.of (symmBlock S) ≠ 1
      exact fun h ↦ hsymm0 (BlockMonoidOver.of_eq_one_iff.mp h)
    have hdmax : (d : ℕ∞) ≤ maxFactorizationLength a := by
      rw [maxFactorizationLength_def]
      exact le_sSup ⟨d, hlend, rfl⟩
    have hmin₂ : minFactorizationLength a ≤ (2 : ℕ∞) := by
      rw [minFactorizationLength_def]
      exact sInf_le ⟨2, hlen₂, rfl⟩
    calc
      (d : ℝ≥0∞) / 2 ≤ _root_.elasticity a := by
        rw [_root_.elasticity_def, ite_eq_right hanu]
        exact ENNReal.div_le_div (ENat.toENNReal_le.mpr hdmax)
          (ENat.toENNReal_le.mpr hmin₂)
      _ ≤ Monoid.elasticity (BlockMonoid G) :=
        Monoid.le_elasticity (BlockMonoidOver.of_ne_zero _)

end BlockMonoid
