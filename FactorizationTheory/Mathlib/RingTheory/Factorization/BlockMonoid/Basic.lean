/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import FactorizationTheory.Mathlib.Combinatorics.Additive.ZeroSum
public import FactorizationTheory.Mathlib.RingTheory.Factorization.DivisorHom

import FactorizationTheory.Mathlib.Algebra.GroupWithZero.WithZero.CancelMulZero

/-!
# Relative block monoids

For a subset `G₀` of an additive commutative monoid `G`, the block monoid over `G₀`
consists of the zero-sum multisets supported on `G₀`. The relative construction is primary;
the full block monoid is its specialization to `Set.univ`.

This file packages block monoids as commutative monoids with zero, develops their constructor,
cardinality, unit, and inclusion APIs, and identifies their atoms with supported minimal zero-sum
sequences. Inclusions of supports are divisor homomorphisms and preserve and reflect atoms.

## Main definitions

* `blockMonoidOver G₀` and `BlockMonoidOver G₀` are the additive and zero-adjoined
  multiplicative forms of the relative block monoid.
* `BlockMonoidOver.of` embeds a supported zero-sum sequence as a nonzero block.
* `BlockMonoidOver.inclusion` is induced by an inclusion of supporting subsets.
* `BlockMonoidOver.atomEquiv` identifies supported minimal zero-sum sequences with irreducible
  associate classes.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

universe u

variable {G : Type u} [AddCommMonoid G]

/-! ### Supported zero-sum sequences -/

/-- The additive monoid of zero-sum multisets supported on `G₀`. -/
def blockMonoidOver (G₀ : Set G) : AddSubmonoid (Multiset G) where
  carrier := {S | S.IsZeroSum ∧ ∀ g ∈ S, g ∈ G₀}
  add_mem' := fun hS hT ↦
    ⟨hS.1.add hT.1, fun g hg ↦ (Multiset.mem_add.mp hg).elim (hS.2 g) (hT.2 g)⟩
  zero_mem' := ⟨Multiset.isZeroSum_zero, fun g hg ↦ absurd hg (Multiset.notMem_zero g)⟩

@[simp]
theorem mem_blockMonoidOver {G₀ : Set G} {S : Multiset G} :
    S ∈ blockMonoidOver G₀ ↔ S.IsZeroSum ∧ ∀ g ∈ S, g ∈ G₀ := by
  rfl

theorem blockMonoidOver_mono {G₀ G₁ : Set G} (h : G₀ ⊆ G₁) :
    blockMonoidOver G₀ ≤ blockMonoidOver G₁ :=
  fun _ hS ↦ ⟨hS.1, fun g hg ↦ h (hS.2 g hg)⟩

variable (G) in
/-- The full additive block monoid, definitionally the relative construction over `Set.univ`. -/
abbrev blockMonoid : AddSubmonoid (Multiset G) :=
  blockMonoidOver (Set.univ : Set G)

theorem mem_blockMonoid {S : Multiset G} : S ∈ blockMonoid G ↔ S.IsZeroSum := by
  simp [blockMonoid]

/-! ### Blocks as a monoid with zero -/

/-- The block monoid over `G₀`, formed by adjoining zero after turning multiset concatenation
into multiplication. -/
@[expose] def BlockMonoidOver (G₀ : Set G) : Type u :=
  WithZero (Multiplicative (blockMonoidOver G₀))

variable (G) in
/-- The full block monoid, definitionally the relative construction over `Set.univ`. -/
abbrev BlockMonoid : Type u :=
  BlockMonoidOver (Set.univ : Set G)

namespace BlockMonoidOver

variable {G₀ : Set G}

instance : CommMonoidWithZero (BlockMonoidOver G₀) :=
  inferInstanceAs (CommMonoidWithZero (WithZero (Multiplicative (blockMonoidOver G₀))))

instance : Nontrivial (BlockMonoidOver G₀) :=
  inferInstanceAs (Nontrivial (WithZero (Multiplicative (blockMonoidOver G₀))))

instance : IsCancelMulZero (BlockMonoidOver G₀) :=
  inferInstanceAs (IsCancelMulZero (WithZero (Multiplicative (blockMonoidOver G₀))))

/-- A supported zero-sum sequence as a nonzero block. -/
def of (S : blockMonoidOver G₀) : BlockMonoidOver G₀ :=
  WithZero.coe (Multiplicative.ofAdd S)

@[simp]
theorem of_ne_zero (S : blockMonoidOver G₀) : of S ≠ 0 :=
  WithZero.coe_ne_zero

@[simp]
theorem of_zero : of (0 : blockMonoidOver G₀) = 1 := by
  rfl

@[simp]
theorem of_add (S T : blockMonoidOver G₀) : of (S + T) = of S * of T := by
  rfl

theorem of_injective : Function.Injective (of : blockMonoidOver G₀ → BlockMonoidOver G₀) :=
  fun _ _ h ↦ Multiplicative.ofAdd.injective (WithZero.coe_injective h)

@[simp]
theorem of_eq_one_iff {S : blockMonoidOver G₀} : of S = 1 ↔ S = 0 := by
  constructor
  · intro h
    exact of_injective (h.trans of_zero.symm)
  · rintro rfl
    exact of_zero

/-- A block is nonzero exactly when it comes from a supported zero-sum sequence. -/
theorem ne_zero_iff_exists_of {a : BlockMonoidOver G₀} :
    a ≠ 0 ↔ ∃ S : blockMonoidOver G₀, of S = a := by
  constructor
  · intro ha
    obtain ⟨S, hS⟩ := WithZero.ne_zero_iff_exists.mp ha
    exact ⟨Multiplicative.toAdd S, hS⟩
  · rintro ⟨S, rfl⟩
    exact of_ne_zero S

/-! ### Divisibility -/

/-- Divisibility between constructed blocks is multiset containment. -/
theorem of_dvd_of_iff (S T : blockMonoidOver G₀) :
    of S ∣ of T ↔ (S : Multiset G) ≤ (T : Multiset G) := by
  constructor
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, mul_zero] at ha
      exact of_ne_zero T ha
    obtain ⟨U, rfl⟩ := ne_zero_iff_exists_of.mp ha0
    apply Multiset.le_iff_exists_add.mpr
    refine ⟨(U : Multiset G), ?_⟩
    have h := of_injective (ha.trans (of_add S U).symm)
    exact congrArg Subtype.val h
  · intro hST
    obtain ⟨U, hU⟩ := Multiset.le_iff_exists_add.mp hST
    have hUz : U.IsZeroSum := by
      apply Multiset.IsZeroSum.of_add_left (S := (S : Multiset G))
      · simpa [← hU] using T.property.1
      · exact S.property.1
    have hUs : ∀ g ∈ U, g ∈ G₀ := by
      intro g hg
      apply T.property.2 g
      rw [hU]
      exact Multiset.mem_add.mpr (Or.inr hg)
    let U' : blockMonoidOver G₀ := ⟨U, hUz, hUs⟩
    refine ⟨of U', ?_⟩
    rw [← of_add]
    exact congrArg of (Subtype.ext (by simpa [U'] using hU))

/-! ### Cardinality and units -/

/-- The number of terms in a block, defined to be `0` at the adjoined zero. -/
def card (a : BlockMonoidOver G₀) : ℕ :=
  WithZero.recZeroCoe 0
    (fun S ↦ ((Multiplicative.toAdd S : blockMonoidOver G₀) : Multiset G).card) a

@[simp]
theorem card_zero : card (0 : BlockMonoidOver G₀) = 0 := by
  rfl

@[simp]
theorem card_of (S : blockMonoidOver G₀) : card (of S) = (S : Multiset G).card := by
  rfl

@[simp]
theorem card_one : card (1 : BlockMonoidOver G₀) = 0 := by
  rw [← of_zero, card_of]
  rfl

theorem card_mul (a b : BlockMonoidOver G₀) (ha : a ≠ 0) (hb : b ≠ 0) :
    card (a * b) = card a + card b := by
  induction a using WithZero.recZeroCoe with
  | zero => exact (ha rfl).elim
  | coe S =>
    induction b using WithZero.recZeroCoe with
    | zero => exact (hb rfl).elim
    | coe T => exact Multiset.card_add _ _

/-- A block is a unit exactly when it is the empty sequence; block monoids are reduced. -/
theorem isUnit_iff {a : BlockMonoidOver G₀} : IsUnit a ↔ a = 1 := by
  constructor
  · intro ha
    obtain ⟨S, rfl⟩ := ne_zero_iff_exists_of.mp ha.ne_zero
    rw [of_eq_one_iff]
    apply Subtype.ext
    apply Multiset.le_zero.mp
    apply (of_dvd_of_iff S 0).mp
    rw [of_zero]
    exact isUnit_iff_dvd_one.mp ha
  · rintro rfl
    exact isUnit_one

/-- The only unit in a block monoid is `1`. -/
instance instSubsingletonUnits : Subsingleton (BlockMonoidOver G₀)ˣ :=
  Subsingleton.units_of_isUnit fun _ ↦ isUnit_iff.mp

/-! ### Inclusions of supports -/

/-- The block-monoid homomorphism induced by an inclusion of supporting subsets. -/
def inclusion {G₀ G₁ : Set G} (h : G₀ ⊆ G₁) :
    BlockMonoidOver G₀ →*₀ BlockMonoidOver G₁ :=
  WithZero.map'
    (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion (blockMonoidOver_mono h)))

@[simp]
theorem inclusion_of {G₀ G₁ : Set G} (h : G₀ ⊆ G₁) (S : blockMonoidOver G₀) :
    inclusion h (of S) = of (AddSubmonoid.inclusion (blockMonoidOver_mono h) S) := by
  rfl

theorem inclusion_injective {G₀ G₁ : Set G} (h : G₀ ⊆ G₁) :
    Function.Injective (inclusion h) := by
  change Function.Injective
    (WithZero.map'
      (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion (blockMonoidOver_mono h))))
  rw [WithZero.map'_injective_iff]
  intro S T hST
  change AddSubmonoid.inclusion (blockMonoidOver_mono h) (Multiplicative.toAdd S) =
    AddSubmonoid.inclusion (blockMonoidOver_mono h) (Multiplicative.toAdd T) at hST
  exact Multiplicative.toAdd.injective (AddSubmonoid.inclusion_injective _ hST)

/-- Every divisor of an included nonzero block is itself the inclusion of a divisor. -/
theorem exists_dvd_of_dvd_inclusion {G₀ G₁ : Set G} (h : G₀ ⊆ G₁)
    {a : BlockMonoidOver G₀} (ha : a ≠ 0) {b : BlockMonoidOver G₁}
    (hb : b ∣ inclusion h a) :
    ∃ c : BlockMonoidOver G₀, c ∣ a ∧ inclusion h c = b := by
  have hia : inclusion h a ≠ 0 := by
    intro hzero
    apply ha
    exact inclusion_injective h (by simpa using hzero)
  have hb0 : b ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ := hb
    rw [hzero, zero_mul] at hc
    exact hia hc
  obtain ⟨A, rfl⟩ := ne_zero_iff_exists_of.mp ha
  obtain ⟨B, rfl⟩ := ne_zero_iff_exists_of.mp hb0
  rw [inclusion_of, of_dvd_of_iff] at hb
  have hBA : (B : Multiset G) ≤ (A : Multiset G) := by
    simpa using hb
  let B₀ : blockMonoidOver G₀ :=
    ⟨B, B.property.1, fun g hg ↦ A.property.2 g (Multiset.mem_of_le hBA hg)⟩
  refine ⟨of B₀, of_dvd_of_iff B₀ A |>.mpr ?_, ?_⟩
  · exact hBA
  · rw [inclusion_of]
    exact congrArg (of : blockMonoidOver G₁ → BlockMonoidOver G₁) (Subtype.ext rfl)

/-- Inclusion of supporting subsets is a divisor homomorphism. -/
theorem isDivisorHom_inclusion {G₀ G₁ : Set G} (h : G₀ ⊆ G₁) :
    IsDivisorHom (inclusion h) := by
  rw [isDivisorHom_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst b
    exact dvd_zero a
  obtain ⟨c, hc, hca⟩ := exists_dvd_of_dvd_inclusion h hb hab
  have : c = a := inclusion_injective h hca
  simpa [this] using hc

/-- Inclusion of supporting subsets preserves and reflects divisibility. -/
theorem inclusion_dvd_iff {G₀ G₁ : Set G} (h : G₀ ⊆ G₁)
    {a b : BlockMonoidOver G₀} : inclusion h a ∣ inclusion h b ↔ a ∣ b :=
  (isDivisorHom_inclusion h).map_dvd_iff

@[simp]
theorem card_inclusion {G₀ G₁ : Set G} (h : G₀ ⊆ G₁) (a : BlockMonoidOver G₀) :
    card (inclusion h a) = card a := by
  induction a using WithZero.recZeroCoe <;> rfl

/-! ### Atoms -/

/-- A constructed block is irreducible exactly when its sequence is minimal zero-sum. -/
theorem irreducible_of_iff {S : blockMonoidOver G₀} :
    Irreducible (of S) ↔ (S : Multiset G).IsMinimalZeroSum := by
  constructor
  · intro hS
    -- A proper nonempty zero-sum subsequence gives a factorization into two nonunits.
    rw [Multiset.isMinimalZeroSum_iff]
    refine ⟨S.property.1, ?_, ?_⟩
    · intro h
      apply hS.not_isUnit
      rw [isUnit_iff, of_eq_one_iff]
      exact Subtype.ext h
    · intro T hTS hT0 hTne hTz
      have hTs : ∀ g ∈ T, g ∈ G₀ := by
        intro g hg
        exact S.property.2 g (Multiset.mem_of_le hTS hg)
      let T' : blockMonoidOver G₀ := ⟨T, hTz, hTs⟩
      obtain ⟨U, hU⟩ := Multiset.le_iff_exists_add.mp hTS
      have hUz : U.IsZeroSum := by
        apply Multiset.IsZeroSum.of_add_left (S := T)
        · simpa [← hU] using S.property.1
        · exact hTz
      have hUs : ∀ g ∈ U, g ∈ G₀ := by
        intro g hg
        apply S.property.2 g
        rw [hU]
        exact Multiset.mem_add.mpr (Or.inr hg)
      let U' : blockMonoidOver G₀ := ⟨U, hUz, hUs⟩
      have hfac : of S = of T' * of U' := by
        rw [← of_add]
        exact congrArg of (Subtype.ext hU)
      rcases hS.isUnit_or_isUnit hfac with hunit | hunit
      · rw [isUnit_iff, of_eq_one_iff] at hunit
        exact hT0 (congrArg Subtype.val hunit)
      · rw [isUnit_iff, of_eq_one_iff] at hunit
        have hU0 : U = 0 := by simpa [U'] using congrArg Subtype.val hunit
        exact hTne (by simp [hU, hU0])
  · intro hS
    -- Conversely, a factorization into two nonunits gives a proper zero-sum subsequence.
    refine ⟨?_, ?_⟩
    · rw [isUnit_iff, of_eq_one_iff]
      exact fun h ↦ hS.ne_zero (congrArg Subtype.val h)
    · intro a b hab
      have ha0 : a ≠ 0 := by
        intro ha
        rw [ha, zero_mul] at hab
        exact of_ne_zero S hab
      have hb0 : b ≠ 0 := by
        intro hb
        rw [hb, mul_zero] at hab
        exact of_ne_zero S hab
      obtain ⟨T, rfl⟩ := ne_zero_iff_exists_of.mp ha0
      obtain ⟨U, rfl⟩ := ne_zero_iff_exists_of.mp hb0
      have hST : (S : Multiset G) = (T : Multiset G) + (U : Multiset G) :=
        congrArg Subtype.val (of_injective (hab.trans (of_add T U).symm))
      by_cases hT : (T : Multiset G) = 0
      · left
        rw [isUnit_iff, of_eq_one_iff]
        exact Subtype.ext hT
      by_cases hU : (U : Multiset G) = 0
      · right
        rw [isUnit_iff, of_eq_one_iff]
        exact Subtype.ext hU
      exfalso
      apply hS.not_isZeroSum (T := (T : Multiset G))
        (Multiset.le_iff_exists_add.mpr ⟨(U : Multiset G), hST⟩) hT
      · intro hEq
        exact hU (by simpa using hEq.trans hST)
      · exact T.property.1

/-- Inclusion of supporting subsets preserves irreducible blocks. -/
theorem irreducible_inclusion {G₀ G₁ : Set G} (h : G₀ ⊆ G₁)
    {a : BlockMonoidOver G₀} (ha : Irreducible a) : Irreducible (inclusion h a) := by
  obtain ⟨S, rfl⟩ := ne_zero_iff_exists_of.mp ha.ne_zero
  rw [inclusion_of, irreducible_of_iff]
  simpa using irreducible_of_iff.mp ha

/-- Inclusion of supporting subsets preserves and reflects irreducible blocks. -/
theorem irreducible_inclusion_iff {G₀ G₁ : Set G} (h : G₀ ⊆ G₁)
    {a : BlockMonoidOver G₀} :
    Irreducible (inclusion h a) ↔ Irreducible a :=
  ⟨(isDivisorHom_inclusion h).irreducible_of_map, irreducible_inclusion h⟩

/-- Every irreducible block comes from a supported minimal zero-sum sequence. -/
theorem exists_isMinimalZeroSum_of_irreducible {a : BlockMonoidOver G₀} (ha : Irreducible a) :
    ∃ S : blockMonoidOver G₀, (S : Multiset G).IsMinimalZeroSum ∧ a = of S := by
  obtain ⟨S, rfl⟩ := ne_zero_iff_exists_of.mp ha.ne_zero
  exact ⟨S, irreducible_of_iff.mp ha, rfl⟩

/-- Supported minimal zero-sum sequences correspond to irreducible associate classes. -/
noncomputable def atomEquiv :
    {S : blockMonoidOver G₀ // (S : Multiset G).IsMinimalZeroSum} ≃
      {p : Associates (BlockMonoidOver G₀) // Irreducible p} := by
  let f : {S : blockMonoidOver G₀ // (S : Multiset G).IsMinimalZeroSum} →
      {p : Associates (BlockMonoidOver G₀) // Irreducible p} :=
    fun S ↦
      ⟨Associates.mk (of S.1), Associates.irreducible_mk.mpr (irreducible_of_iff.mpr S.2)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro S T hST
    apply Subtype.ext
    apply of_injective
    apply Associates.mk_injective
    exact congrArg Subtype.val hST
  · rintro ⟨p, hp⟩
    obtain ⟨a, ha⟩ := Associates.exists_rep p
    have haI : Irreducible a := Associates.irreducible_mk.mp (by simpa [ha] using hp)
    obtain ⟨S, hS, rfl⟩ := exists_isMinimalZeroSum_of_irreducible haI
    refine ⟨⟨S, hS⟩, ?_⟩
    exact Subtype.ext ha

@[simp]
theorem coe_atomEquiv
    (S : {S : blockMonoidOver G₀ // (S : Multiset G).IsMinimalZeroSum}) :
    (atomEquiv S : Associates (BlockMonoidOver G₀)) = Associates.mk (of S.1) := by
  rfl

@[simp]
theorem coe_atomEquiv_symm_apply
    (p : {p : Associates (BlockMonoidOver G₀) // Irreducible p}) :
    Associates.mk (of (atomEquiv.symm p).1) = p.1 := by
  simpa only [coe_atomEquiv] using
    congrArg Subtype.val (atomEquiv.apply_symm_apply p)

end BlockMonoidOver
