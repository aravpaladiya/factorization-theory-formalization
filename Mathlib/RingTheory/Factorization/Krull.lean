/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Mathlib.RingTheory.Factorization.DivisorTheory.ClassGroup
public import Mathlib.RingTheory.Factorization.Monoid

import Mathlib.RingTheory.Factorization.DivisorTheory.Finite
import Mathlib.RingTheory.Factorization.DivisorTheory.Unique

/-!
# Krull monoids

This file defines the chosen-presentation convenience layer for Krull monoids. Results about a
fixed presentation live in the `DivisorTheory` modules; this layer selects a presentation only
when no explicit divisor theory is supplied.

## Main definitions

* `KrullMonoid α`: a cancellative nontrivial commutative monoid with zero admitting a divisor
  theory.
* `KrullMonoid.chooseDivisorTheory α`: a divisor theory selected by classical choice.
* `KrullMonoid.ClassGroup α`: the class group of that selected theory.

## Main results

* `KrullMonoid.toFiniteFactorizationMonoid`: a Krull monoid has finite factorization.
* `KrullMonoid.uniqueFactorizationMonoid_of_classGroup_subsingleton`: triviality of the chosen
  class group gives unique factorization.
* `UniqueFactorizationMonoid.krullMonoid`: every nontrivial UFM is a Krull monoid.
-/

public section

assert_not_exists Ideal

universe u

variable {α : Type u}

section Krull

variable [CommMonoidWithZero α]

variable (α) in
/-- A Krull monoid is a nontrivial cancellative commutative monoid with zero admitting a
divisor theory. This is the with-zero form of Definition 2.4.1 of Geroldinger and Halter-Koch.
The class group is defined from an explicit divisor theory; `KrullMonoid.ClassGroup` uses a
theory selected by classical choice. -/
@[mk_iff] class KrullMonoid : Prop extends IsCancelMulZero α, Nontrivial α where
  /-- A Krull monoid admits a divisor theory, over some type of prime divisors. -/
  exists_divisorTheory : ∃ P : Type u, Nonempty (DivisorTheory α P)

attribute [instance 100] KrullMonoid.toIsCancelMulZero KrullMonoid.toNontrivial

namespace KrullMonoid

variable (α) [KrullMonoid α]

/-- A type of prime divisors selected from `KrullMonoid.exists_divisorTheory` by classical
choice. -/
def ChoosePrimeDivisors : Type u :=
  (exists_divisorTheory (α := α)).choose

/-- A divisor theory selected from `KrullMonoid.exists_divisorTheory` by classical choice. -/
noncomputable def chooseDivisorTheory : DivisorTheory α (ChoosePrimeDivisors α) :=
  (exists_divisorTheory (α := α)).choose_spec.some

/-- The class group attached to `KrullMonoid.chooseDivisorTheory α`. -/
abbrev ClassGroup : Type u :=
  (chooseDivisorTheory α).ClassGroup

end KrullMonoid

end Krull

section Consequences

variable [CommMonoidWithZero α]

-- see Note [lower instance priority]
/-- A Krull monoid is a finite factorization monoid. Through the factorization hierarchy this
also gives `BoundedFactorizationMonoid`, `WfDvdMonoid` and `AtomicMonoid`. -/
instance (priority := 100) KrullMonoid.toFiniteFactorizationMonoid
    [KrullMonoid α] : FiniteFactorizationMonoid α :=
  (KrullMonoid.chooseDivisorTheory α).finiteFactorizationMonoid

/-- A Krull monoid with trivial chosen class group is a unique factorization monoid. -/
theorem KrullMonoid.uniqueFactorizationMonoid_of_classGroup_subsingleton [KrullMonoid α]
    (h : Subsingleton (KrullMonoid.ClassGroup α)) : UniqueFactorizationMonoid α :=
  (KrullMonoid.chooseDivisorTheory α).uniqueFactorizationMonoid_of_classGroup_subsingleton h

/-- A unique factorization monoid is a Krull monoid, with divisor theory the factorization
into primes; the class group of this canonical divisor theory is trivial by
`UniqueFactorizationMonoid.divisorTheory_classGroup_subsingleton`. The `Nontrivial`
hypothesis is necessary because the trivial monoid admits no zero-preserving homomorphism to
the nontrivial zero-adjoined free divisor monoid. -/
theorem UniqueFactorizationMonoid.krullMonoid [Nontrivial α]
    [UniqueFactorizationMonoid α] : KrullMonoid α := by
  refine
    { exists_divisorTheory :=
        ⟨{p : Associates α // Irreducible p},
          ⟨UniqueFactorizationMonoid.divisorTheory⟩⟩ }

end Consequences
