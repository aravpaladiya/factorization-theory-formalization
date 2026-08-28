# Factorization Theory Formalization

[![CI](https://github.com/aravpaladiya/factorization-theory-formalization/actions/workflows/ci.yml/badge.svg)](https://github.com/aravpaladiya/factorization-theory-formalization/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

This repository formalizes non-unique factorization theory in Lean, built on top of
[mathlib](https://github.com/leanprover-community/mathlib4).

Factorization theory asks how badly factorization into irreducibles can fail to be unique in a
commutative monoid, and measures the failure through invariants: sets of lengths, elasticity,
delta sets. Its central method reduces these questions, via transfer homomorphisms, to
combinatorial questions about zero-sum sequences over an abelian group (the block monoid), where
tools like the Davenport constant take over. This repository develops that pipeline formally,
end to end: formal factorizations and the arithmetic hierarchy of monoids, the length invariants,
transfer and divisor homomorphisms with their preservation theorems, zero-sum theory and block
monoids, explicit divisor theories, and generic Krull monoids. It is an independent project and
is not part of the mathlib distribution.

The repository is a standalone Lake package with mathlib as a dependency. Files written as
candidates for eventual contribution to mathlib live under the project prefix
`FactorizationTheory/Mathlib/`, and the path after that prefix is the file's intended location
upstream: for example, `FactorizationTheory/Mathlib/RingTheory/Factorization/BlockMonoid/Basic.lean`
is written for `Mathlib/RingTheory/Factorization/BlockMonoid/Basic.lean`. The prefix keeps the
package's module names from colliding with the mathlib dependency while making each file's
intended upstream home explicit.

## Status

The committed Lean declarations are proof-complete: no proof uses `sorry` or `admit`, and the
project declares no additional axioms. The development currently spans about 30 modules and
260 theorem-level declarations. The API is still evolving and may change as portions are
prepared for upstream review.

For now, the repository focuses on the generic factorization foundation. Specializations to
Dedekind domains, ideal class groups, number fields, and Carlitz or analytic results will be
added later.

## Highlights

- **Davenport constants**: `AddMonoid.davenportConstant`, with the exact value for finite
  cyclic groups and lower bounds for products.
- **Half-factorial supports**: relative block monoids over an arbitrary support set, with the
  combinatorial form of Carlitz's criterion: the full support of a finite abelian group is
  half-factorial exactly when the group has order at most two.
- **Transfer theorems**: transfer homomorphisms preserve factorization lengths, sets of
  lengths, and elasticity, formalizing the reduction that drives the subject.
- **Krull monoids**: the generic hierarchy, including unique factorization for Krull monoids
  with trivial divisor class group and the converse construction of a divisor theory for
  unique factorization monoids.

Definitions are stated for commutative monoids in the generality the theory supports, with
with-zero specializations where ring-theoretic applications will want them; block monoids are
developed relative to arbitrary supports so that subset and full-support results are instances
of one theory.

## Contents

| Area | Modules | Highlights |
| --- | --- | --- |
| Formal factorizations | `Factorization/Basic`, `Factorization/Unique` | Factorization multisets, evaluation, length fibers, and uniqueness |
| Factorization hierarchy | `Factorization/Monoid`, `Factorization/UniqueFactorizationMonoid` | Atomic, bounded-, finite-, half-, and unique-factorization monoids |
| Length invariants | `Lengths`, `Elasticity`, `Delta`, `UnionOfLengths` | Sets of lengths, elasticity, delta sets, and unions of lengths |
| Additive combinatorics | `ZeroSum`, `DavenportConstant` | Zero-sum sequences and Davenport constants, including product and cyclic results |
| Morphisms | `DivisorHom`, `Transfer/*` | Divisor and transfer homomorphisms and preservation results |
| Block monoids | `BlockMonoid/*` | Relative block monoids, atoms, finiteness, elasticity, and half-factorial supports |
| Divisor theories | `DivisorTheory/*` | Explicit divisor theories, divisor class groups, and factorization consequences |
| Krull monoids | `Factorization/Krull` | Generic Krull hierarchy and chosen divisor-theory conveniences |

The package-level module [`FactorizationTheory.lean`](FactorizationTheory.lean) imports the full
public API. Individual modules can be imported directly for a smaller dependency surface.

## Getting started

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/aravpaladiya/factorization-theory-formalization.git
cd factorization-theory-formalization
lake exe cache get
lake build
```

To run the same warning-as-error build used by CI:

```bash
lake build --wfail
```

Use the full package with:

```lean
import FactorizationTheory
```

or import a focused module, for example:

```lean
import FactorizationTheory.Mathlib.RingTheory.Factorization.BlockMonoid.Finite
```

## Compatibility and reproducibility

The project is pinned to Lean `v4.34.0-rc2` and mathlib commit
`ce084ccd34fcf5e2b486381cece9035df94b0dc1`. The generated `lake-manifest.json` is committed so
fresh clones resolve the same dependency graph.

Because the tree under `FactorizationTheory/Mathlib` mirrors mathlib's own organization,
updating the mathlib pin carries one maintenance duty: check whether upstream has since gained
files at the mirrored paths, and remove or migrate any local file whose upstream counterpart now
exists.

## Upstreaming

The project is being prepared for incremental contribution to mathlib. The current priority is
the generic factorization foundation; algebraic-number-theory and Carlitz-oriented layers will
be added later.

## Reference

The main mathematical reference is:

> Alfred Geroldinger and Franz Halter-Koch, *Non-Unique Factorizations: Algebraic,
> Combinatorial and Analytic Theory*, Chapman & Hall/CRC, 1st edition, 2006.
> [doi:10.1201/9781420003208](https://doi.org/10.1201/9781420003208)

Bibliographic metadata is also available in [`docs/references.bib`](docs/references.bib).

## Citation

If you use this formalization, please cite the repository using
[`CITATION.cff`](CITATION.cff). GitHub exposes the same metadata through its **Cite this
repository** menu.

## License

This project is released under the [Apache License 2.0](LICENSE).
