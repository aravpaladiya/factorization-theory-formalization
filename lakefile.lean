import Lake

open Lake DSL

abbrev factorizationLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`autoImplicit, false⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.header, true⟩,
  ⟨`weak.linter.style.longFile, .ofNat 1500⟩,
]

package factorizationTheory where
  version := v!"0.1.0"
  description := "Non-unique factorization theory in Lean, built on top of mathlib."
  keywords := #["factorization", "commutative algebra", "Lean", "mathlib"]
  license := "Apache-2.0"
  fixedToolchain := true

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "ce084ccd34fcf5e2b486381cece9035df94b0dc1"

@[default_target]
lean_lib FactorizationTheory where
  globs := #[`FactorizationTheory.*]
  leanOptions := factorizationLeanOptions
