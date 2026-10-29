module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Range

@[expose] public section

assert_not_exists Real Complex

open scoped BigOperators

namespace Salem

/-- The computable rational cosine Taylor polynomial used in the real majorant. -/
def rationalCosineLowerPolynomial (x : ℚ) : ℚ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

/-- A computable rational version of the proved real radius potential bound. -/
def rationalRadiusPotentialBound (a : ℚ) (n : ℕ) : ℚ :=
  let c := rationalCosineLowerPolynomial ((3927 / 1250 : ℚ) * a)
  let z := (1 - c) / (1 + c)
  4 * ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1) +
    4 * z ^ (2 * n + 1) / (1 - z ^ 2)

/-- Rounding upward to an integer number of `1/S` units gives a computable common-denominator budget. -/
def rationalPotentialBudget (a : ℚ) (n S : ℕ) : ℚ :=
  (⌈rationalRadiusPotentialBound a n * (S : ℚ)⌉ : ℚ) / (S : ℚ)

end Salem
