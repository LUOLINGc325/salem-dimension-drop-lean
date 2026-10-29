module

public import Salem.P1Analytic
public import Salem.RationalPotentialData

@[expose] public section

open scoped BigOperators

namespace Salem

theorem rationalCosineLowerPolynomial_cast (x : ℚ) :
    (rationalCosineLowerPolynomial x : ℝ) = cosineLowerPolynomial (x : ℝ) := by
  unfold rationalCosineLowerPolynomial cosineLowerPolynomial
  push_cast
  rfl

/-- The computable rational expression has exactly the same real value as the analytic majorant. -/
theorem rationalRadiusPotentialBound_cast (a : ℚ) (n : ℕ) :
    (rationalRadiusPotentialBound a n : ℝ) = radiusPotentialBound (a : ℝ) n := by
  unfold rationalRadiusPotentialBound radiusPotentialBound potentialLogSum
  push_cast
  rw [rationalCosineLowerPolynomial_cast]
  norm_num

/-- Scaling and taking the exact rational ceiling can only enlarge the potential majorant. -/
theorem rationalRadiusPotentialBound_le_budget (a : ℚ) (n : ℕ) {S : ℕ} (hS : 0 < S) :
    rationalRadiusPotentialBound a n ≤ rationalPotentialBudget a n S := by
  unfold rationalPotentialBudget
  apply (le_div_iff₀ (Nat.cast_pos.2 hS : (0 : ℚ) < S)).2
  exact Int.le_ceil _

/-- The budget bounds the actual cosine potential under the precise real-majorant hypotheses. -/
theorem cosinePotential_le_rationalPotentialBudget {a : ℚ} {t : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 43 / 100) (ht : |t| ≤ (a : ℝ))
    (n : ℕ) {S : ℕ} (hS : 0 < S) :
    cosinePotential t ≤ (rationalPotentialBudget a n S : ℝ) := by
  have hreal := cosinePotential_le_radiusPotentialBound
    (show (0 : ℝ) ≤ a by exact_mod_cast ha0)
    (show (a : ℝ) ≤ 43 / 100 by
      have h : (a : ℝ) ≤ ((43 / 100 : ℚ) : ℝ) := Rat.cast_le.2 ha
      norm_num at h ⊢
      exact h) ht n
  rw [← rationalRadiusPotentialBound_cast a n] at hreal
  exact hreal.trans (by exact_mod_cast rationalRadiusPotentialBound_le_budget a n hS)

end Salem
