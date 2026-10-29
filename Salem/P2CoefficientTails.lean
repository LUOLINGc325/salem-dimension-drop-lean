module

public import Salem.CosineTail
public import Salem.P2Coefficients

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The actual preprocessing seed's two stable tails are summable and obey the
appendix budget.  This theorem has no conditional coefficient or action premise. -/
lemma p2GreenSeed_actual_tail_action :
    Summable (fun n : ℕ => cosinePotential
      (p2GreenSeedLeftCoefficient * p2CoefficientR ^ (n + 1))) ∧
    Summable (fun n : ℕ => cosinePotential
      (p2GreenSeedRightCoefficient * p2CoefficientR ^ n)) ∧
    ((∑' n : ℕ, cosinePotential (p2GreenSeedLeftCoefficient * p2CoefficientR ^ (n + 1))) +
      ∑' n : ℕ, cosinePotential (p2GreenSeedRightCoefficient * p2CoefficientR ^ n)) <
        (275 / 10 ^ 49 : ℝ) := by
  exact small_stable_tail_action p2CoefficientR_bounds.1.le p2CoefficientR_sharp
    p2GreenSeed_stable_coefficients_small.1.le p2GreenSeed_stable_coefficients_small.2.le

/-- The final odd direct difference preserves the actual stable-tail budget.
Only the 2885-core action and the direct-difference core estimate remain separate. -/
lemma p2GreenFinal_actual_tail_action :
    Summable (fun n : ℕ => cosinePotential
      (p2GreenFinalLeftCoefficient * p2CoefficientR ^ (n + 1))) ∧
    Summable (fun n : ℕ => cosinePotential
      (p2GreenFinalRightCoefficient * p2CoefficientR ^ n)) ∧
    ((∑' n : ℕ, cosinePotential (p2GreenFinalLeftCoefficient * p2CoefficientR ^ (n + 1))) +
      ∑' n : ℕ, cosinePotential (p2GreenFinalRightCoefficient * p2CoefficientR ^ n)) <
        (275 / 10 ^ 49 : ℝ) := by
  exact small_stable_tail_action p2CoefficientR_bounds.1.le p2CoefficientR_sharp
    p2GreenFinal_stable_coefficients_small.1.le p2GreenFinal_stable_coefficients_small.2.le

/-- Every actual final stable-tail coordinate is strictly centered, so none
of its cosine factors vanishes.  The finite core needs its own centering proof. -/
lemma p2GreenFinal_tail_cos_pos (n : ℕ) :
    0 < Real.cos (Real.pi * (p2GreenFinalLeftCoefficient * p2CoefficientR ^ (n + 1))) ∧
      0 < Real.cos (Real.pi * (p2GreenFinalRightCoefficient * p2CoefficientR ^ n)) := by
  have hr0 := p2CoefficientR_bounds.1.le
  have hr1 : p2CoefficientR ≤ 1 := by linarith [p2CoefficientR_bounds.2]
  have hcenter (a : ℝ) (ha : |a| ≤ (1 / 10 ^ 24 : ℝ)) (j : ℕ) :
      |a * p2CoefficientR ^ j| < (1 / 2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 _)]
    calc
      |a| * p2CoefficientR ^ j ≤ (1 / 10 ^ 24 : ℝ) * 1 :=
        mul_le_mul ha (pow_le_one₀ hr0 hr1) (pow_nonneg hr0 _) (by norm_num)
      _ < 1 / 2 := by norm_num
  exact ⟨cosinePotential_cos_pos
      (hcenter _ p2GreenFinal_stable_coefficients_small.1.le (n + 1)),
    cosinePotential_cos_pos (hcenter _ p2GreenFinal_stable_coefficients_small.2.le n)⟩

end Salem
