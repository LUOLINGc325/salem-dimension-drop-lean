module

public import Salem.Restoration

@[expose] public section

namespace Salem

/-- The unchanged source tail parameters restore an actual action up to 47.647
strictly below 47.648. -/
theorem sharp_restoration_p2_budget_lt_direct (E r d : ℝ) (hE : E ≤ 47647/1000)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 1 ≤ d) :
    E + 20 * (1105305 / 10^21 : ℝ) * (1/10^23 : ℝ) * r / (1-r) +
      10 * (1105305 / 10^21 : ℝ)^2 * (((10^26 : ℝ)+1)/2 + 1/d) < 5956/125 := by
  apply (sharp_restoration_budget_le_coarse E (1105305/10^21) (1/10^23)
    (10^26) r d (by norm_num) (by norm_num) hr0 hr hd).trans_lt
  linarith

set_option exponentiation.threshold 10000 in
/-- A kernel-checked rational power comparison preserves the frozen second
modulus even at the 47.648 restored-action threshold. -/
theorem restoration_p2_exp_modulus_lt_one_direct :
    Real.exp (5956/125 : ℝ) * (9 / (2*10^11) : ℝ)^2 < 1 := by
  apply exp_mul_sq_lt_one_of_power_comparison (9/(2*10^11)) (27183/10000) 5956 125
    (by norm_num)
  · linarith [Real.exp_one_lt_d9]
  · norm_num

/-- The direct-difference action allowance leaves the actual frozen modulus
unchanged. -/
theorem restoration_p2_modulus_gt_direct (s A : ℝ) (hs : 0 ≤ s) (hA : A ≤ 5956/125)
    (haction : Real.exp (-A) ≤ s ^ 2) : (9 / (2*10^11) : ℝ) < s := by
  apply modulus_gt_of_exp_action s (9/(2*10^11)) (5956/125) hs (by norm_num)
    restoration_p2_exp_modulus_lt_one_direct
  exact (Real.exp_le_exp.mpr (neg_le_neg hA)).trans haction

end Salem
