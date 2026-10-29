module

public import Salem.QuarticClassificationCore

@[expose] public section

namespace Salem.QuarticCore

/-! Exact rational root and logarithm bounds for the canonical quartic radicals. -/

/-- A rational upper bound for the first explicit quartic Salem parameter. -/
lemma beta1_lt_173_div_100 : beta1 < (173 / 100 : ℝ) := by
  let u : ℝ := (1 + Real.sqrt 13) / 2
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
  have hslt : (Real.sqrt 13 : ℝ) < 361 / 100 := by nlinarith
  have hu : u < 461 / 200 := by dsimp [u]; linarith
  have hupos : 0 ≤ u := by dsimp [u]; positivity
  have hrad : 0 ≤ u ^ 2 - 4 := by dsimp [u]; nlinarith
  have hv : 0 ≤ Real.sqrt (u ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlt : Real.sqrt (u ^ 2 - 4) < 231 / 200 := by nlinarith
  change (u + Real.sqrt (u ^ 2 - 4)) / 2 < 173 / 100
  linarith

/-- A rational upper bound for the second explicit quartic Salem parameter. -/
lemma beta2_lt_189_div_100 : beta2 < (189 / 100 : ℝ) := by
  let u : ℝ := 1 + Real.sqrt 2
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hslt : (Real.sqrt 2 : ℝ) < 283 / 200 := by nlinarith
  have hu : u < 483 / 200 := by dsimp [u]; linarith
  have hupos : 0 ≤ u := by dsimp [u]; positivity
  have hrad : 0 ≤ u ^ 2 - 4 := by dsimp [u]; nlinarith
  have hv : 0 ≤ Real.sqrt (u ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlt : Real.sqrt (u ^ 2 - 4) < 273 / 200 := by nlinarith
  change (u + Real.sqrt (u ^ 2 - 4)) / 2 < 189 / 100
  linarith

/-- The five-term exponential Taylor lower bound certifies the P₁ logarithm bound. -/
lemma log_beta1_lt_eleven_twentieths : Real.log beta1 < (11 / 20 : ℝ) := by
  have hexp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 20) 5
  norm_num [Finset.sum_range_succ] at hexp
  apply (Real.log_lt_iff_lt_exp (lt_trans zero_lt_one one_lt_beta1)).mpr
  linarith [beta1_lt_173_div_100]

/-- The five-term exponential Taylor lower bound certifies the P₂ logarithm bound. -/
lemma log_beta2_lt_sixteen_twentyfifths : Real.log beta2 < (16 / 25 : ℝ) := by
  have hexp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 25) 5
  norm_num [Finset.sum_range_succ] at hexp
  apply (Real.log_lt_iff_lt_exp (lt_trans zero_lt_one one_lt_beta2)).mpr
  linarith [beta2_lt_189_div_100]

end Salem.QuarticCore
