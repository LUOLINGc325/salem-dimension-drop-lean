module

public import Salem.P1Analytic

@[expose] public section

namespace Salem

/-- The positive magnitude after the two actual P1 mirror updates. -/
noncomputable def p1FinalStartingCoefficientMagnitude (b : ℝ) : ℝ :=
  p1SeedStartingCoefficient b * (1 - b⁻¹ ^ 124) * (1 - b⁻¹ ^ 489637838)

/-- The signed incoming coefficient retains the negative sign of the P1 seed. -/
noncomputable def p1FinalStartingCoefficient (b : ℝ) : ℝ :=
  -p1SeedStartingCoefficient b * (1 - b⁻¹ ^ 124) * (1 - b⁻¹ ^ 489637838)

theorem p1FinalStartingCoefficient_eq_neg_magnitude (b : ℝ) :
    p1FinalStartingCoefficient b = -p1FinalStartingCoefficientMagnitude b := by
  unfold p1FinalStartingCoefficient p1FinalStartingCoefficientMagnitude
  ring

/-- Both mirror factors are bounded without expanding their large powers. -/
theorem p1IncomingFactor_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 5)
    {L : ℕ} (hL : 2 ≤ L) : (1 / 2 : ℝ) < 1 - r ^ L ∧ 1 - r ^ L ≤ 1 := by
  have hr1 : r ≤ 1 := hr.trans (by norm_num)
  have hpow : r ^ L ≤ (3 / 5 : ℝ) ^ 2 :=
    (pow_le_pow_of_le_one hr0 hr1 hL).trans (pow_le_pow_left₀ hr0 hr 2)
  norm_num at hpow
  constructor
  · linarith
  · linarith [pow_nonneg hr0 L]

/-- The actual root and seed-coefficient bounds give a fixed positive final magnitude. -/
theorem p1FinalStartingCoefficientMagnitude_bounds {b : ℝ}
    (hb : (5 / 3 : ℝ) ≤ b) (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (1 / 1000 : ℝ) < p1FinalStartingCoefficientMagnitude b ∧
      p1FinalStartingCoefficientMagnitude b < 1 := by
  have hi := p1_expanding_root_interval hb hroot
  have hh := p1SeedStartingCoefficient_bounds hi.1.le hi.2.le
  have hhpos : 0 < p1SeedStartingCoefficient b := lt_of_lt_of_le (by norm_num) hh.1
  have hbl : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hr0 : 0 ≤ b⁻¹ := inv_nonneg.2 hbl.le
  have hr : b⁻¹ ≤ 3 / 5 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 3) hb
    norm_num [one_div] at h ⊢
    exact h
  have hfirst := p1IncomingFactor_bounds hr0 hr (L := 124) (by norm_num)
  have hsecond := p1IncomingFactor_bounds hr0 hr (L := 489637838) (by norm_num)
  have hfpos : 0 < 1 - b⁻¹ ^ 124 := lt_trans (by norm_num) hfirst.1
  have hlower : p1SeedStartingCoefficient b / 4 <
      p1FinalStartingCoefficientMagnitude b := by
    unfold p1FinalStartingCoefficientMagnitude
    calc
      _ = p1SeedStartingCoefficient b * (1 / 2) * (1 / 2) := by ring
      _ < (p1SeedStartingCoefficient b * (1 - b⁻¹ ^ 124)) * (1 / 2) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hfirst.1 hhpos) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hsecond.1 (mul_pos hhpos hfpos)
  have hupper : p1FinalStartingCoefficientMagnitude b ≤ p1SeedStartingCoefficient b := by
    unfold p1FinalStartingCoefficientMagnitude
    calc
      _ ≤ p1SeedStartingCoefficient b * (1 - b⁻¹ ^ 124) :=
        mul_le_of_le_one_right (mul_nonneg hhpos.le hfpos.le) hsecond.2
      _ ≤ _ := mul_le_of_le_one_right hhpos.le hfirst.2
  constructor
  · have hcoarse : (1 / 1000 : ℝ) < p1SeedStartingCoefficient b / 4 := by linarith [hh.1]
    exact hcoarse.trans hlower
  · exact hupper.trans_lt (lt_of_le_of_lt hh.2 (by norm_num))

theorem p1FinalStartingCoefficientMagnitude_pos {b : ℝ}
    (hb : (5 / 3 : ℝ) ≤ b) (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    0 < p1FinalStartingCoefficientMagnitude b :=
  lt_trans (by norm_num) (p1FinalStartingCoefficientMagnitude_bounds hb hroot).1

theorem abs_p1FinalStartingCoefficient {b : ℝ}
    (hb : (5 / 3 : ℝ) ≤ b) (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    |p1FinalStartingCoefficient b| = p1FinalStartingCoefficientMagnitude b := by
  rw [p1FinalStartingCoefficient_eq_neg_magnitude, abs_neg,
    abs_of_pos (p1FinalStartingCoefficientMagnitude_pos hb hroot)]

theorem p1FinalStartingCoefficient_neg {b : ℝ}
    (hb : (5 / 3 : ℝ) ≤ b) (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    p1FinalStartingCoefficient b < 0 := by
  rw [p1FinalStartingCoefficient_eq_neg_magnitude]
  exact neg_neg_of_pos (p1FinalStartingCoefficientMagnitude_pos hb hroot)

/-- The genuine finite-frequency coefficient bounds for the twice-mirrored P1 profile. -/
theorem p1FinalStartingCoefficient_bounds {b : ℝ}
    (hb : (5 / 3 : ℝ) ≤ b) (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (2 : ℝ) ^ (-112 : ℤ) < |p1FinalStartingCoefficient b| ∧
      |p1FinalStartingCoefficient b| < 1 := by
  rw [abs_p1FinalStartingCoefficient hb hroot]
  have h := p1FinalStartingCoefficientMagnitude_bounds hb hroot
  exact ⟨(by norm_num : (2 : ℝ) ^ (-112 : ℤ) < 1 / 1000).trans h.1, h.2⟩

end Salem
