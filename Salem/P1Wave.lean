module

public import Salem.P1Returns
public import Salem.GreenKernel

@[expose] public section

namespace Salem

theorem p1NeutralRoot_ne_zero : p1NeutralRoot ≠ 0 := by
  intro h
  have hn := p1NeutralRoot_norm
  rw [h, norm_zero] at hn
  norm_num at hn

theorem p1NeutralRoot_star_eq_inv : star p1NeutralRoot = p1NeutralRoot⁻¹ :=
  (Complex.inv_eq_conj p1NeutralRoot_norm).symm

/-- The actual derivative residue of the P1 neutral root. -/
noncomputable def p1NeutralResidue : ℂ :=
  (reciprocalQuarticDerivativeValue (1 : ℂ) (-1) p1NeutralRoot)⁻¹

theorem p1NeutralResidue_eq : p1NeutralResidue =
    (4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1)⁻¹ := by
  unfold p1NeutralResidue
  congr 1
  unfold reciprocalQuarticDerivativeValue
  ring

/-- Reciprocity of the actual neutral derivative fixes its phase. -/
theorem p1NeutralResidue_star :
    star p1NeutralResidue = -p1NeutralRoot ^ 2 * p1NeutralResidue := by
  have hroot : p1NeutralRoot ^ 4 - (1 : ℂ) * p1NeutralRoot ^ 3 +
      (-1 : ℂ) * p1NeutralRoot ^ 2 - 1 * p1NeutralRoot + 1 = 0 := by
    simpa [sub_eq_add_neg] using p1NeutralRoot_quartic
  have hs : star (reciprocalQuarticDerivativeValue (1 : ℂ) (-1) p1NeutralRoot) =
      reciprocalQuarticDerivativeValue (1 : ℂ) (-1) p1NeutralRoot⁻¹ := by
    simp [reciprocalQuarticDerivativeValue, p1NeutralRoot_star_eq_inv]
  unfold p1NeutralResidue
  rw [star_inv₀, hs]
  exact reciprocalQuartic_inverse_derivative_inv p1NeutralRoot_ne_zero hroot

theorem p1SeedNeutralCoefficient_eq_residue :
    p1SeedNeutralCoefficient = p1NeutralResidue * (p1NeutralRoot + 1 + p1NeutralRoot⁻¹) ^ 3 := by
  rw [p1NeutralResidue_eq]
  rfl

/-- The Laurent forcing multiplier is real at the actual unit-circle root. -/
theorem p1SeedNeutralMultiplier_real :
    p1NeutralRoot + 1 + p1NeutralRoot⁻¹ = ((1 + 2 * p1NeutralRoot.re : ℝ) : ℂ) := by
  calc
    _ = (p1NeutralRoot + p1NeutralRoot⁻¹) + 1 := by ring
    _ = _ := by rw [p1NeutralRoot_trace]; push_cast; ring

/-- The actual seed mode has the precise phase needed for reflection about index two. -/
theorem p1SeedNeutralCoefficient_star :
    star p1SeedNeutralCoefficient = -p1NeutralRoot ^ 2 * p1SeedNeutralCoefficient := by
  have hreal : star (p1NeutralRoot + 1 + p1NeutralRoot⁻¹) =
      p1NeutralRoot + 1 + p1NeutralRoot⁻¹ := by
    rw [p1SeedNeutralMultiplier_real]
    simp
  rw [p1SeedNeutralCoefficient_eq_residue, star_mul, star_pow, hreal, p1NeutralResidue_star]
  ring

/-- The real two-conjugate wave, in the physical source indexing. -/
noncomputable def neutralModeWave (z C : ℂ) (t : ℤ) : ℝ :=
  2 * (C * z ^ (t - 1)).re

theorem abs_neutralModeWave_le {z : ℂ} (hz : ‖z‖ = 1) (C : ℂ) (t : ℤ) :
    |neutralModeWave z C t| ≤ 2 * ‖C‖ := by
  unfold neutralModeWave
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ‖C * z ^ (t - 1)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = _ := by rw [norm_mul, norm_zpow, hz, one_zpow, mul_one]

/-- The phase equation alone gives the exact antisymmetry at source reflection index four. -/
theorem neutralModeWave_reflection {z C : ℂ} (hz : ‖z‖ = 1)
    (hC : star C = -z ^ 2 * C) (t : ℤ) :
    neutralModeWave z C (4 - t) = -neutralModeWave z C t := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  have hstar : star z = z⁻¹ := (Complex.inv_eq_conj hz).symm
  have hpow : z ^ 2 * z ^ (-(t - 1)) = z ^ ((4 - t) - 1) := by
    rw [show z ^ 2 = z ^ (2 : ℤ) by norm_num, ← zpow_add₀ hz0]
    congr 1
    omega
  have heq : star (C * z ^ (t - 1)) = -(C * z ^ ((4 - t) - 1)) := by
    rw [star_mul, star_zpow₀, hstar, inv_zpow', hC]
    calc
      _ = -C * (z ^ 2 * z ^ (-(t - 1))) := by ring
      _ = _ := by rw [hpow]; ring
  have hre := congrArg Complex.re heq
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hre
  unfold neutralModeWave
  linarith

/-- The actual seed wave. -/
noncomputable def p1SeedNeutralWave (t : ℤ) : ℝ :=
  neutralModeWave p1NeutralRoot p1SeedNeutralCoefficient t

theorem abs_p1SeedNeutralWave_le (t : ℤ) :
    |p1SeedNeutralWave t| ≤ 2 * ‖p1SeedNeutralCoefficient‖ :=
  abs_neutralModeWave_le p1NeutralRoot_norm p1SeedNeutralCoefficient t

theorem p1SeedNeutralWave_reflection (t : ℤ) : p1SeedNeutralWave (4 - t) = -p1SeedNeutralWave t :=
  neutralModeWave_reflection p1NeutralRoot_norm p1SeedNeutralCoefficient_star t

/-- The unforced Green wave uses the same root and its actual derivative residue. -/
noncomputable def p1GreenNeutralWave (t : ℤ) : ℝ :=
  neutralModeWave p1NeutralRoot p1NeutralResidue t

theorem abs_p1GreenNeutralWave_le (t : ℤ) : |p1GreenNeutralWave t| ≤ 2 * ‖p1NeutralResidue‖ :=
  abs_neutralModeWave_le p1NeutralRoot_norm p1NeutralResidue t

theorem p1GreenNeutralWave_reflection (t : ℤ) :
    p1GreenNeutralWave (4 - t) = -p1GreenNeutralWave t :=
  neutralModeWave_reflection p1NeutralRoot_norm p1NeutralResidue_star t

/-- The actual neutral-root separation has the exact source normalization. -/
theorem p1NeutralRoot_norm_one_sub_sq : ‖1 - p1NeutralRoot ^ 2‖ = 2 * p1NeutralRoot.im := by
  have hprod : p1NeutralRoot * star p1NeutralRoot = 1 := by
    calc
      _ = (Complex.normSq p1NeutralRoot : ℂ) := Complex.mul_conj p1NeutralRoot
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, p1NeutralRoot_norm]; norm_num
  have heq : 1 - p1NeutralRoot ^ 2 = p1NeutralRoot * (star p1NeutralRoot - p1NeutralRoot) := by
    rw [mul_sub, hprod]
    ring
  have hdiff : star p1NeutralRoot - p1NeutralRoot =
      ((-2 * p1NeutralRoot.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
    ring
  have him : 0 ≤ p1NeutralRoot.im := by linarith [p1NeutralRoot_im_bounds.1]
  rw [heq, norm_mul, p1NeutralRoot_norm, one_mul, hdiff, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_nonpos (by linarith : -2 * p1NeutralRoot.im ≤ 0)]
  ring

theorem p1NeutralRoot_norm_one_sub_sq_gt_three_halves :
    (3 / 2 : ℝ) < ‖1 - p1NeutralRoot ^ 2‖ := by
  rw [p1NeutralRoot_norm_one_sub_sq]
  linarith [p1NeutralRoot_im_bounds.1]

end Salem
