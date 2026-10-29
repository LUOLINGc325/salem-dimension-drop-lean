module

public import Salem.P2GreenForcing
public import Salem.P2Neutral
public import Salem.MirrorAction

@[expose] public section

namespace Salem

/-- The actual P₂ seed has the source's monic integer recurrence forcing. -/
theorem p2GreenSeedCoordinate_quarticResidual (j : ℤ) :
    quarticResidual 1 (-2) 1 (-2) p2GreenSeedCoordinate j =
      (p2GreenSeedForcing j : ℝ) := by
  have h := p2GreenSeedCoordinate_forcing j
  simp only [quarticResidual, reciprocalQuarticOperator] at h ⊢
  norm_num at h ⊢
  linarith

/-- The entire incoming tail uses the actual unshifted seed coefficient. -/
theorem p2GreenSeedCoordinate_expanding_left (j : ℤ) (hj : j < 0) :
    p2GreenSeedCoordinate j =
      p2GreenSeedLeftCoefficient * p2CoefficientBeta ^ j := by
  let n : ℕ := (-j-1).toNat
  have hjn : j = -((n+1 : ℕ) : ℤ) := by dsimp [n]; omega
  rw [hjn, p2GreenSeedCoordinate_left_tail]
  congr 1
  simp only [p2CoefficientR, zpow_neg, zpow_natCast, inv_pow]

/-- The literal expanding parameter satisfies the exact real P₂ equation. -/
theorem p2CoefficientBeta_scalar_equation :
    p2CoefficientBeta ^ 4 - 2 * p2CoefficientBeta ^ 3 +
      p2CoefficientBeta ^ 2 - 2 * p2CoefficientBeta + 1 = 0 := by
  have h := congrArg Complex.re (p2GreenRoot_scalar_equation 0)
  norm_num [p2GreenRoot, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, ← Complex.ofReal_add] at h
  exact h

/-- Actual integer forcing restores the Fourier orbit congruence of the seed. -/
theorem p2GreenSeedCoordinate_congruent_expanding (j : ℤ) :
    ∃ m : ℤ, p2GreenSeedCoordinate j -
      p2GreenSeedLeftCoefficient * p2CoefficientBeta ^ j = m := by
  have hb : p2CoefficientBeta ≠ 0 := by
    have h := p2CoefficientBeta_lower
    linarith
  apply quartic_forcing_global_congruent_expanding 1 (-2) 1 (-2)
    p2CoefficientBeta p2GreenSeedLeftCoefficient hb
  · norm_num
    nlinarith [p2CoefficientBeta_scalar_equation]
  · exact p2GreenSeedCoordinate_expanding_left
  · intro t _ht
    exact ⟨p2GreenSeedForcing t, p2GreenSeedCoordinate_quarticResidual t⟩

/-- The appendix's literal odd direct difference, with no padding shift. -/
noncomputable def p2GreenFinalCoordinate (j : ℤ) : ℝ :=
  p2GreenSeedCoordinate j - p2GreenSeedCoordinate (j - 1846082221)

/-- The final Fourier orbit has the actual coefficient already bounded away from zero. -/
theorem p2GreenFinalCoordinate_congruent_expanding (j : ℤ) :
    ∃ m : ℤ, p2GreenFinalCoordinate j -
      p2GreenFinalLeftCoefficient * p2CoefficientBeta ^ j = m := by
  have hb : p2CoefficientBeta ≠ 0 := by
    have h := p2CoefficientBeta_lower
    linarith
  have h := mirrorDifference_congruent_expanding
    p2CoefficientBeta p2GreenSeedLeftCoefficient hb p2GreenSeedCoordinate 1846082221
    p2GreenSeedCoordinate_congruent_expanding j
  simpa only [Nat.cast_ofNat, mirrorDifference, p2GreenFinalCoordinate,
    p2GreenFinalLeftCoefficient, p2CoefficientR, mul_comm p2GreenSeedLeftCoefficient] using h

/-- The final incoming mode is exact at every negative index. -/
theorem p2GreenFinalCoordinate_expanding_left (j : ℤ) (hj : j < 0) :
    p2GreenFinalCoordinate j =
      p2GreenFinalLeftCoefficient * p2CoefficientBeta ^ j := by
  have hb : p2CoefficientBeta ≠ 0 := by
    have h := p2CoefficientBeta_lower
    linarith
  rw [p2GreenFinalCoordinate, p2GreenSeedCoordinate_expanding_left j hj,
    p2GreenSeedCoordinate_expanding_left (j-1846082221) (by omega)]
  have h := expanding_mirror_difference
    p2CoefficientBeta p2GreenSeedLeftCoefficient hb 1846082221 j
  simpa only [Nat.cast_ofNat, p2GreenFinalLeftCoefficient, p2CoefficientR,
    mul_comm p2GreenSeedLeftCoefficient] using h

/-- The actual seed's two outgoing modes use the already certified neutral coefficient. -/
theorem p2GreenSeedCoordinate_right_modes (j : ℤ) (hj : 2885 ≤ j) :
    p2GreenSeedCoordinate j =
      p2GreenSeedRightCoefficient * p2CoefficientR ^ (j-2885).toNat +
        2 * (p2GreenSeedNeutralCoefficient * p2CoefficientZeta ^ j).re := by
  let n : ℕ := (j-2885).toNat
  have hn : (n : ℤ) = j-2885 := by dsimp [n]; omega
  have hjn : j = 2885 + (n : ℤ) := by omega
  have h := p2GreenSeedCoordinate_right_tail n
  rw [hjn]
  have he : (2885 : ℤ) + (n : ℤ) = ((2885+n : ℕ) : ℤ) := by omega
  rw [he] at h ⊢
  simpa only [p2GreenSeedNeutralCoefficient, zpow_natCast,
    show (((2885+n : ℕ) : ℤ)-2885).toNat = n by omega] using h

/-- The delayed outgoing neutral mode is exactly the source's final γ. -/
theorem p2GreenFinalNeutralCoefficient_mode (j : ℤ) :
    (p2GreenSeedNeutralCoefficient * p2CoefficientZeta ^ j).re -
      (p2GreenSeedNeutralCoefficient * p2CoefficientZeta ^ (j-1846082221)).re =
        (p2GreenFinalNeutralCoefficient * p2CoefficientZeta ^ j).re := by
  have hz : p2CoefficientZeta ≠ 0 := by
    intro h
    have hn := p2CoefficientZeta_unit.1
    rw [h, norm_zero] at hn
    norm_num at hn
  have h := neutralMode_mirror_difference p2GreenSeedNeutralCoefficient
    p2CoefficientZeta hz 1846082221 j
  simpa only [neutralMode, mirrorNeutralCoefficient, zpow_neg, zpow_ofNat, ← inv_pow,
    p2GreenFinalNeutralCoefficient, mul_comm p2GreenSeedNeutralCoefficient] using h

/-- Both actual final outgoing modes start at the source endpoint ℓ+L. -/
theorem p2GreenFinalCoordinate_right_modes (j : ℤ) (hj : 1846085106 ≤ j) :
    p2GreenFinalCoordinate j =
      p2GreenFinalRightCoefficient * p2CoefficientR ^ (j-1846085106).toNat +
        2 * (p2GreenFinalNeutralCoefficient * p2CoefficientZeta ^ j).re := by
  rw [p2GreenFinalCoordinate, p2GreenSeedCoordinate_right_modes j (by omega),
    p2GreenSeedCoordinate_right_modes (j-1846082221) (by omega)]
  have he1 : (j-2885).toNat = 1846082221 + (j-1846085106).toNat := by omega
  have he2 : (j-1846082221-2885).toNat = (j-1846085106).toNat := by omega
  rw [he1, he2, pow_add]
  have h := p2GreenFinalNeutralCoefficient_mode j
  dsimp only [p2GreenFinalRightCoefficient]
  nlinarith

/-- The final trajectory keeps the exact two shifted integer forcing cores. -/
theorem p2GreenFinalCoordinate_quarticResidual (j : ℤ) :
    quarticResidual 1 (-2) 1 (-2) p2GreenFinalCoordinate j =
      ((p2GreenSeedForcing j - p2GreenSeedForcing (j-1846082221) : ℤ) : ℝ) := by
  change quarticResidual 1 (-2) 1 (-2)
    (mirrorDifference p2GreenSeedCoordinate 1846082221) j = _
  rw [quarticResidual_mirrorDifference, p2GreenSeedCoordinate_quarticResidual,
    p2GreenSeedCoordinate_quarticResidual, Int.cast_sub]

theorem p2GreenFinalCoordinate_integer_forcing (j : ℤ) :
    ∃ m : ℤ, quarticResidual 1 (-2) 1 (-2) p2GreenFinalCoordinate j = m :=
  ⟨_, p2GreenFinalCoordinate_quarticResidual j⟩

/-- The literal localized final profile removes precisely its outgoing neutral wave. -/
noncomputable def p2GreenFinalLocalizedCoordinate (j : ℤ) : ℝ :=
  if j < 1846085106 then p2GreenFinalCoordinate j else
    p2GreenFinalRightCoefficient * p2CoefficientR ^ (j-1846085106).toNat

/-- The endpoint-relative coefficient needed by the restoration theorem. -/
noncomputable def p2GreenFinalOutgoingCoefficient : ℂ :=
  2 * p2GreenFinalNeutralCoefficient * p2CoefficientZeta ^ (1846085106 : ℤ)

/-- Restoring the outgoing wave gives the actual integer-forced final trajectory. -/
theorem p2GreenFinalCoordinate_restored (j : ℤ) :
    p2GreenFinalLocalizedCoordinate j + outgoingNeutralWave
      p2GreenFinalOutgoingCoefficient p2CoefficientZeta 1846085106 j =
        p2GreenFinalCoordinate j := by
  have hz : p2CoefficientZeta ≠ 0 := by
    intro h
    have hn := p2CoefficientZeta_unit.1
    rw [h, norm_zero] at hn
    norm_num at hn
  by_cases hj : j < 1846085106
  · simp only [p2GreenFinalLocalizedCoordinate, hj, ite_true,
      outgoingNeutralWave, show ¬(1846085106 : ℤ) ≤ j by omega, ite_false, add_zero]
  · rw [p2GreenFinalCoordinate_right_modes j (by omega)]
    simp only [p2GreenFinalLocalizedCoordinate, hj, ite_false,
      outgoingNeutralWave, show (1846085106 : ℤ) ≤ j by omega, ite_true]
    congr 1
    have he : p2GreenFinalOutgoingCoefficient * p2CoefficientZeta ^ (j-1846085106) =
        2 * (p2GreenFinalNeutralCoefficient * p2CoefficientZeta ^ j) := by
      rw [p2GreenFinalOutgoingCoefficient, mul_assoc, ← zpow_add₀ hz,
        show (1846085106 : ℤ)+(j-1846085106) = j by ring]
      ring
    rw [he]
    norm_num [Complex.mul_re]

/-- Endpoint phase rotation preserves exactly the certified final amplitude. -/
theorem p2GreenFinalOutgoingCoefficient_norm :
    ‖p2GreenFinalOutgoingCoefficient‖ = p2GreenFinalNeutralAmplitude := by
  simp only [p2GreenFinalOutgoingCoefficient, norm_mul, norm_zpow,
    p2CoefficientZeta_unit.1, one_zpow, mul_one, p2GreenFinalNeutralAmplitude]
  norm_num
/-- The actual localized profile has the exact final incoming exponential. -/
theorem p2GreenFinalLocalizedCoordinate_expanding_left (j : ℤ) (hj : j < 0) :
    p2GreenFinalLocalizedCoordinate j =
      p2GreenFinalLeftCoefficient * p2CoefficientBeta ^ j := by
  rw [p2GreenFinalLocalizedCoordinate, ite_eq_left (by omega)]
  exact p2GreenFinalCoordinate_expanding_left j hj
/-- The actual localized profile has the exact outgoing stable tail. -/
theorem p2GreenFinalLocalizedCoordinate_right_tail (n : ℕ) :
    p2GreenFinalLocalizedCoordinate (1846085106+(n : ℤ)) =
      p2GreenFinalRightCoefficient * p2CoefficientR ^ n := by
  simp only [p2GreenFinalLocalizedCoordinate,
    show ¬1846085106+(n : ℤ) < 1846085106 by omega, ite_false,
    show (1846085106+(n : ℤ)-1846085106).toNat = n by omega]
/-- The true restored localized profile retains the proved global Fourier congruence. -/
theorem p2GreenFinalLocalizedCoordinate_congruent_expanding (j : ℤ) :
    ∃ m : ℤ, p2GreenFinalLocalizedCoordinate j + outgoingNeutralWave
      p2GreenFinalOutgoingCoefficient p2CoefficientZeta 1846085106 j -
        p2GreenFinalLeftCoefficient * p2CoefficientBeta ^ j = m := by
  rw [p2GreenFinalCoordinate_restored]
  exact p2GreenFinalCoordinate_congruent_expanding j

end Salem
