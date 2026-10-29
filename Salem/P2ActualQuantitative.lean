module

public import Salem.P2FourierOrbit
public import Salem.P2DirectBudgets
public import Salem.P2RestorationBudget
public import Salem.P2CoefficientTails
public import Salem.P2CoreCertificate
public import Salem.QuantitativeBernoulliCore

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace Salem

/-- The localized final sequence is exactly its finite core and the two
actual stable tails; no action estimate is assumed. -/
theorem p2GreenFinalLocalizedCoordinate_eq_profile :
    p2GreenFinalLocalizedCoordinate =
      localizedProfile 1846085106 (fun i : Fin 1846085106 => p2GreenFinalCoordinate i)
        (fun n => p2GreenFinalLeftCoefficient*p2CoefficientR^(n+1))
        (fun n => p2GreenFinalRightCoefficient*p2CoefficientR^n) := by
  funext j
  obtain ⟨q, rfl⟩ := (localizedProfileIndex 1846085106).surjective j
  rcases q with i | (n | n)
  · have hi : (i : ℤ) < 1846085106 := by exact_mod_cast i.isLt
    change p2GreenFinalLocalizedCoordinate (i : ℤ) = _
    rw [p2GreenFinalLocalizedCoordinate, ite_eq_left hi]
    change _ = Sum.elim _ (Sum.elim _ _) ((localizedProfileIndex 1846085106).symm
      (localizedProfileIndex 1846085106 (.inl i)))
    rw [Equiv.symm_apply_apply]
    rfl
  · change p2GreenFinalLocalizedCoordinate (-1-(n : ℤ)) = _
    rw [p2GreenFinalLocalizedCoordinate_expanding_left _ (by omega)]
    have he : (-1 : ℤ)-(n : ℤ) = -((n+1 : ℕ) : ℤ) := by omega
    rw [he]
    simp only [p2CoefficientR, zpow_neg, zpow_natCast, inv_pow]
    change _ = Sum.elim _ (Sum.elim _ _) ((localizedProfileIndex 1846085106).symm
      (localizedProfileIndex 1846085106 (.inr (.inl n))))
    rw [Equiv.symm_apply_apply]
    rfl
  · change p2GreenFinalLocalizedCoordinate (1846085106+(n : ℤ)) = _
    rw [p2GreenFinalLocalizedCoordinate_right_tail]
    change _ = Sum.elim _ (Sum.elim _ _) ((localizedProfileIndex 1846085106).symm
      (localizedProfileIndex 1846085106 (.inr (.inr n))))
    rw [Equiv.symm_apply_apply]
    rfl

/-- The actual bilateral localized action splits into its finite core and the
two summable source tails, even before the finite-core certificate is supplied. -/
theorem p2GreenFinalLocalizedCoordinate_action_hasSum :
    HasSum (fun j : ℤ => cosinePotential (p2GreenFinalLocalizedCoordinate j))
      (directCoreAction p2GreenFinalCoordinate 1846085106 +
        (∑' n : ℕ, cosinePotential (p2GreenFinalLeftCoefficient*p2CoefficientR^(n+1))) +
        (∑' n : ℕ, cosinePotential (p2GreenFinalRightCoefficient*p2CoefficientR^n))) := by
  have h := localizedProfile_action_hasSum 1846085106
    (fun i : Fin 1846085106 => p2GreenFinalCoordinate i)
    (fun n => p2GreenFinalLeftCoefficient*p2CoefficientR^(n+1))
    (fun n => p2GreenFinalRightCoefficient*p2CoefficientR^n) _ _
    p2GreenFinal_actual_tail_action.1.hasSum p2GreenFinal_actual_tail_action.2.1.hasSum
  have hc : (∑ i : Fin 1846085106, cosinePotential (p2GreenFinalCoordinate i)) =
      directCoreAction p2GreenFinalCoordinate 1846085106 := by
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => cosinePotential (p2GreenFinalCoordinate n))
      1846085106
  rw [hc, ← p2GreenFinalLocalizedCoordinate_eq_profile] at h
  exact h

/-- The actual seed right modes in the exact integer-power convention of the
direct-difference action theorem. -/
theorem p2GreenSeedCoordinate_source_right (j : ℤ) (hj : 2885 ≤ j) :
    p2GreenSeedCoordinate j =
      neutralMode (2*p2GreenSeedNeutralCoefficient) p2CoefficientZeta j +
        p2GreenSeedRightCoefficient*p2CoefficientBeta⁻¹^(j-2885) := by
  rw [p2GreenSeedCoordinate_right_modes j hj]
  have hre : neutralMode (2*p2GreenSeedNeutralCoefficient) p2CoefficientZeta j =
      2*(p2GreenSeedNeutralCoefficient*p2CoefficientZeta^j).re := by
    unfold neutralMode
    rw [mul_assoc]
    norm_num [Complex.mul_re]
  have hp : p2CoefficientBeta⁻¹^(j-2885) = p2CoefficientR^(j-2885).toNat := by
    have he : j-2885 = (((j-2885).toNat : ℕ) : ℤ) := by omega
    rw [he, zpow_natCast]
    rfl
  rw [hre, hp]
  ring

/-- The actual sign-series characteristic modulus is its real cosine expectation. -/
theorem p2_norm_charFun_eq_abs_integral_cos (t : ℝ) :
    ‖charFun (ElementaryCore.bernoulliLaw p2CoefficientBeta) t‖ =
      |∫ x, Real.cos (t*x) ∂ElementaryCore.bernoulliLaw p2CoefficientBeta| := by
  have hb : 1 < p2CoefficientBeta := by linarith [p2CoefficientBeta_lower]
  rw [charFun_bernoulliLaw_eq_tprod _ hb, integral_cos_bernoulliLaw_eq_tprod _ hb]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The explicit P₂ radical and actual four roots satisfy the cycle-free
quartic guard used by the quantitative entropy cover theorem. -/
theorem p2Actual_quartic_guard :
    QuarticCore.IsQuarticSalemNumber QuarticCore.beta2 := by
  classical
  have hmonic : p2CoefficientPolynomial.Monic := by
    dsimp [p2CoefficientPolynomial]
    monicity <;> norm_num
  have hdeg : p2CoefficientPolynomial.natDegree = 4 := by
    dsimp [p2CoefficientPolynomial]
    compute_degree!
  have hirr : Irreducible (p2CoefficientPolynomial.map (algebraMap ℤ ℚ)) := by
    apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp
    apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap ℤ (ZMod 3))
      p2CoefficientPolynomial hmonic
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have heq : p2CoefficientPolynomial.map (algebraMap ℤ (ZMod 3)) =
        Polynomial.cyclotomic 5 (ZMod 3) := by
      norm_num [p2CoefficientPolynomial, Polynomial.cyclotomic_prime, Finset.sum_range_succ]
      ext n
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one]
      split_ifs <;> simp_all [Polynomial.coeff_X] <;> decide
    rw [heq]
    apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 3) (n := 5) (by decide) dvd_rfl
    rw [Polynomial.natDegree_cyclotomic]
    symm
    apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  have hr (i : Fin 4) : (p2CoefficientPolynomial.map (algebraMap ℤ ℂ)).IsRoot (p2GreenRoot i) := by
    simpa only [algebraMap_int_eq] using p2GreenRoot_isRoot i
  change QuarticCore.IsQuarticSalemNumber p2CoefficientBeta
  refine ⟨p2CoefficientPolynomial, p2CoefficientZeta, hmonic, hdeg, hirr,
    by linarith [p2CoefficientBeta_lower], ?_, ?_, ?_, ?_, p2CoefficientZeta_unit.1,
    ne_of_gt p2CoefficientZeta_unit.2, ?_⟩
  · simpa [p2GreenRoot] using hr 0
  · simpa [p2GreenRoot, p2CoefficientR] using hr 1
  · simpa [p2GreenRoot] using hr 2
  · simpa [p2GreenRoot] using hr 3
  · intro z hz
    change (p2CoefficientPolynomial.map (Int.castRingHom ℂ)).IsRoot z at hz
    rw [p2GreenRoot_factorization] at hz
    simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hz
    obtain ⟨i, _hi, hi⟩ := Finset.prod_eq_zero_iff.mp hz
    have hi' : z = p2GreenRoot i := sub_eq_zero.mp hi
    fin_cases i
    · exact Or.inl (by simpa [p2GreenRoot] using hi')
    · exact Or.inr (Or.inl (by simpa [p2GreenRoot, p2CoefficientR] using hi'))
    · exact Or.inr (Or.inr (Or.inl (by simpa [p2GreenRoot] using hi')))
    · exact Or.inr (Or.inr (Or.inr (by simpa [p2GreenRoot] using hi')))


/-- Assembly checkpoint: the only inputs are the two fixed finite-core facts
being independently kernel-certified. Every trajectory, forcing, mode, action,
and Fourier quantity here is the actual literal P₂ construction. -/
theorem p2ActualQuantitative_of_core_certificates
    (hmax : ∀ i : Fin 2885, |p2GreenSeedCoordinate (i.val : ℤ)| ≤ (2/5 : ℝ))
    (hcore : (∑ i : Fin 2885, cosinePotential (p2GreenSeedCoordinate (i.val : ℤ))) ≤
      (4743/200 : ℝ)) :
    (Summable (fun j : ℤ => cosinePotential (p2GreenFinalLocalizedCoordinate j)) ∧
      (∑' j : ℤ, cosinePotential (p2GreenFinalLocalizedCoordinate j)) < 47647/1000 ∧
      ∀ j : ℤ, |p2GreenFinalLocalizedCoordinate j| < (1/2 : ℝ)) ∧
    (∀ n ≤ (10^26 : ℕ), (9/(2*10^11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi*|p2GreenFinalLeftCoefficient| *p2CoefficientBeta^n)*x)
        ∂ElementaryCore.bernoulliLaw p2CoefficientBeta|) ∧
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw QuarticCore.beta2 F = 1 ∧
      dimH F < ENNReal.ofReal (1-(78 : ℝ)/10^23) := by
  suffices hd :
      (Summable (fun j : ℤ => cosinePotential (p2GreenFinalLocalizedCoordinate j)) ∧
        (∑' j : ℤ, cosinePotential (p2GreenFinalLocalizedCoordinate j)) < 47647/1000 ∧
        ∀ j : ℤ, |p2GreenFinalLocalizedCoordinate j| < (1/2 : ℝ)) ∧
      ∀ n ≤ (10^26 : ℕ), (9/(2*10^11) : ℝ) ≤
        |∫ x, Real.cos ((Real.pi*|p2GreenFinalLeftCoefficient| *p2CoefficientBeta^n)*x)
          ∂ElementaryCore.bernoulliLaw p2CoefficientBeta| by
    refine ⟨hd.1, hd.2, ?_⟩
    have hc : 1/(2 : ℝ)^112 < |p2GreenFinalLeftCoefficient| := by
      simpa only [zpow_neg, zpow_ofNat, one_div] using p2GreenFinal_incoming_coefficient_bounds.1
    exact QuarticCore.exists_quantitative_beta2_cover_of_uniform_bias p2Actual_quartic_guard
      hc p2GreenFinal_incoming_coefficient_bounds.2 hd.2
  have hb : 1 < p2CoefficientBeta := by linarith [p2CoefficientBeta_lower]
  have hr0 : 0 ≤ p2CoefficientR := p2CoefficientR_bounds.1.le
  have hr : p2CoefficientR ≤ (3/5 : ℝ) := by linarith [p2CoefficientR_bounds.2]
  have hr1 : p2CoefficientR < 1 := by linarith
  have hΔ0 : 0 ≤ p2GreenSeedNeutralAmplitude := p2GreenSeedNeutralAmplitude_bounds.1.le
  have hΔ : p2GreenSeedNeutralAmplitude ≤ (4674807/10^12 : ℝ) :=
    p2GreenSeedNeutralAmplitude_bounds.2.le
  have ha : ‖2*p2GreenSeedNeutralCoefficient‖ ≤ p2GreenSeedNeutralAmplitude := by
    rw [norm_mul]
    norm_num [p2GreenSeedNeutralAmplitude]
  have hne : 1-p2CoefficientZeta^2 ≠ 0 := by
    apply norm_pos_iff.mp
    linarith [p2CoefficientZeta_gap_gt]
  have hm : |p2GreenSeedLeftCoefficient| ≤ (1/10^24 : ℝ) :=
    p2GreenSeed_stable_coefficients_small.1.le
  have hp : |p2GreenSeedRightCoefficient| ≤ (1/10^24 : ℝ) :=
    p2GreenSeed_stable_coefficients_small.2.le
  have hmax' (i : ℕ) (hi : i < 2885) : |p2GreenSeedCoordinate (i : ℤ)| ≤ (2/5 : ℝ) :=
    hmax ⟨i, hi⟩
  have hEc : directCoreAction p2GreenSeedCoordinate 2885 ≤ (4743/200 : ℝ) := by
    have he := Fin.sum_univ_eq_sum_range
      (fun n : ℕ => cosinePotential (p2GreenSeedCoordinate n)) 2885
    rw [he] at hcore
    exact hcore
  have hEc0 : 0 ≤ directCoreAction p2GreenSeedCoordinate 2885 := by
    unfold directCoreAction
    exact Finset.sum_nonneg (fun i _ => cosinePotential_nonneg _)
  have hradii := p2Direct_radii_bounds (2/5) p2GreenSeedNeutralAmplitude p2CoefficientR
    le_rfl hΔ hr0 hr
  have hmc : (2/5 : ℝ)+p2GreenSeedNeutralAmplitude+(1/10^24 : ℝ)*
      p2CoefficientBeta⁻¹^1846079336 < 1/2 := by
    change (2/5 : ℝ)+p2GreenSeedNeutralAmplitude+(1/10^24 : ℝ)*
      p2CoefficientR^1846079336 < 1/2
    linarith [hradii.1]
  have hcurv : cosineCurvatureBound ((2/5 : ℝ)+p2GreenSeedNeutralAmplitude+
      (1/10^24 : ℝ)*p2CoefficientBeta⁻¹^1846079336) ≤ 2*104 := by
    have hC := p2Direct_core_constant_le_104 (by positivity :
      0 ≤ (2/5 : ℝ)+p2GreenSeedNeutralAmplitude+(1/10^24 : ℝ)*p2CoefficientR^1846079336)
      hradii.1
    unfold directActionConstant at hC
    change cosineCurvatureBound ((2/5 : ℝ)+p2GreenSeedNeutralAmplitude+
      (1/10^24 : ℝ)*p2CoefficientR^1846079336) ≤ 2*104
    linarith
  have haction := direct_difference_action_le_of_constants
    p2GreenSeedCoordinate (2*p2GreenSeedNeutralCoefficient) p2CoefficientZeta
    (b := p2CoefficientBeta) (aMinus := p2GreenSeedLeftCoefficient)
    (aPlus := p2GreenSeedRightCoefficient) (τ := 1/10^24)
    (Δ := p2GreenSeedNeutralAmplitude) (aStar := 2/5) (Ccore := 104) (Cgap := 987/100)
    2885 1846079336 hb (by norm_num) (by norm_num) hm hp p2CoefficientZeta_unit.1 hne ha
    p2GreenSeedCoordinate_expanding_left p2GreenSeedCoordinate_source_right hmax' hmc
    (by norm_num) hcurv (by norm_num) (fun u hu => cosinePotential_le_quadratic (hu.trans hradii.2))
  norm_num only [Nat.cast_ofNat] at haction
  change directCoreAction p2GreenFinalCoordinate 1846085106 ≤ _ at haction
  have hnum := p2Direct_source_full_budget_lt
    (directCoreAction p2GreenSeedCoordinate 2885) p2GreenSeedNeutralAmplitude p2CoefficientR
    ((∑' n : ℕ, cosinePotential (p2GreenFinalLeftCoefficient*p2CoefficientR^(n+1))) +
      ∑' n : ℕ, cosinePotential (p2GreenFinalRightCoefficient*p2CoefficientR^n))
    hEc0 hEc hΔ0 hΔ hr0 hr p2GreenFinal_actual_tail_action.2.2.le
  simp only [show p2CoefficientBeta⁻¹ = p2CoefficientR from rfl] at haction
  norm_num only [Nat.cast_ofNat] at hnum
  have hsum := p2GreenFinalLocalizedCoordinate_action_hasSum
  have hsumLt : (∑' j : ℤ, cosinePotential (p2GreenFinalLocalizedCoordinate j)) < 47647/1000 := by
    rw [hsum.tsum_eq]
    linarith only [haction, hnum]
  have hcanon := directDifference_abs_lt_half
    p2GreenSeedCoordinate (2*p2GreenSeedNeutralCoefficient) p2CoefficientZeta
    (b := p2CoefficientBeta) (aMinus := p2GreenSeedLeftCoefficient)
    (aPlus := p2GreenSeedRightCoefficient) (τ := 1/10^24)
    (Δ := p2GreenSeedNeutralAmplitude) (aStar := 2/5)
    2885 1846079336 hb (by norm_num) hm hp p2CoefficientZeta_unit.1 ha
    p2GreenSeedCoordinate_expanding_left p2GreenSeedCoordinate_source_right hmax' hmc
    (by linarith [hradii.2])
  norm_num only [Nat.cast_ofNat] at hcanon
  change ∀ j : ℤ, |p2GreenFinalCoordinate j| < (1/2 : ℝ) at hcanon
  have hcenter (j : ℤ) : |p2GreenFinalLocalizedCoordinate j| < (1/2 : ℝ) := by
    by_cases hj : j < 1846085106
    · rw [p2GreenFinalLocalizedCoordinate, ite_eq_left hj]
      exact hcanon j
    · rw [p2GreenFinalLocalizedCoordinate, ite_eq_right hj, abs_mul,
        abs_of_nonneg (pow_nonneg hr0 _)]
      calc
        _ ≤ (1/10^24 : ℝ)*1 := mul_le_mul p2GreenFinal_stable_coefficients_small.2.le
          (pow_le_one₀ hr0 hr1.le) (pow_nonneg hr0 _) (by norm_num)
        _ < _ := by norm_num
  refine ⟨⟨hsum.summable, hsumLt, hcenter⟩, ?_⟩
  intro n hn
  have hH (k : ℕ) : |p2GreenFinalLocalizedCoordinate (1846085106+(k : ℤ))| ≤
      (1/10^23 : ℝ)*p2CoefficientR^(k+1) := by
    rw [p2GreenFinalLocalizedCoordinate_right_tail, abs_mul,
      abs_of_nonneg (pow_nonneg hr0 _)]
    have hτr : (1/10^24 : ℝ) ≤ (1/10^23 : ℝ)*p2CoefficientR := by
      linarith [p2CoefficientR_lower]
    calc
      _ ≤ (1/10^24 : ℝ)*p2CoefficientR^k :=
        mul_le_mul_of_nonneg_right p2GreenFinal_stable_coefficients_small.2.le (pow_nonneg hr0 _)
      _ ≤ ((1/10^23 : ℝ)*p2CoefficientR)*p2CoefficientR^k :=
        mul_le_mul_of_nonneg_right hτr (pow_nonneg hr0 _)
      _ = _ := by rw [pow_succ]; ring
  have haFinal : ‖p2GreenFinalOutgoingCoefficient‖ ≤ (1105305/10^21 : ℝ) := by
    rw [p2GreenFinalOutgoingCoefficient_norm]
    exact p2GreenFinalNeutralAmplitude_bounds.2.le
  have hsmall : (1/10^23 : ℝ)*p2CoefficientR+1105305/10^21 ≤ 1/100 := by
    linarith
  have hfourier := sharp_restoration_fourier_bound p2CoefficientBeta p2GreenFinalLeftCoefficient hb
    p2GreenFinalLocalizedCoordinate (1/10^23) p2CoefficientR (1105305/10^21)
    p2GreenFinalOutgoingCoefficient p2CoefficientZeta 1846085106 (10^26)
    hsum.summable (fun j _ => hcenter j) (by norm_num) hr0 hr1 hH haFinal
    p2CoefficientZeta_unit.1 hne hsmall p2GreenFinalLocalizedCoordinate_congruent_expanding n hn
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hfourier
  have hbudget := sharp_restoration_p2_budget_lt_direct
    (∑' j : ℤ, cosinePotential (p2GreenFinalLocalizedCoordinate j)) p2CoefficientR
    ‖1-p2CoefficientZeta^2‖ hsumLt.le hr0 hr (by linarith [p2CoefficientZeta_gap_gt])
  have hmod := restoration_p2_modulus_gt_direct _ _ (norm_nonneg _) hbudget.le hfourier
  have heq : ‖charFun (ElementaryCore.bernoulliLaw p2CoefficientBeta)
      (Real.pi*(p2GreenFinalLeftCoefficient*p2CoefficientBeta^n))‖ =
      |∫ x, Real.cos ((Real.pi*|p2GreenFinalLeftCoefficient| *p2CoefficientBeta^n)*x)
        ∂ElementaryCore.bernoulliLaw p2CoefficientBeta| := by
    calc
      _ = ‖charFun (ElementaryCore.bernoulliLaw p2CoefficientBeta)
          ((Real.pi*p2CoefficientBeta^n)*p2GreenFinalLeftCoefficient)‖ := by
            rw [show Real.pi*(p2GreenFinalLeftCoefficient*p2CoefficientBeta^n) =
              (Real.pi*p2CoefficientBeta^n)*p2GreenFinalLeftCoefficient by ring]
      _ = ‖charFun (ElementaryCore.bernoulliLaw p2CoefficientBeta)
          ((Real.pi*p2CoefficientBeta^n)*|p2GreenFinalLeftCoefficient|)‖ :=
        (norm_charFun_mul_abs _ _ _).symm
      _ = _ := by
        rw [p2_norm_charFun_eq_abs_integral_cos,
          show (Real.pi*p2CoefficientBeta^n)*|p2GreenFinalLeftCoefficient| =
            Real.pi*|p2GreenFinalLeftCoefficient| *p2CoefficientBeta^n by ring]
  exact heq ▸ hmod.le


/-- The actual final localized P₂ action is summable, centered, and below47.647. -/
theorem p2GreenFinal_actual_action :
    Summable (fun j : ℤ => cosinePotential (p2GreenFinalLocalizedCoordinate j)) ∧
      (∑' j : ℤ, cosinePotential (p2GreenFinalLocalizedCoordinate j)) < 47647/1000 ∧
      ∀ j : ℤ, |p2GreenFinalLocalizedCoordinate j| < (1/2 : ℝ) :=
  (p2ActualQuantitative_of_core_certificates
    p2GreenSeedCoordinate_core_abs_le p2GreenSeedCoordinate_core_action_le).1

/-- The unchanged source modulus holds at every actual requested P₂ frequency. -/
theorem p2Actual_uniform_cosine_lower_bound :
    ∀ n ≤ (10^26 : ℕ), (9/(2*10^11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi*|p2GreenFinalLeftCoefficient| *p2CoefficientBeta^n)*x)
        ∂ElementaryCore.bernoulliLaw p2CoefficientBeta| :=
  (p2ActualQuantitative_of_core_certificates
    p2GreenSeedCoordinate_core_abs_le p2GreenSeedCoordinate_core_action_le).2.1

/-- The actual second quartic parameter has the exact quantitative full-mass cover. -/
theorem p2Actual_exists_quantitative_cover :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw QuarticCore.beta2 F = 1 ∧
      dimH F < ENNReal.ofReal (1-(78 : ℝ)/10^23) :=
  (p2ActualQuantitative_of_core_certificates
    p2GreenSeedCoordinate_core_abs_le p2GreenSeedCoordinate_core_action_le).2.2

end Salem
