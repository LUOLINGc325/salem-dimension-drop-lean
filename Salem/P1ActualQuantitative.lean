module

public import Salem.P1Mirrors
public import Salem.QuantitativeBernoulliCore

@[expose] public section

open MeasureTheory

namespace Salem

/-- The modulus of the actual symmetric Bernoulli characteristic function is
 the absolute value of its cosine integral at the same real frequency. -/
theorem norm_charFun_bernoulliLaw_eq_abs_cos (b : ℝ) (hb : 1 < b) (t : ℝ) :
    ‖charFun (ElementaryCore.bernoulliLaw b) t‖ =
      |∫ x, Real.cos (t*x) ∂ElementaryCore.bernoulliLaw b| := by
  rw [charFun_bernoulliLaw_eq_tprod b hb t,
    integral_cos_bernoulliLaw_eq_tprod b hb t]
  simp

/-- Frequency normalization preserves the modulus even when the actual incoming
 coefficient is negative. -/
theorem norm_charFun_bernoulliLaw_abs_frequency (b c : ℝ) (hb : 1 < b) (n : ℕ) :
    ‖charFun (ElementaryCore.bernoulliLaw b) (Real.pi*(c*b^n))‖ =
      |∫ x, Real.cos ((Real.pi * |c| * b^n)*x) ∂ElementaryCore.bernoulliLaw b| := by
  rw [← norm_charFun_bernoulliLaw_eq_abs_cos b hb]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (norm_charFun_mul_abs (ElementaryCore.bernoulliLaw b) (Real.pi*b^n) c).symm

/-- The two actual mirror constructions and the actual neutral amplitude fit
 the rigorous P1 restoration threshold, with every infinite tail included. -/
theorem p1_actual_restored_action_lt {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (∑' j : ℤ, cosinePotential (p1MirrorFinalProfile b j)) +
      20*(9498/10^17 : ℝ)*(1/100 : ℝ)*b⁻¹/(1-b⁻¹) +
      10*(9498/10^17 : ℝ)^2*
        (((2*10^25 : ℝ)+1)/2 + 1/‖1-p1NeutralRoot^2‖) < 2561/50 := by
  exact sharp_restoration_p1_budget_lt_relaxed _ _ _
    (p1MirrorFinal_action hb hroot).2.le (p1Mirror_inverse_bounds hb).1
    (p1Mirror_inverse_bounds hb).2
    (by linarith [p1NeutralRoot_norm_one_sub_sq_gt_three_halves])

/-- Every source frequency through `J₁` has the required actual cosine Fourier
 bias. The finite core, both stable tails, and outgoing neutral restoration are
 supplied by the constructed twice-mirrored P1 orbit. -/
theorem p1_actual_uniform_fourier_bound {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (n : ℕ) (hn : n ≤ 2*10^25) :
    (3/(4*10^11) : ℝ) <
      |∫ x, Real.cos ((Real.pi * |p1FinalStartingCoefficient b| * b^n)*x)
        ∂ElementaryCore.bernoulliLaw b| := by
  have hr := p1Mirror_inverse_bounds hb
  have hmargin := (p1MirrorFinal_canonical_and_margin hb hroot).2.2
  have hne : 1-p1NeutralRoot^2 ≠ 0 := by
    intro he
    have hd := p1NeutralRoot_norm_one_sub_sq_gt_three_halves
    rw [he, norm_zero] at hd
    norm_num at hd
  have hcong (j : ℤ) : ∃ m : ℤ,
      p1MirrorFinalProfile b j +
        outgoingNeutralWave (p1MirrorFinalMode*p1NeutralRoot^(489637989 : ℤ))
          p1NeutralRoot 489637989 j - p1FinalStartingCoefficient b*b^j = m := by
    rw [← p1MirrorFinal_restoration hb hroot j]
    exact p1MirrorFinal_congruent hb hroot j
  have hfourier := sharp_restoration_fourier_bound b (p1FinalStartingCoefficient b)
    (by linarith) (p1MirrorFinalProfile b) (1/100) b⁻¹ (9498/10^17)
    (p1MirrorFinalMode*p1NeutralRoot^(489637989 : ℤ)) p1NeutralRoot 489637989
    (2*10^25) (p1MirrorFinal_action hb hroot).1
    (by intro j hj; linarith [hmargin j]) (by norm_num) hr.1 (by linarith [hr.2])
    (p1MirrorFinal_tail hb hroot) p1MirrorFinal_outgoing_norm.le p1NeutralRoot_norm
    hne (by linarith [hr.2]) hcong n hn
  have hbudget := (p1_actual_restored_action_lt hb hroot).le
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hfourier hbudget
  have hmod := restoration_p1_modulus_gt _ _ (norm_nonneg _) hbudget hfourier
  rwa [norm_charFun_bernoulliLaw_abs_frequency b (p1FinalStartingCoefficient b)
    (by linarith) n] at hmod

namespace QuarticCore

/-- The literal first source parameter satisfies the polynomial equation used by
 the actual analytic construction. -/
theorem beta1_actual_polynomial_root : beta1^4-beta1^3-beta1^2-beta1+1 = 0 := by
  simpa only [P1_eval_real] using beta1_P1_root

/-- The actual twice-mirrored incoming coefficient retains its negative sign and
 has precisely the magnitude range required by the quantitative cover theorem. -/
theorem beta1_actual_starting_coefficient_bounds :
    p1FinalStartingCoefficient beta1 < 0 ∧
    1/(2 : ℝ)^112 < |p1FinalStartingCoefficient beta1| ∧
    |p1FinalStartingCoefficient beta1| < 1 := by
  have h := p1FinalStartingCoefficient_bounds beta1_gt_five_thirds.le
    beta1_actual_polynomial_root
  refine ⟨p1FinalStartingCoefficient_neg beta1_gt_five_thirds.le
    beta1_actual_polynomial_root, ?_, h.2⟩
  simpa only [zpow_neg, zpow_ofNat, one_div] using h.1

/-- The literal first source parameter has the required actual finite uniform
 Fourier bias, with no seed, action, or Fourier premise. -/
theorem beta1_actual_uniform_fourier_bound (n : ℕ) (hn : n ≤ 2*10^25) :
    (3/(4*10^11) : ℝ) <
      |∫ x, Real.cos ((Real.pi * |p1FinalStartingCoefficient beta1| * beta1^n)*x)
        ∂ElementaryCore.bernoulliLaw beta1| :=
  p1_actual_uniform_fourier_bound beta1_gt_five_thirds.le beta1_actual_polynomial_root n hn

/-- The actual first Salem construction gives the unchanged quantitative
 full-mass cover. Its only premise is the quartic nonvacuity guard supplied by
 the frozen statement module. -/
theorem exists_actual_quantitative_beta1_cover
    (hquartic : IsQuarticSalemNumber beta1) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw beta1 F = 1 ∧
      dimH F < ENNReal.ofReal (1-(14 : ℝ)/10^24) := by
  have hc := beta1_actual_starting_coefficient_bounds
  exact exists_quantitative_beta1_cover_of_uniform_bias hquartic hc.2.1 hc.2.2
    (fun n hn => (beta1_actual_uniform_fourier_bound n hn).le)

end QuarticCore

end Salem
