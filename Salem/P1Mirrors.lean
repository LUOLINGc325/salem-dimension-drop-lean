module

public import Salem.MirrorOrbit
public import Salem.P1Green
public import Salem.P1CoefficientBounds
public import Salem.P1MirrorBudgets

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The actual Green trajectory translated so its certified core is `0,...,26`. -/
noncomputable def p1MirrorSeedOrbit (b : ℝ) (j : ℤ) : ℝ := p1GreenSeed b (j-11)

/-- The full neutral coefficient in the same normalized coordinates. -/
noncomputable def p1MirrorSeedMode : ℂ :=
  2*p1SeedNeutralCoefficient*p1NeutralRoot^(-12 : ℤ)

/-- The actual normalized incoming coefficient, including its sign. -/
noncomputable def p1MirrorSeedCoefficient (b : ℝ) : ℝ := -p1SeedStartingCoefficient b

/-- The actual first delayed difference. -/
noncomputable def p1MirrorFirstOrbit (b : ℝ) : ℤ → ℝ :=
  mirrorDifference (p1MirrorSeedOrbit b) 124

noncomputable def p1MirrorFirstCoefficient (b : ℝ) : ℝ :=
  p1MirrorSeedCoefficient b*(1-b⁻¹^124)

noncomputable def p1MirrorFirstMode : ℂ :=
  mirrorNeutralCoefficient p1MirrorSeedMode p1NeutralRoot 124

/-- The actual second delayed difference. -/
noncomputable def p1MirrorFinalOrbit (b : ℝ) : ℤ → ℝ :=
  mirrorDifference (p1MirrorFirstOrbit b) 489637838

noncomputable def p1MirrorFinalMode : ℂ :=
  mirrorNeutralCoefficient p1MirrorFirstMode p1NeutralRoot 489637838

/-- Localization removes only the actual outgoing neutral wave. -/
noncomputable def p1MirrorSeedProfile (b : ℝ) : ℤ → ℝ :=
  localizeReciprocalOrbit b (p1MirrorSeedCoefficient b) 1 27 (p1MirrorSeedOrbit b)

noncomputable def p1MirrorFirstProfile (b : ℝ) : ℤ → ℝ :=
  localizeReciprocalOrbit b (p1MirrorFirstCoefficient b) (-1) 151 (p1MirrorFirstOrbit b)

noncomputable def p1MirrorFinalProfile (b : ℝ) : ℤ → ℝ :=
  localizeReciprocalOrbit b (p1FinalStartingCoefficient b) 1 489637989 (p1MirrorFinalOrbit b)

/-- Exact normalization of the physical expanding mode, for all integer times. -/
theorem p1MirrorSeed_expanding (b : ℝ) (hb : b ≠ 0) (j : ℤ) :
    p1SeedExpandingOrbit b (j-11) = p1MirrorSeedCoefficient b*b^j := by
  unfold p1SeedExpandingOrbit p1MirrorSeedCoefficient p1SeedStartingCoefficient
  rw [show j-11-1 = j-12 by ring, zpow_sub₀ hb]
  norm_num [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

/-- Exact normalized incoming data of the actual P1 Green seed. -/
theorem p1MirrorSeed_left {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) (hj : j < 0) :
    p1MirrorSeedOrbit b j = p1MirrorSeedCoefficient b*b^j := by
  rw [p1MirrorSeedOrbit, p1GreenSeed_left hb hroot (by omega)]
  exact p1MirrorSeed_expanding b (ne_of_gt (by linarith)) j

/-- Exact phase normalization of the physical neutral wave. -/
theorem p1MirrorSeed_wave (j : ℤ) :
    p1SeedNeutralWave (j-11) = neutralMode p1MirrorSeedMode p1NeutralRoot j := by
  unfold p1SeedNeutralWave neutralModeWave neutralMode p1MirrorSeedMode
  rw [show j-11-1 = (-12)+j by ring, zpow_add₀ p1NeutralRoot_ne_zero]
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

/-- Actual outgoing stable-plus-neutral data in normalized coordinates. -/
theorem p1MirrorSeed_right {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) (hj : (27 : ℤ) ≤ j) :
    p1MirrorSeedOrbit b j = p1MirrorSeedCoefficient b*b^(26-j)+
      neutralMode p1MirrorSeedMode p1NeutralRoot j := by
  rw [p1MirrorSeedOrbit, p1GreenSeed_right hb hroot (by omega), p1MirrorSeed_wave]
  rw [show 4-(j-11) = (26-j)-11 by ring,
    p1MirrorSeed_expanding b (ne_of_gt (by linarith))]

/-- The actual seed localization is precisely the previously certified profile,
 translated by eleven physical time steps. -/
theorem p1MirrorSeedProfile_eq {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) :
    p1MirrorSeedProfile b j = p1SeedLocalizedSequence b (j-11) := by
  unfold p1MirrorSeedProfile localizeReciprocalOrbit
  norm_num only [Nat.cast_ofNat, one_mul]
  by_cases hj : j < 27
  · rw [ite_eq_left hj]
    exact p1GreenSeed_eq_localized_left hb hroot (by omega)
  · rw [ite_eq_right hj, p1SeedLocalizedSequence_eq_reflected_orbit b (by omega),
      show 4-(j-11) = (26-j)-11 by ring,
      p1MirrorSeed_expanding b (ne_of_gt (by linarith))]

/-- The certified actual seed core retains the full `0.07804` margin. -/
theorem p1MirrorSeed_core_margin {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (i : Fin 27) :
    |p1MirrorSeedOrbit b i| ≤ (1/2-1951/25000 : ℝ) := by
  have he := p1GreenSeed_eq_localized_left hb hroot (t := (i : ℕ)-11) (by omega)
  rw [p1MirrorSeedOrbit, he]
  exact p1_seed_localized_margin_refined hb hroot _

/-- Actual integer forcing of the Green orbit gives actual Fourier congruence
 on the whole normalized integer trajectory. -/
theorem p1MirrorSeed_congruent {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    ∀ j : ℤ, ∃ m : ℤ,
      p1MirrorSeedOrbit b j-p1MirrorSeedCoefficient b*b^j = m := by
  apply quartic_forcing_global_congruent_expanding 1 (-1) (-1) (-1) b
    (p1MirrorSeedCoefficient b) (ne_of_gt (by linarith))
    (by simpa only [Int.cast_one, Int.cast_neg, neg_one_mul, one_mul, sub_eq_add_neg] using hroot)
    (p1MirrorSeedOrbit b) (p1MirrorSeed_left hb hroot)
  intro j _hj
  obtain ⟨m, hm⟩ := p1GreenSeed_integer_forcing hb hroot (j-11)
  refine ⟨m, ?_⟩
  unfold quarticResidual p1MirrorSeedOrbit
  unfold reciprocalQuarticOperator at hm
  norm_num only [Int.cast_one, Int.cast_neg, neg_one_mul, one_mul]
  have hidx (d : ℤ) : j+d-11 = (j-11)+d := by ring
  simp only [hidx]
  norm_num only [one_mul, neg_one_mul] at hm
  linear_combination hm

theorem p1Mirror_inverse_bounds {b : ℝ} (hb : (5/3 : ℝ) ≤ b) :
    0 ≤ b⁻¹ ∧ b⁻¹ ≤ (3/5 : ℝ) := by
  refine ⟨inv_nonneg.mpr (by linarith), ?_⟩
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5/3) hb
  simpa [one_div] using h

/-- The actual signed seed coefficient satisfies the common tail bound. -/
theorem p1MirrorSeed_coefficient_bound {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) : |p1MirrorSeedCoefficient b| ≤ (1/100 : ℝ) := by
  have hi := p1_expanding_root_interval hb hroot
  have hh := p1SeedStartingCoefficient_bounds hi.1.le hi.2.le
  rw [p1MirrorSeedCoefficient, abs_neg, abs_of_nonneg (by linarith : 0 ≤ p1SeedStartingCoefficient b)]
  linarith [hh.2]

/-- The normalized phase has exactly the actual spectral seed amplitude. -/
theorem p1MirrorSeedMode_norm : ‖p1MirrorSeedMode‖ = p1SeedNeutralAmplitude := by
  unfold p1MirrorSeedMode p1SeedNeutralAmplitude
  simp [p1NeutralRoot_norm]

/-- A slightly sharper true seed enclosure retains the first-return rounding slack. -/
theorem p1MirrorSeedAmplitude_refined : p1SeedNeutralAmplitude < (10146012/10^9 : ℝ) := by
  have hD := p1NeutralRoot_derivative_norm_lower
  have hDpos : 0 < ‖4*p1NeutralRoot^3-3*p1NeutralRoot^2-2*p1NeutralRoot-1‖ := by linarith
  have hkpos : 0 < -(1+2*p1NeutralRoot.re) := by linarith [p1NeutralRoot_re_bounds.2]
  have hkupper : -(1+2*p1NeutralRoot.re) ≤ (302775638/10^9 : ℝ) := by
    linarith [p1NeutralRoot_re_bounds.1]
  rw [p1SeedNeutralAmplitude_formula]
  calc
    _ ≤ 2*(302775638/10^9 : ℝ)^3/(5471387/10^6) := by gcongr
    _ < _ := by norm_num

/-- The actual first return gives its required normalized neutral radius. -/
theorem p1MirrorFirstMode_bound : ‖p1MirrorFirstMode‖ < (2542925/10^11 : ℝ) := by
  rw [p1MirrorFirstMode, norm_mirrorNeutralCoefficient _ _ p1NeutralRoot_norm,
    p1MirrorSeedMode_norm]
  calc
    _ < (10146012/10^9 : ℝ)*(250632946/10^11 : ℝ) :=
      mul_lt_mul_of_pos_left p1_return_bound_124_refined p1SeedNeutralAmplitude_bounds.1 |>.trans_le
        (mul_le_mul_of_nonneg_right p1MirrorSeedAmplitude_refined.le (by norm_num))
    _ < _ := by norm_num

/-- Both prescribed delay factors occur in the actual final normalized mode. -/
theorem p1MirrorFinalMode_eq :
    p1MirrorFinalMode = 2*p1FinalNeutralCoefficient*p1NeutralRoot^(-12 : ℤ) := by
  unfold p1MirrorFinalMode p1MirrorFirstMode p1MirrorSeedMode mirrorNeutralCoefficient
    p1FinalNeutralCoefficient
  simp only [zpow_neg, zpow_ofNat]
  ring

theorem p1MirrorFinalMode_norm : ‖p1MirrorFinalMode‖ = p1FinalNeutralAmplitude := by
  rw [p1MirrorFinalMode_eq]
  unfold p1FinalNeutralAmplitude
  simp [p1NeutralRoot_norm]

theorem p1MirrorFinalMode_bound : ‖p1MirrorFinalMode‖ < (9498/10^17 : ℝ) := by
  rw [p1MirrorFinalMode_norm]
  exact p1FinalNeutralAmplitude_bounds.2

/-- The actual normalized real stable tail is the previously certified tail. -/
theorem p1MirrorSeed_tail (b : ℝ) (k : ℕ) :
    p1MirrorSeedCoefficient b*b^(-1-(k : ℤ)) = p1SeedStableTail b k := by
  unfold p1MirrorSeedCoefficient p1SeedStableTail
  rw [show -1-(k : ℤ) = -((k+1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, inv_pow]

theorem p1MirrorSeed_core {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (i : Fin 27) :
    p1MirrorSeedOrbit b i = p1SeedCoreCoordinate b i := p1GreenSeed_core hb hroot i

/-- The actual seed profile has exactly the already certified bilateral action. -/
theorem p1MirrorSeed_action_hasSum {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    HasSum (fun j : ℤ => cosinePotential (p1MirrorSeedProfile b j)) (p1SeedLocalizedAction b) := by
  have ht := (p1_seed_stable_tail_action hb hroot).1
  have h := localizeReciprocalOrbit_action_hasSum (p1MirrorSeedOrbit b) b
    (p1MirrorSeedCoefficient b) 1 27 (Or.inl rfl) (p1MirrorSeed_left hb hroot)
    (by simpa only [p1MirrorSeed_tail] using ht)
  simpa only [p1MirrorSeedProfile, p1MirrorSeed_core hb hroot, p1MirrorSeed_tail,
    p1SeedLocalizedAction] using h

theorem p1MirrorSeed_action_lt {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (∑' j : ℤ, cosinePotential (p1MirrorSeedProfile b j)) < (2429771/200000 : ℝ) := by
  exact (p1MirrorSeed_action_hasSum hb hroot).tsum_eq.trans_lt
    (by simpa only [show (12148855/1000000 : ℝ) = 2429771/200000 by norm_num]
      using p1_seed_localized_action_refined hb hroot)

/-- Actual Green reciprocity in the normalized core coordinates. -/
theorem p1MirrorSeed_reciprocal {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) :
    p1MirrorSeedOrbit b (26-j) = p1MirrorSeedOrbit b j-
      neutralMode p1MirrorSeedMode p1NeutralRoot j := by
  change p1GreenSeed b ((26-j)-11) = p1GreenSeed b (j-11)-_
  rw [show (26-j)-11 = 4-(j-11) by ring,
    p1GreenSeed_reflection hb hroot, p1MirrorSeed_wave]

/-- The actual normalized wave has the matching opposite reflection sign. -/
theorem p1MirrorSeed_wave_reflection (j : ℤ) :
    neutralMode p1MirrorSeedMode p1NeutralRoot (26-j) =
      -neutralMode p1MirrorSeedMode p1NeutralRoot j := by
  rw [← p1MirrorSeed_wave, ← p1MirrorSeed_wave,
    show (26-j)-11 = 4-(j-11) by ring, p1SeedNeutralWave_reflection]

/-- The first actual P1 difference is the canonical Fourier orbit and retains
 the unrounded margin `0.07801` needed for the second mirror. -/
theorem p1MirrorFirst_canonical_and_margin {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (∀ j : ℤ, p1MirrorFirstOrbit b j = canonicalCenter (p1MirrorFirstCoefficient b*b^j)) ∧
    (∀ j : ℤ, |p1MirrorFirstOrbit b j| < (1/2 : ℝ)) ∧
    (∀ j : ℤ, |p1MirrorFirstProfile b j| ≤ (1/2-7801/100000 : ℝ)) := by
  have hr := p1Mirror_inverse_bounds hb
  have hp := p1Mirror_first_gap_power_bound b⁻¹ hr.1 hr.2
  have hmin : (7801/100000 : ℝ) ≤
      min (1951/25000-2542925/10^11-(1/100 : ℝ)*b⁻¹^(124-27+1))
        (min ((1/2 : ℝ)-(1014602/10^8+2*(1/100)*b⁻¹)) ((1/2 : ℝ)-(1/100)*b⁻¹)) := by
    refine le_min ?_ (le_min ?_ ?_) <;> norm_num only [Nat.reduceSub, Nat.reduceAdd] at * <;> linarith
  have hz0 : ‖p1MirrorSeedMode‖ ≤ (1014602/10^8 : ℝ) := by
    rw [p1MirrorSeedMode_norm]
    exact p1SeedNeutralAmplitude_bounds.2.le
  have h := mirrorDifference_canonical_of_seed_data (p1MirrorSeedOrbit b) b
    (p1MirrorSeedCoefficient b) (1/100) 1 (by linarith) (p1MirrorSeed_coefficient_bound hb hroot)
    (Or.inl rfl) p1MirrorSeedMode p1NeutralRoot p1NeutralRoot_norm
    (1014602/10^8) (2542925/10^11) (1951/25000) hz0 (by norm_num) 27 124
    p1MirrorFirstMode_bound.le (by norm_num) (by norm_num) (p1MirrorSeed_left hb hroot)
    (by intro j hj; simpa using p1MirrorSeed_right hb hroot j hj)
    (by intro j; simpa using p1MirrorSeed_reciprocal hb hroot j)
    (by intro j; simpa using p1MirrorSeed_wave_reflection j)
    (p1MirrorSeed_congruent hb hroot) (p1MirrorSeed_core_margin hb hroot)
    (lt_of_lt_of_le (by norm_num) hmin) (by linarith [hr.2])
  refine ⟨h.1, h.2.1, ?_⟩
  intro j
  have hj := h.2.2 j
  change |p1MirrorFirstProfile b j| ≤ _ at hj
  linarith

theorem p1MirrorFirst_coefficient_bound {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) : |p1MirrorFirstCoefficient b| ≤ (1/100 : ℝ) :=
  (mirror_coefficient_abs_le b (p1MirrorSeedCoefficient b) (by linarith) 124 (by norm_num)).trans
    (p1MirrorSeed_coefficient_bound hb hroot)

/-- The actual first core inherits the certified seed's derivative budget. -/
theorem p1MirrorSeed_slope_sum_lt {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (∑ i : Fin 27, |cosinePotentialSlope (p1MirrorSeedOrbit b i)|) < 473 := by
  apply mirror_first_core_slope_sum_lt
  · intro i
    exact (p1MirrorSeed_core_margin hb hroot i).trans (by norm_num)
  · simp_rw [p1MirrorSeed_core hb hroot]
    have hi := p1_expanding_root_interval hb hroot
    exact (p1_seed_core_action_budget hi.1.le hi.2.le).le.trans (by norm_num)

/-- Summability of the actual first stable tail is inherited from the actual seed. -/
theorem p1MirrorFirst_tail_summable {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    Summable (fun k : ℕ => cosinePotential (p1MirrorFirstCoefficient b*b^(-1-(k : ℤ)))) := by
  have hr := p1Mirror_inverse_bounds hb
  exact (mirrorStableTail_action_mono b (p1MirrorSeedCoefficient b) (1/100) (by linarith)
    (p1MirrorSeed_coefficient_bound hb hroot) 124 (by norm_num) (by linarith [hr.2])
    (by simpa only [p1MirrorSeed_tail] using (p1_seed_stable_tail_action hb hroot).1)).1

/-- The first actual localized mirror has its derived action below `24.367`. -/
theorem p1MirrorFirst_action {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    Summable (fun j : ℤ => cosinePotential (p1MirrorFirstProfile b j)) ∧
    (∑' j : ℤ, cosinePotential (p1MirrorFirstProfile b j)) < (24367/1000 : ℝ) := by
  have hr := p1Mirror_inverse_bounds hb
  have hp := p1Mirror_first_gap_power_bound b⁻¹ hr.1 hr.2
  have hz0 : ‖p1MirrorSeedMode‖ ≤ (1014602/10^8 : ℝ) := by
    rw [p1MirrorSeedMode_norm]
    exact p1SeedNeutralAmplitude_bounds.2.le
  have hne : 1-p1NeutralRoot^2 ≠ 0 := by
    intro he
    have hd := p1NeutralRoot_norm_one_sub_sq_gt_three_halves
    rw [he, norm_zero] at hd
    norm_num at hd
  have hcore (i : Fin 27) : |p1MirrorSeedOrbit b i|+
      (1/100 : ℝ)*b⁻¹^(124-27+1)+2542925/10^11 ≤ (211/500 : ℝ) := by
    have hi := p1MirrorSeed_core_margin hb hroot i
    norm_num only [Nat.reduceSub, Nat.reduceAdd] at *
    linarith
  have ha := mirrorDifference_localized_action_le (p1MirrorSeedOrbit b) b
    (p1MirrorSeedCoefficient b) (1/100) 1 (by linarith) (p1MirrorSeed_coefficient_bound hb hroot)
    (Or.inl rfl) p1MirrorSeedMode p1NeutralRoot p1NeutralRoot_norm hne
    (1014602/10^8) (2542925/10^11) (211/500) (223/10000) hz0 (by norm_num) 27 124
    p1MirrorFirstMode_bound.le (by norm_num) (by norm_num) (p1MirrorSeed_left hb hroot)
    (by intro j hj; simpa using p1MirrorSeed_right hb hroot j hj)
    (by intro j; simpa using p1MirrorSeed_reciprocal hb hroot j)
    (by intro j; simpa using p1MirrorSeed_wave_reflection j)
    (by simpa only [p1MirrorSeed_tail] using (p1_seed_stable_tail_action hb hroot).1)
    (by linarith [hr.2]) (by norm_num) (by norm_num) hcore
    (by norm_num) (by norm_num) (by linarith [hr.2])
  let E := ∑' j : ℤ, cosinePotential (p1MirrorSeedProfile b j)
  let W := ∑ i : Fin 27, |cosinePotentialSlope (p1MirrorSeedOrbit b i)|
  change Summable (fun j : ℤ => cosinePotential (p1MirrorFirstProfile b j)) ∧
    (∑' j : ℤ, cosinePotential (p1MirrorFirstProfile b j)) ≤
      p1MirrorActionBudget E W (cosineCurvatureBound (211/500))
        (cosineCurvatureBound (223/10000)) (1014602/10^8) (2542925/10^11) b⁻¹
        ‖1-p1NeutralRoot^2‖ 27 97 at ha
  have hbudget := p1Mirror_first_budget_lt E W (cosineCurvatureBound (211/500))
    (cosineCurvatureBound (223/10000)) (1014602/10^8) (2542925/10^11) b⁻¹
    ‖1-p1NeutralRoot^2‖ (p1MirrorSeed_action_lt hb hroot).le (by dsimp [W]; positivity)
    (p1MirrorSeed_slope_sum_lt hb hroot).le
    (by unfold cosineCurvatureBound; positivity)
    (mirror_core_curvature_le _ (by norm_num) (by norm_num))
    (by unfold cosineCurvatureBound; positivity)
    (mirror_curvature_first_le _ (by norm_num) le_rfl)
    (by norm_num) le_rfl (by norm_num) le_rfl hr.1 hr.2
    p1NeutralRoot_norm_one_sub_sq_gt_three_halves.le
  exact ⟨ha.1, ha.2.trans_lt hbudget⟩

theorem p1MirrorFirst_left {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) (hj : j < 0) :
    p1MirrorFirstOrbit b j = p1MirrorFirstCoefficient b*b^j :=
  mirrorDifference_incoming (p1MirrorSeedOrbit b) b (p1MirrorSeedCoefficient b)
    (ne_of_gt (by linarith)) 124 (p1MirrorSeed_left hb hroot) j hj

theorem p1MirrorFirst_right {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) (hj : (151 : ℤ) ≤ j) :
    p1MirrorFirstOrbit b j = (-1 : ℝ)*p1MirrorFirstCoefficient b*b^(150-j)+
      neutralMode p1MirrorFirstMode p1NeutralRoot j := by
  have h := mirrorDifference_outgoing (p1MirrorSeedOrbit b) b (p1MirrorSeedCoefficient b) 1
    (ne_of_gt (by linarith)) p1MirrorSeedMode p1NeutralRoot p1NeutralRoot_ne_zero 27 124
    (by intro k hk; simpa using p1MirrorSeed_right hb hroot k hk) j (by omega)
  simpa [p1MirrorFirstOrbit, p1MirrorFirstCoefficient, p1MirrorFirstMode] using h

theorem p1MirrorFirst_reciprocal {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) :
    p1MirrorFirstOrbit b (150-j) = (-1 : ℝ)*(p1MirrorFirstOrbit b j-
      neutralMode p1MirrorFirstMode p1NeutralRoot j) := by
  have h := mirrorDifference_reciprocal_mode (p1MirrorSeedOrbit b) p1MirrorSeedMode
    p1NeutralRoot p1NeutralRoot_ne_zero 27 124 1
    (by intro k; simpa using p1MirrorSeed_reciprocal hb hroot k) j
  simpa [p1MirrorFirstOrbit, p1MirrorFirstMode] using h

theorem p1MirrorFirst_wave_reflection (j : ℤ) :
    neutralMode p1MirrorFirstMode p1NeutralRoot (150-j) =
      neutralMode p1MirrorFirstMode p1NeutralRoot j := by
  have h := mirrorNeutralCoefficient_reflection p1MirrorSeedMode p1NeutralRoot
    p1NeutralRoot_ne_zero 27 124 1 (by intro k; simpa using p1MirrorSeed_wave_reflection k) j
  simpa [p1MirrorFirstMode] using h

theorem p1MirrorFirst_congruent {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    ∀ j : ℤ, ∃ m : ℤ, p1MirrorFirstOrbit b j-p1MirrorFirstCoefficient b*b^j = m :=
  mirrorDifference_congruent_expanding b (p1MirrorSeedCoefficient b) (ne_of_gt (by linarith))
    (p1MirrorSeedOrbit b) 124 (p1MirrorSeed_congruent hb hroot)

theorem p1MirrorFirst_core_margin {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (i : Fin 151) :
    |p1MirrorFirstOrbit b i| ≤ (1/2-7801/100000 : ℝ) := by
  have h := (p1MirrorFirst_canonical_and_margin hb hroot).2.2 i
  have he : p1MirrorFirstProfile b i = p1MirrorFirstOrbit b i := by
    unfold p1MirrorFirstProfile localizeReciprocalOrbit
    rw [ite_eq_left (by exact_mod_cast i.isLt)]
  rwa [he] at h

/-- The first actual core inherits its action bound from the full proved action,
 and therefore has the derivative budget required for the second mirror. -/
theorem p1MirrorFirst_slope_sum_lt {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (∑ i : Fin 151, |cosinePotentialSlope (p1MirrorFirstOrbit b i)|) < 1600 := by
  apply mirror_second_core_slope_sum_lt_relaxed
  · intro i
    exact (p1MirrorFirst_core_margin hb hroot i).trans (by norm_num)
  · have h := localizeReciprocalOrbit_action_hasSum (p1MirrorFirstOrbit b) b
      (p1MirrorFirstCoefficient b) (-1) 151 (Or.inr rfl) (p1MirrorFirst_left hb hroot)
      (p1MirrorFirst_tail_summable hb hroot)
    have he := h.tsum_eq
    change (∑' j : ℤ, cosinePotential (p1MirrorFirstProfile b j)) = _ at he
    have htail : 0 ≤ ∑' k : ℕ, cosinePotential (p1MirrorFirstCoefficient b*b^(-1-(k : ℤ))) := by
      apply tsum_nonneg
      intro k
      unfold cosinePotential
      exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
    linarith [(p1MirrorFirst_action hb hroot).2]

/-- The final incoming coefficient is the actual twice-updated seed coefficient. -/
theorem p1MirrorFinal_coefficient_update (b : ℝ) :
    p1MirrorFirstCoefficient b*(1-b⁻¹^489637838) = p1FinalStartingCoefficient b := rfl

/-- The actual second P1 difference is canonical and retains the printed final
 boundary margin `39/500` everywhere in its localization. -/
theorem p1MirrorFinal_canonical_and_margin {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (∀ j : ℤ, p1MirrorFinalOrbit b j = canonicalCenter (p1FinalStartingCoefficient b*b^j)) ∧
    (∀ j : ℤ, |p1MirrorFinalOrbit b j| < (1/2 : ℝ)) ∧
    (∀ j : ℤ, |p1MirrorFinalProfile b j| ≤ (1/2-39/500 : ℝ)) := by
  have hr := p1Mirror_inverse_bounds hb
  have hp := p1Mirror_long_gap_power_bound b⁻¹ hr.1 hr.2 (489637838-151+1) (by norm_num)
  have hmin : (39/500 : ℝ) ≤
      min (7801/100000-9498/10^17-(1/100 : ℝ)*b⁻¹^(489637838-151+1))
        (min ((1/2 : ℝ)-(2542925/10^11+2*(1/100)*b⁻¹)) ((1/2 : ℝ)-(1/100)*b⁻¹)) := by
    refine le_min ?_ (le_min ?_ ?_) <;> linarith
  have h := mirrorDifference_canonical_of_seed_data (p1MirrorFirstOrbit b) b
    (p1MirrorFirstCoefficient b) (1/100) (-1) (by linarith)
    (p1MirrorFirst_coefficient_bound hb hroot) (Or.inr rfl)
    p1MirrorFirstMode p1NeutralRoot p1NeutralRoot_norm
    (2542925/10^11) (9498/10^17) (7801/100000) p1MirrorFirstMode_bound.le (by norm_num)
    151 489637838 p1MirrorFinalMode_bound.le (by norm_num) (by norm_num)
    (p1MirrorFirst_left hb hroot)
    (by intro j hj; simpa using p1MirrorFirst_right hb hroot j hj)
    (by intro j; simpa using p1MirrorFirst_reciprocal hb hroot j)
    (by intro j; simpa using p1MirrorFirst_wave_reflection j)
    (p1MirrorFirst_congruent hb hroot) (p1MirrorFirst_core_margin hb hroot)
    (lt_of_lt_of_le (by norm_num) hmin) (by linarith [hr.2])
  simp only [neg_neg] at h
  refine ⟨h.1, h.2.1, ?_⟩
  intro j
  have hj := h.2.2 j
  change |p1MirrorFinalProfile b j| ≤ _ at hj
  linarith

theorem p1MirrorFinal_congruent {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    ∀ j : ℤ, ∃ m : ℤ, p1MirrorFinalOrbit b j-p1FinalStartingCoefficient b*b^j = m :=
  mirrorDifference_congruent_expanding b (p1MirrorFirstCoefficient b) (ne_of_gt (by linarith))
    (p1MirrorFirstOrbit b) 489637838 (p1MirrorFirst_congruent hb hroot)

/-- Both actual mirror constructions give the required full final action,
 including both infinite stable tails and the exact `489637687`-site bridge. -/
theorem p1MirrorFinal_action {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    Summable (fun j : ℤ => cosinePotential (p1MirrorFinalProfile b j)) ∧
    (∑' j : ℤ, cosinePotential (p1MirrorFinalProfile b j)) < (503/10 : ℝ) := by
  have hr := p1Mirror_inverse_bounds hb
  have hp := p1Mirror_long_gap_power_bound b⁻¹ hr.1 hr.2 (489637838-151+1) (by norm_num)
  have hne : 1-p1NeutralRoot^2 ≠ 0 := by
    intro he
    have hd := p1NeutralRoot_norm_one_sub_sq_gt_three_halves
    rw [he, norm_zero] at hd
    norm_num at hd
  have hcore (i : Fin 151) : |p1MirrorFirstOrbit b i|+
      (1/100 : ℝ)*b⁻¹^(489637838-151+1)+9498/10^17 ≤ (211/500 : ℝ) := by
    have hi := p1MirrorFirst_core_margin hb hroot i
    linarith
  have ha := mirrorDifference_localized_action_le (p1MirrorFirstOrbit b) b
    (p1MirrorFirstCoefficient b) (1/100) (-1) (by linarith) (p1MirrorFirst_coefficient_bound hb hroot)
    (Or.inr rfl) p1MirrorFirstMode p1NeutralRoot p1NeutralRoot_norm hne
    (2542925/10^11) (9498/10^17) (211/500) (121/10000) p1MirrorFirstMode_bound.le
    (by norm_num) 151 489637838 p1MirrorFinalMode_bound.le (by norm_num) (by norm_num)
    (p1MirrorFirst_left hb hroot)
    (by intro j hj; simpa using p1MirrorFirst_right hb hroot j hj)
    (by intro j; simpa using p1MirrorFirst_reciprocal hb hroot j)
    (by intro j; simpa using p1MirrorFirst_wave_reflection j)
    (p1MirrorFirst_tail_summable hb hroot)
    (by linarith [hr.2]) (by norm_num) (by norm_num) hcore
    (by norm_num) (by norm_num) (by linarith [hr.2])
  simp only [neg_neg] at ha
  let E := ∑' j : ℤ, cosinePotential (p1MirrorFirstProfile b j)
  let W := ∑ i : Fin 151, |cosinePotentialSlope (p1MirrorFirstOrbit b i)|
  change Summable (fun j : ℤ => cosinePotential (p1MirrorFinalProfile b j)) ∧
    (∑' j : ℤ, cosinePotential (p1MirrorFinalProfile b j)) ≤
      p1MirrorActionBudget E W (cosineCurvatureBound (211/500))
        (cosineCurvatureBound (121/10000)) (2542925/10^11) (9498/10^17) b⁻¹
        ‖1-p1NeutralRoot^2‖ 151 489637687 at ha
  have hbudget := p1Mirror_second_budget_lt E W (cosineCurvatureBound (211/500))
    (cosineCurvatureBound (121/10000)) (2542925/10^11) (9498/10^17) b⁻¹
    ‖1-p1NeutralRoot^2‖ (p1MirrorFirst_action hb hroot).2.le (by dsimp [W]; positivity)
    (p1MirrorFirst_slope_sum_lt hb hroot).le
    (by unfold cosineCurvatureBound; positivity)
    (mirror_core_curvature_le _ (by norm_num) (by norm_num))
    (by unfold cosineCurvatureBound; positivity)
    (mirror_curvature_second_le _ (by norm_num) le_rfl)
    (by norm_num) le_rfl (by norm_num) le_rfl hr.1 hr.2
    p1NeutralRoot_norm_one_sub_sq_gt_three_halves.le
  exact ⟨ha.1, ha.2.trans_lt hbudget⟩

theorem p1MirrorFinal_coefficient_bound {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) : |p1FinalStartingCoefficient b| ≤ (1/100 : ℝ) :=
  (mirror_coefficient_abs_le b (p1MirrorFirstCoefficient b) (by linarith)
    489637838 (by norm_num)).trans (p1MirrorFirst_coefficient_bound hb hroot)

/-- The actual final outgoing stable mode and actual neutral wave. -/
theorem p1MirrorFinal_right {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) (hj : (489637989 : ℤ) ≤ j) :
    p1MirrorFinalOrbit b j = p1FinalStartingCoefficient b*b^(489637988-j)+
      neutralMode p1MirrorFinalMode p1NeutralRoot j := by
  have h := mirrorDifference_outgoing (p1MirrorFirstOrbit b) b (p1MirrorFirstCoefficient b) (-1)
    (ne_of_gt (by linarith)) p1MirrorFirstMode p1NeutralRoot p1NeutralRoot_ne_zero 151 489637838
    (by intro k hk; simpa using p1MirrorFirst_right hb hroot k hk) j (by omega)
  rw [p1MirrorFinal_coefficient_update] at h
  simpa [p1MirrorFinalOrbit, p1MirrorFinalMode] using h

/-- The actual final localized exterior is exactly its derived stable exponential. -/
theorem p1MirrorFinal_tail_eq (b : ℝ) (k : ℕ) :
    p1MirrorFinalProfile b ((489637989 : ℤ)+k) =
      p1FinalStartingCoefficient b*b^(-1-(k : ℤ)) := by
  unfold p1MirrorFinalProfile localizeReciprocalOrbit
  norm_num only [Nat.cast_ofNat, one_mul]
  rw [ite_eq_right (by omega)]
  congr 2
  ring

theorem p1MirrorFinal_tail {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (k : ℕ) :
    |p1MirrorFinalProfile b ((489637989 : ℤ)+k)| ≤ (1/100 : ℝ)*b⁻¹^(k+1) := by
  rw [p1MirrorFinal_tail_eq, reciprocalStableTail_abs b _ (by linarith)]
  exact mul_le_mul_of_nonneg_right (p1MirrorFinal_coefficient_bound hb hroot)
    (pow_nonneg (p1Mirror_inverse_bounds hb).1 _)

/-- The exact true Fourier orbit is the actual finite-action localization plus
 its outgoing neutral wave with the derived phase at the final boundary. -/
theorem p1MirrorFinal_restoration {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) (j : ℤ) :
    p1MirrorFinalOrbit b j = p1MirrorFinalProfile b j+
      outgoingNeutralWave (p1MirrorFinalMode*p1NeutralRoot^(489637989 : ℤ))
        p1NeutralRoot 489637989 j := by
  unfold outgoingNeutralWave
  by_cases hj : (489637989 : ℤ) ≤ j
  · rw [ite_eq_left hj, p1MirrorFinal_right hb hroot j hj]
    have hloc : p1MirrorFinalProfile b j = p1FinalStartingCoefficient b*b^(489637988-j) := by
      unfold p1MirrorFinalProfile localizeReciprocalOrbit
      norm_num only [Nat.cast_ofNat, one_mul]
      rw [ite_eq_right (by omega)]
    rw [hloc]
    congr 1
    unfold neutralMode
    congr 1
    rw [mul_assoc, ← zpow_add₀ p1NeutralRoot_ne_zero]
    congr 1
    ring
  · rw [ite_eq_right hj, add_zero]
    unfold p1MirrorFinalProfile localizeReciprocalOrbit
    rw [ite_eq_left (by omega)]

/-- The outgoing-boundary phase preserves the certified actual final amplitude. -/
theorem p1MirrorFinal_outgoing_norm :
    ‖p1MirrorFinalMode*p1NeutralRoot^(489637989 : ℤ)‖ < (9498/10^17 : ℝ) := by
  simpa [p1NeutralRoot_norm] using p1MirrorFinalMode_bound

/-- The actual final positive frequency magnitude lies in the prescribed interval. -/
theorem p1MirrorFinal_frequency_bounds {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    (2 : ℝ)^(-112 : ℤ) < p1FinalStartingCoefficientMagnitude b ∧
      p1FinalStartingCoefficientMagnitude b < 1 := by
  simpa only [abs_p1FinalStartingCoefficient hb hroot] using p1FinalStartingCoefficient_bounds hb hroot

/-- An actual positive-frequency P1 certificate. A global sign reversal of the
 constructed profile puts the genuine frequency in the printed positive interval;
 evenness preserves every proved action and boundary estimate. -/
theorem p1Mirrors_actual_certificate {b : ℝ} (hb : (5/3 : ℝ) ≤ b)
    (hroot : b^4-b^3-b^2-b+1 = 0) :
    ∃ (H : ℤ → ℝ) (a : ℂ) (c : ℝ),
      (2 : ℝ)^(-112 : ℤ) < c ∧ c < 1 ∧
      Summable (fun j : ℤ => cosinePotential (H j)) ∧
      (∑' j : ℤ, cosinePotential (H j)) ≤ (503/10 : ℝ) ∧
      (∀ j : ℤ, |H j| ≤ (1/2-39/500 : ℝ)) ∧
      ‖a‖ < (9498/10^17 : ℝ) ∧
      (∀ k : ℕ, |H ((489637989 : ℤ)+k)| ≤ (1/100 : ℝ)*b⁻¹^(k+1)) ∧
      (∀ j : ℤ, canonicalCenter (c*b^j) = H j+
        outgoingNeutralWave a p1NeutralRoot 489637989 j) := by
  let a := p1MirrorFinalMode*p1NeutralRoot^(489637989 : ℤ)
  have haction := p1MirrorFinal_action hb hroot
  have hcanonical := p1MirrorFinal_canonical_and_margin hb hroot
  have hfreq := p1MirrorFinal_frequency_bounds hb hroot
  refine ⟨fun j => -p1MirrorFinalProfile b j, -a, p1FinalStartingCoefficientMagnitude b,
    hfreq.1, hfreq.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cosinePotential, mul_neg, Real.cos_neg] using haction.1
  · simpa only [cosinePotential, mul_neg, Real.cos_neg] using haction.2.le
  · intro j
    simpa only [abs_neg] using hcanonical.2.2 j
  · simpa only [norm_neg] using p1MirrorFinal_outgoing_norm
  · intro k
    simpa only [abs_neg] using p1MirrorFinal_tail hb hroot k
  · intro j
    obtain ⟨m, hm⟩ := p1MirrorFinal_congruent hb hroot j
    have hi : ∃ n : ℤ, (-p1MirrorFinalOrbit b j)-
        p1FinalStartingCoefficientMagnitude b*b^j = n := by
      refine ⟨-m, ?_⟩
      rw [p1FinalStartingCoefficient_eq_neg_magnitude] at hm
      push_cast
      linarith
    have hc := canonicalCenter_eq_of_int_congr (-p1MirrorFinalOrbit b j)
      (p1FinalStartingCoefficientMagnitude b*b^j) hi
    rw [canonicalCenter_eq_self_of_abs_lt_half _
      (by simpa only [abs_neg] using hcanonical.2.1 j)] at hc
    have hw : outgoingNeutralWave (-a) p1NeutralRoot 489637989 j =
        -outgoingNeutralWave a p1NeutralRoot 489637989 j := by
      unfold outgoingNeutralWave
      split_ifs <;> simp
    rw [← hc, p1MirrorFinal_restoration hb hroot j, hw]
    dsimp [a]
    ring

end Salem
