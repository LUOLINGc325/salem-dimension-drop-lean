module

public import Salem.MirrorAction
public import Salem.CosineTail

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The source quadratic/Taylor constant is half the second-derivative bound. -/
noncomputable def directActionConstant (R : ℝ) : ℝ := cosineCurvatureBound R / 2

/-- Exact finite geometric square norm, including the zero-length case. -/
noncomputable def directGeometricFactor (r : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt ((1 - r ^ (2 * m)) / (1 - r ^ 2))

/-- The source minimum of the pointwise and half-density oscillatory square bounds. -/
noncomputable def directOscillationFactor (ζ : ℂ) (m : ℕ) : ℝ :=
  Real.sqrt (min (m : ℝ) ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖))

theorem sum_geometric_sq_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    (∑ i ∈ Finset.range m, (r ^ i) ^ 2) = (1 - r ^ (2 * m)) / (1 - r ^ 2) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  apply (eq_div_iff (by linarith : 1 - r ^ 2 ≠ 0)).2
  have h := geom_sum_mul_neg (r ^ 2) m
  convert h using 1 <;> simp only [← pow_mul, Nat.mul_comm]

theorem directGeometricFactor_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    directGeometricFactor r m ^ 2 = ∑ i ∈ Finset.range m, (r ^ i) ^ 2 := by
  unfold directGeometricFactor
  rw [← sum_geometric_sq_eq hr0 hr1 m]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem directGeometricFactor_nonneg (r : ℝ) (m : ℕ) : 0 ≤ directGeometricFactor r m :=
  Real.sqrt_nonneg _

theorem directOscillationFactor_nonneg (ζ : ℂ) (m : ℕ) : 0 ≤ directOscillationFactor ζ m :=
  Real.sqrt_nonneg _

theorem directOscillationFactor_sq (ζ : ℂ) (m : ℕ) :
    directOscillationFactor ζ m ^ 2 = min (m : ℝ) ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
  apply Real.sq_sqrt
  exact le_min (Nat.cast_nonneg _) (by positivity)

/-- Finite Cauchy--Schwarz in the exact squared form used for direct core perturbations. -/
theorem direct_sum_mul_le {ι : Type*} (s : Finset ι) (f h : ι → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∑ i ∈ s, f i ^ 2 ≤ A ^ 2) (hh : ∑ i ∈ s, h i ^ 2 ≤ B ^ 2) :
    (∑ i ∈ s, f i * h i) ≤ A * B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f h
  have hf0 : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh0 : 0 ≤ ∑ i ∈ s, h i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hprod := mul_le_mul hf hh hh0 (sq_nonneg A)
  have hprod' := hcs.trans hprod
  nlinarith [mul_nonneg hA hB]

/-- The finite square norm satisfies the source triangle estimate without a pointwise loss. -/
theorem direct_sum_add_sq_le {ι : Type*} (s : Finset ι) (f h : ι → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∑ i ∈ s, f i ^ 2 ≤ A ^ 2) (hh : ∑ i ∈ s, h i ^ 2 ≤ B ^ 2) :
    (∑ i ∈ s, (f i + h i) ^ 2) ≤ (A + B) ^ 2 := by
  have hc := direct_sum_mul_le s f h hA hB hf hh
  have heq : (∑ i ∈ s, (f i + h i) ^ 2) =
      (∑ i ∈ s, f i ^ 2) + 2 * (∑ i ∈ s, f i * h i) + ∑ i ∈ s, h i ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [heq]
  nlinarith

/-- Both available oscillatory square estimates are retained, with no phase or parity condition. -/
theorem direct_neutral_sq_sum_le (a ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hne : 1 - ζ ^ 2 ≠ 0) (m : ℕ) :
    (∑ i ∈ Finset.range m, (a * ζ ^ i).re ^ 2) ≤
      (‖a‖ * directOscillationFactor ζ m) ^ 2 := by
  have hfirst : (∑ i ∈ Finset.range m, (a * ζ ^ i).re ^ 2) ≤ ‖a‖ ^ 2 * (m : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range m, ‖a‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh : |(a * ζ ^ i).re| ≤ ‖a‖ := by
          simpa only [norm_mul, norm_pow, hζ, one_pow, mul_one] using
            Complex.abs_re_le_norm (a * ζ ^ i)
        nlinarith [sq_abs (a * ζ ^ i).re, norm_nonneg a, abs_nonneg (a * ζ ^ i).re]
      _ = _ := by simp [mul_comm]
  have hsecond := neutral_sq_sum_le a ζ hζ hne m
  rw [mul_pow, directOscillationFactor_sq]
  by_cases hm : (m : ℝ) ≤ (m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖
  · rw [min_eq_left hm]
    exact hfirst
  · rw [min_eq_right (le_of_not_ge hm)]
    exact hsecond

theorem direct_neutral_shift_sq_sum_le (a ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hne : 1 - ζ ^ 2 ≠ 0) (s m : ℕ) {Δ : ℝ} (ha : ‖a‖ ≤ Δ) :
    (∑ i ∈ Finset.range m, neutralMode a ζ ((s + i : ℕ) : ℤ) ^ 2) ≤
      (Δ * directOscillationFactor ζ m) ^ 2 := by
  have h := direct_neutral_sq_sum_le (a * ζ ^ s) ζ hζ hne m
  have hn : ‖a * ζ ^ s‖ ≤ Δ := by simpa [norm_mul, norm_pow, hζ] using ha
  have heq (i : ℕ) : neutralMode a ζ ((s + i : ℕ) : ℤ) = ((a * ζ ^ s) * ζ ^ i).re := by
    simp only [neutralMode, zpow_natCast, pow_add, mul_assoc]
  simp_rw [heq]
  apply h.trans
  exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (directOscillationFactor_nonneg ζ m))
    (mul_le_mul_of_nonneg_right hn (directOscillationFactor_nonneg ζ m)) 2

/-- Exact geometric square sums after any nonnegative shift. -/
theorem direct_scaled_geometric_sq_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (b : ℝ) (s m : ℕ) :
    (∑ i ∈ Finset.range m, (b * r ^ (s + i)) ^ 2) =
      (|b| * r ^ s * directGeometricFactor r m) ^ 2 := by
  calc
    _ = (b * r ^ s) ^ 2 * (∑ i ∈ Finset.range m, (r ^ i) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = _ := by rw [← directGeometricFactor_sq hr0 hr1 m]; simp [mul_pow]

theorem direct_geometric_sq_sum_le {r τ b : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : |b| ≤ τ) (s m : ℕ) :
    (∑ i ∈ Finset.range m, (b * r ^ (s + i)) ^ 2) ≤
      (τ * r ^ s * directGeometricFactor r m) ^ 2 := by
  rw [direct_scaled_geometric_sq_sum hr0 hr1 b s m]
  apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg (abs_nonneg b) (pow_nonneg hr0 s))
    (directGeometricFactor_nonneg r m))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (pow_nonneg hr0 s)) (directGeometricFactor_nonneg r m)

theorem directActionConstant_nonneg (R : ℝ) : 0 ≤ directActionConstant R := by
  unfold directActionConstant cosineCurvatureBound
  positivity

/-- The source core constant is at most 104 on every radius at most 0.4. -/
theorem direct_core_constant_le_104 {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 2 / 5) :
    directActionConstant R ≤ 104 := by
  have harg : |Real.pi * R| ≤ (3927 / 1250 : ℝ) * (2 / 5) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hR0]
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hcos := cos_lower_degree_six_of_abs_le harg
    (show (3927 / 1250 : ℝ) * (2 / 5) ≤ Real.pi / 2 by nlinarith [Real.pi_gt_three])
  have hbound : (3088 / 10000 : ℝ) ≤ Real.cos (Real.pi * R) := by
    apply le_trans (show (3088 / 10000 : ℝ) ≤
      1 - ((3927 / 1250 : ℝ) * (2 / 5)) ^ 2 / 2 +
      ((3927 / 1250 : ℝ) * (2 / 5)) ^ 4 / 24 -
      ((3927 / 1250 : ℝ) * (2 / 5)) ^ 6 / 720 by norm_num) hcos
  have h := cosineCurvatureBound_le_of_cos_lower R (3088 / 10000) 208
    (by norm_num) hbound (by norm_num) (by nlinarith [Real.pi_lt_d4, Real.pi_pos])
  unfold directActionConstant
  linarith

/-- The squared derivative norm is bounded by the actual core action. -/
theorem direct_core_slope_sq_sum_le {ι : Type*} (s : Finset ι) (Y : ι → ℝ)
    {R C : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 2)
    (hcurv : cosineCurvatureBound R ≤ 2 * C) (hY : ∀ i ∈ s, |Y i| ≤ R) :
    (∑ i ∈ s, cosinePotentialSlope (Y i) ^ 2) ≤
      4 * C * (∑ i ∈ s, cosinePotential (Y i)) := by
  have hE : 0 ≤ ∑ i ∈ s, cosinePotential (Y i) :=
    Finset.sum_nonneg (fun _ _ => cosinePotential_nonneg _)
  calc
    _ ≤ ∑ i ∈ s, 2 * cosineCurvatureBound R * cosinePotential (Y i) :=
      Finset.sum_le_sum (fun i hi => cosinePotentialSlope_sq_le_action R (Y i) hR0 hR (hY i hi))
    _ = 2 * cosineCurvatureBound R * (∑ i ∈ s, cosinePotential (Y i)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE

/-- The source finite-core Taylor/Cauchy--Schwarz estimate for an actual perturbation. -/
theorem direct_core_perturbation_sum_le {ι : Type*} (s : Finset ι) (Y u : ι → ℝ)
    {R C α : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 2) (hC : 0 ≤ C)
    (hcurv : cosineCurvatureBound R ≤ 2 * C) (hα : 0 ≤ α)
    (hY : ∀ i ∈ s, |Y i| ≤ R) (hYu : ∀ i ∈ s, |Y i + u i| ≤ R)
    (hu : ∑ i ∈ s, u i ^ 2 ≤ α ^ 2) :
    (∑ i ∈ s, cosinePotential (Y i + u i)) ≤
      (∑ i ∈ s, cosinePotential (Y i)) +
      2 * Real.sqrt (C * (∑ i ∈ s, cosinePotential (Y i))) * α + C * α ^ 2 := by
  let E := ∑ i ∈ s, cosinePotential (Y i)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => cosinePotential_nonneg _)
  have hCE : 0 ≤ C * E := mul_nonneg hC hE
  have hslope : (∑ i ∈ s, cosinePotentialSlope (Y i) ^ 2) ≤
      (2 * Real.sqrt (C * E)) ^ 2 := by
    calc
      _ ≤ 4 * C * E := direct_core_slope_sq_sum_le s Y hR0 hR hcurv hY
      _ = _ := by rw [mul_pow, Real.sq_sqrt hCE]; ring
  have hcross := direct_sum_mul_le s (fun i => cosinePotentialSlope (Y i)) u
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hα hslope hu
  have hu0 : 0 ≤ ∑ i ∈ s, u i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hquad : cosineCurvatureBound R / 2 * (∑ i ∈ s, u i ^ 2) ≤ C * α ^ 2 :=
    mul_le_mul (by linarith) hu hu0 hC
  have hpoint := Finset.sum_le_sum (fun i hi =>
    cosinePotential_taylor_le_radius R (Y i) (u i) hR0 hR (hY i hi) (hYu i hi))
  have heq : (∑ i ∈ s, (cosinePotential (Y i) + cosinePotentialSlope (Y i) * u i +
      cosineCurvatureBound R / 2 * u i ^ 2)) =
      E + (∑ i ∈ s, cosinePotentialSlope (Y i) * u i) +
        cosineCurvatureBound R / 2 * (∑ i ∈ s, u i ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [heq] at hpoint
  linarith

noncomputable def directAlpha1 (τ r : ℝ) (ell g : ℕ) : ℝ :=
  τ * r ^ (g + 1) * directGeometricFactor r ell

noncomputable def directAlpha2 (Δ τ r : ℝ) (ζ : ℂ) (ell g : ℕ) : ℝ :=
  Δ * directOscillationFactor ζ ell + τ * r ^ g * directGeometricFactor r ell

noncomputable def directAlphaGap (Δ τ r : ℝ) (ζ : ℂ) (g : ℕ) : ℝ :=
  Δ * directOscillationFactor ζ g + τ * (1 + r) * directGeometricFactor r g

noncomputable def directFirstPerturbation (aMinus r : ℝ) (ell g i : ℕ) : ℝ :=
  -aMinus * r ^ (ell + g - i)

noncomputable def directSecondPerturbation (a : ℂ) (aPlus r : ℝ) (ζ : ℂ) (ell g i : ℕ) : ℝ :=
  neutralMode a ζ ((ell + g + i : ℕ) : ℤ) + aPlus * r ^ (g + i)

noncomputable def directGapTerm (a : ℂ) (aMinus aPlus r : ℝ) (ζ : ℂ) (ell g i : ℕ) : ℝ :=
  neutralMode a ζ ((ell + i : ℕ) : ℤ) + aPlus * r ^ i - aMinus * r ^ (g - i)

theorem directAlpha1_nonneg {τ r : ℝ} (hτ : 0 ≤ τ) (hr : 0 ≤ r) (ell g : ℕ) :
    0 ≤ directAlpha1 τ r ell g :=
  mul_nonneg (mul_nonneg hτ (pow_nonneg hr _)) (directGeometricFactor_nonneg r ell)

theorem directAlpha2_nonneg {Δ τ r : ℝ} (hΔ : 0 ≤ Δ) (hτ : 0 ≤ τ) (hr : 0 ≤ r)
    (ζ : ℂ) (ell g : ℕ) : 0 ≤ directAlpha2 Δ τ r ζ ell g :=
  add_nonneg (mul_nonneg hΔ (directOscillationFactor_nonneg ζ ell))
    (mul_nonneg (mul_nonneg hτ (pow_nonneg hr _)) (directGeometricFactor_nonneg r ell))

theorem directAlphaGap_nonneg {Δ τ r : ℝ} (hΔ : 0 ≤ Δ) (hτ : 0 ≤ τ) (hr : 0 ≤ r)
    (ζ : ℂ) (g : ℕ) : 0 ≤ directAlphaGap Δ τ r ζ g :=
  add_nonneg (mul_nonneg hΔ (directOscillationFactor_nonneg ζ g))
    (mul_nonneg (mul_nonneg hτ (by linarith)) (directGeometricFactor_nonneg r g))

/-- The first core perturbation has exactly the short geometric norm from the source. -/
theorem direct_first_perturbation_sq_sum_le {r τ aMinus : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hMinus : |aMinus| ≤ τ) (ell g : ℕ) :
    (∑ i ∈ Finset.range ell, directFirstPerturbation aMinus r ell g i ^ 2) ≤
      directAlpha1 τ r ell g ^ 2 := by
  have heq : (∑ i ∈ Finset.range ell, directFirstPerturbation aMinus r ell g i ^ 2) =
      ∑ i ∈ Finset.range ell, (-aMinus * r ^ ((g + 1) + i)) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range ell, (-aMinus * r ^ ((g + 1) + (ell - 1 - i))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.1 hi
        unfold directFirstPerturbation
        rw [show ell + g - i = (g + 1) + (ell - 1 - i) by omega]
      _ = _ := Finset.sum_range_reflect (fun i => (-aMinus * r ^ ((g + 1) + i)) ^ 2) ell
  rw [heq]
  exact direct_geometric_sq_sum_le hr0 hr1 (by simpa only [abs_neg] using hMinus) (g + 1) ell

/-- The translated core retains the source sum of neutral and stable square norms. -/
theorem direct_second_perturbation_sq_sum_le {r τ Δ aPlus : ℝ} (a ζ : ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ) (ell g : ℕ) :
    (∑ i ∈ Finset.range ell, directSecondPerturbation a aPlus r ζ ell g i ^ 2) ≤
      directAlpha2 Δ τ r ζ ell g ^ 2 := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  exact direct_sum_add_sq_le (Finset.range ell)
    (fun i => neutralMode a ζ ((ell + g + i : ℕ) : ℤ))
    (fun i => aPlus * r ^ (g + i))
    (mul_nonneg hΔ (directOscillationFactor_nonneg ζ ell))
    (mul_nonneg (mul_nonneg hτ (pow_nonneg hr0 g)) (directGeometricFactor_nonneg r ell))
    (direct_neutral_shift_sq_sum_le a ζ hζ hne (ell + g) ell ha)
    (direct_geometric_sq_sum_le hr0 hr1 hPlus g ell)

/-- The gap combines the half-density neutral norm with the two exact finite geometric tails. -/
theorem direct_gap_sq_sum_le {r τ Δ aMinus aPlus : ℝ} (a ζ : ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ) (ell g : ℕ) :
    (∑ i ∈ Finset.range g, directGapTerm a aMinus aPlus r ζ ell g i ^ 2) ≤
      directAlphaGap Δ τ r ζ g ^ 2 := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hA0 : 0 ≤ Δ * directOscillationFactor ζ g :=
    mul_nonneg hΔ (directOscillationFactor_nonneg ζ g)
  have hB0 : 0 ≤ τ * directGeometricFactor r g := mul_nonneg hτ (directGeometricFactor_nonneg r g)
  have hC0 : 0 ≤ τ * r * directGeometricFactor r g :=
    mul_nonneg (mul_nonneg hτ hr0) (directGeometricFactor_nonneg r g)
  have hplus := direct_sum_add_sq_le (Finset.range g)
    (fun i => neutralMode a ζ ((ell + i : ℕ) : ℤ)) (fun i => aPlus * r ^ i) hA0 hB0
    (direct_neutral_shift_sq_sum_le a ζ hζ hne ell g ha)
    (by simpa only [zero_add, pow_zero, mul_one] using direct_geometric_sq_sum_le hr0 hr1 hPlus 0 g)
  have hleft : (∑ i ∈ Finset.range g, (-aMinus * r ^ (g - i)) ^ 2) ≤
      (τ * r * directGeometricFactor r g) ^ 2 := by
    simpa only [directFirstPerturbation, directAlpha1, add_zero, zero_add, pow_one] using
      direct_first_perturbation_sq_sum_le hr0 hr1 hMinus g 0
  have h := direct_sum_add_sq_le (Finset.range g)
    (fun i => neutralMode a ζ ((ell + i : ℕ) : ℤ) + aPlus * r ^ i)
    (fun i => -aMinus * r ^ (g - i)) (add_nonneg hA0 hB0) hC0 hplus hleft
  have heq : Δ * directOscillationFactor ζ g + τ * directGeometricFactor r g +
      τ * r * directGeometricFactor r g = directAlphaGap Δ τ r ζ g := by
    unfold directAlphaGap
    ring
  rw [heq] at h
  simpa only [directGapTerm, sub_eq_add_neg, neg_mul] using h

theorem direct_first_perturbation_abs_le {r τ aMinus : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hMinus : |aMinus| ≤ τ)
    (ell g i : ℕ) (hi : i < ell) :
    |directFirstPerturbation aMinus r ell g i| ≤ τ * r ^ g := by
  unfold directFirstPerturbation
  rw [abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hr0 _)]
  calc
    _ ≤ τ * r ^ (ell + g - i) :=
      mul_le_mul_of_nonneg_right hMinus (pow_nonneg hr0 _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1.le (by omega)) hτ

theorem direct_second_perturbation_abs_le {r τ Δ aPlus : ℝ} (a ζ : ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (ha : ‖a‖ ≤ Δ) (ell g i : ℕ) :
    |directSecondPerturbation a aPlus r ζ ell g i| ≤ Δ + τ * r ^ g := by
  have hs : |aPlus * r ^ (g + i)| ≤ τ * r ^ g := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 _)]
    exact (mul_le_mul_of_nonneg_right hPlus (pow_nonneg hr0 _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1.le (by omega)) hτ)
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_neutralMode_le a ζ hζ _).trans ha) hs)

theorem direct_gap_abs_le {r τ Δ aMinus aPlus : ℝ} (a ζ : ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (ha : ‖a‖ ≤ Δ) (ell g i : ℕ) :
    |directGapTerm a aMinus aPlus r ζ ell g i| ≤ 2 * Δ + 2 * τ := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hb (b : ℝ) (hb : |b| ≤ τ) (j : ℕ) : |b * r ^ j| ≤ τ := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 _)]
    exact (mul_le_mul_of_nonneg_right hb (pow_nonneg hr0 _)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) hτ)
  have hn := (abs_neutralMode_le a ζ hζ ((ell + i : ℕ) : ℤ)).trans ha
  have hp := hb aPlus hPlus i
  have hm := hb aMinus hMinus (g - i)
  have hh : |neutralMode a ζ ((ell + i : ℕ) : ℤ) + aPlus * r ^ i -
      aMinus * r ^ (g - i)| ≤
      |neutralMode a ζ ((ell + i : ℕ) : ℤ) + aPlus * r ^ i| + |aMinus * r ^ (g - i)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (neutralMode a ζ ((ell + i : ℕ) : ℤ) + aPlus * r ^ i)
        (-(aMinus * r ^ (g - i)))
  have hh' := abs_add_le (neutralMode a ζ ((ell + i : ℕ) : ℤ)) (aPlus * r ^ i)
  unfold directGapTerm
  linarith

/-- The first actual core is the original core plus its exact incoming-tail perturbation. -/
theorem directDifference_first_core_eq (Y : ℤ → ℝ) (b aMinus : ℝ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (ell g i : ℕ) (hi : i < ell) :
    mirrorDifference Y ((ell + g : ℕ) : ℤ) i =
      Y i + directFirstPerturbation aMinus b⁻¹ ell g i := by
  have hneg : (i : ℤ) - ((ell + g : ℕ) : ℤ) < 0 := by omega
  unfold mirrorDifference directFirstPerturbation
  rw [hleft _ hneg,
    show (i : ℤ) - ((ell + g : ℕ) : ℤ) = -((ell + g - i : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, ← inv_pow]
  ring

/-- The translated actual core is the negative original core plus its exact outgoing tail. -/
theorem directDifference_second_core_eq (Y : ℤ → ℝ) (b aPlus : ℝ) (a ζ : ℂ)
    (ell g i : ℕ)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell)) :
    mirrorDifference Y ((ell + g : ℕ) : ℤ) ((ell + g + i : ℕ) : ℤ) =
      -Y i + directSecondPerturbation a aPlus b⁻¹ ζ ell g i := by
  unfold mirrorDifference directSecondPerturbation
  rw [hright _ (by omega),
    show ((ell + g + i : ℕ) : ℤ) - (ell : ℤ) = ((g + i : ℕ) : ℤ) by omega,
    show ((ell + g + i : ℕ) : ℤ) - ((ell + g : ℕ) : ℤ) = (i : ℤ) by omega,
    zpow_natCast]
  ring

/-- The actual gap has exactly the three source terms, without any reflection or parity input. -/
theorem directDifference_gap_eq (Y : ℤ → ℝ) (b aMinus aPlus : ℝ) (a ζ : ℂ)
    (ell g i : ℕ) (hi : i < g)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell)) :
    mirrorDifference Y ((ell + g : ℕ) : ℤ) ((ell + i : ℕ) : ℤ) =
      directGapTerm a aMinus aPlus b⁻¹ ζ ell g i := by
  have hneg : ((ell + i : ℕ) : ℤ) - ((ell + g : ℕ) : ℤ) < 0 := by omega
  unfold mirrorDifference directGapTerm
  rw [hright _ (by omega), hleft _ hneg,
    show ((ell + i : ℕ) : ℤ) - (ell : ℤ) = (i : ℤ) by omega,
    show ((ell + i : ℕ) : ℤ) - ((ell + g : ℕ) : ℤ) = -((g - i : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow]

/-- The quadratic source bound follows from Taylor's theorem at the origin. -/
theorem direct_potential_le_quadratic_radius {R u : ℝ}
    (hR0 : 0 ≤ R) (hR : R < 1 / 2) (hu : |u| ≤ R) :
    cosinePotential u ≤ directActionConstant R * u ^ 2 := by
  have h := cosinePotential_taylor_le_radius R 0 u hR0 hR (by simpa) (by simpa using hu)
  simpa [cosinePotential, cosinePotentialSlope, directActionConstant] using h

/-- Finite square bounds become action bounds with the certified radius constant. -/
theorem direct_gap_action_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    {R α : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 2)
    (hu : ∀ i ∈ s, |u i| ≤ R) (hsq : ∑ i ∈ s, u i ^ 2 ≤ α ^ 2) :
    (∑ i ∈ s, cosinePotential (u i)) ≤ directActionConstant R * α ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, directActionConstant R * u i ^ 2 :=
      Finset.sum_le_sum (fun i hi => direct_potential_le_quadratic_radius hR0 hR (hu i hi))
    _ = directActionConstant R * (∑ i ∈ s, u i ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (directActionConstant_nonneg R)

/-- The sharp small-gap estimate retains the source constant 9.87. -/
theorem direct_small_gap_action_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    {α : ℝ} (hu : ∀ i ∈ s, |u i| ≤ 1 / 1000)
    (hsq : ∑ i ∈ s, u i ^ 2 ≤ α ^ 2) :
    (∑ i ∈ s, cosinePotential (u i)) ≤ (987 / 100 : ℝ) * α ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, (987 / 100 : ℝ) * u i ^ 2 :=
      Finset.sum_le_sum (fun i hi => cosinePotential_le_quadratic (hu i hi))
    _ = (987 / 100 : ℝ) * (∑ i ∈ s, u i ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- The two original cores and the intervening gap exactly partition the new core. -/
theorem direct_action_partition (Y : ℤ → ℝ) (ell g : ℕ) :
    (∑ i ∈ Finset.range (ell + (ell + g)), cosinePotential (Y i)) =
      (∑ i ∈ Finset.range ell, cosinePotential (Y i)) +
      (∑ i ∈ Finset.range ell, cosinePotential (Y ((ell + g + i : ℕ) : ℤ))) +
      (∑ i ∈ Finset.range g, cosinePotential (Y ((ell + i : ℕ) : ℤ))) := by
  rw [show ell + (ell + g) = (ell + g) + ell by omega,
    Finset.sum_range_add, Finset.sum_range_add]
  ring

/-- The actual finite core action, without a separate numerical cap. -/
noncomputable def directCoreAction (Y : ℤ → ℝ) (ell : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ell, cosinePotential (Y i)

theorem directCoreAction_nonneg (Y : ℤ → ℝ) (ell : ℕ) : 0 ≤ directCoreAction Y ell :=
  Finset.sum_nonneg (fun _ _ => cosinePotential_nonneg _)

/-- Both actual core blocks satisfy the source Taylor/Cauchy estimate. -/
theorem direct_two_core_action_sum_le (Y : ℤ → ℝ) (a ζ : ℂ)
    {b aMinus aPlus τ Δ aStar C : ℝ} (ell g : ℕ)
    (hb : 1 < b) (hτ : 0 ≤ τ) (haStar : 0 ≤ aStar)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (hcore : ∀ i : ℕ, i < ell → |Y i| ≤ aStar)
    (hmc : aStar + Δ + τ * b⁻¹ ^ g < 1 / 2)
    (hC : 0 ≤ C) (hcurv : cosineCurvatureBound (aStar + Δ + τ * b⁻¹ ^ g) ≤ 2 * C) :
    (∑ i ∈ Finset.range ell, cosinePotential (mirrorDifference Y ((ell + g : ℕ) : ℤ) i)) +
      (∑ i ∈ Finset.range ell,
        cosinePotential (mirrorDifference Y ((ell + g : ℕ) : ℤ) ((ell + g + i : ℕ) : ℤ))) ≤
      2 * directCoreAction Y ell +
      2 * Real.sqrt (C * directCoreAction Y ell) *
        (directAlpha1 τ b⁻¹ ell g + directAlpha2 Δ τ b⁻¹ ζ ell g) +
      C * (directAlpha1 τ b⁻¹ ell g ^ 2 + directAlpha2 Δ τ b⁻¹ ζ ell g ^ 2) := by
  have hr0 : 0 ≤ b⁻¹ := (inv_pos.2 (by linarith : 0 < b)).le
  have hr1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have htail : 0 ≤ τ * b⁻¹ ^ g := mul_nonneg hτ (pow_nonneg hr0 _)
  have hmc0 : 0 ≤ aStar + Δ + τ * b⁻¹ ^ g := by positivity
  have hY (i : ℕ) (hi : i ∈ Finset.range ell) :
      |Y i| ≤ aStar + Δ + τ * b⁻¹ ^ g := by
    have hc := hcore i (Finset.mem_range.1 hi)
    linarith
  have hfirstEnd (i : ℕ) (hi : i ∈ Finset.range ell) :
      |Y i + directFirstPerturbation aMinus b⁻¹ ell g i| ≤
        aStar + Δ + τ * b⁻¹ ^ g := by
    have hc := hcore i (Finset.mem_range.1 hi)
    have hu := direct_first_perturbation_abs_le hr0 hr1 hτ hMinus ell g i (Finset.mem_range.1 hi)
    have ht := abs_add_le (Y i) (directFirstPerturbation aMinus b⁻¹ ell g i)
    linarith
  have hsecondEnd (i : ℕ) (hi : i ∈ Finset.range ell) :
      |-Y i + directSecondPerturbation a aPlus b⁻¹ ζ ell g i| ≤
        aStar + Δ + τ * b⁻¹ ^ g := by
    have hc := hcore i (Finset.mem_range.1 hi)
    have hu := direct_second_perturbation_abs_le a ζ hr0 hr1 hτ hPlus hζ ha ell g i
    have ht := abs_add_le (-Y i) (directSecondPerturbation a aPlus b⁻¹ ζ ell g i)
    rw [abs_neg] at ht
    linarith
  have hfirst := direct_core_perturbation_sum_le (Finset.range ell) (fun i => Y i)
    (directFirstPerturbation aMinus b⁻¹ ell g) hmc0 hmc hC hcurv
    (directAlpha1_nonneg hτ hr0 ell g) hY hfirstEnd
    (direct_first_perturbation_sq_sum_le hr0 hr1 hMinus ell g)
  have hsecond := direct_core_perturbation_sum_le (Finset.range ell) (fun i => -Y i)
    (directSecondPerturbation a aPlus b⁻¹ ζ ell g) hmc0 hmc hC hcurv
    (directAlpha2_nonneg hΔ hτ hr0 ζ ell g)
    (fun i hi => by simpa only [abs_neg] using hY i hi) hsecondEnd
    (direct_second_perturbation_sq_sum_le a ζ hr0 hr1 hτ hPlus hζ hne ha ell g)
  have hneg (u : ℝ) : cosinePotential (-u) = cosinePotential u :=
    cosinePotential_eq_of_abs_eq (-u) u (abs_neg u)
  simp only [hneg] at hsecond
  have heq1 : (∑ i ∈ Finset.range ell,
      cosinePotential (mirrorDifference Y ((ell + g : ℕ) : ℤ) i)) =
      ∑ i ∈ Finset.range ell, cosinePotential (Y i + directFirstPerturbation aMinus b⁻¹ ell g i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [directDifference_first_core_eq Y b aMinus hleft ell g i (Finset.mem_range.1 hi)]
  have heq2 : (∑ i ∈ Finset.range ell,
      cosinePotential (mirrorDifference Y ((ell + g : ℕ) : ℤ) ((ell + g + i : ℕ) : ℤ))) =
      ∑ i ∈ Finset.range ell,
        cosinePotential (-Y i + directSecondPerturbation a aPlus b⁻¹ ζ ell g i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [directDifference_second_core_eq Y b aPlus a ζ ell g i hright]
  rw [heq1, heq2]
  unfold directCoreAction
  nlinarith [hfirst, hsecond]

/-- Analytic constants may be supplied separately from the actual trajectory data. -/
theorem direct_difference_action_le_of_constants (Y : ℤ → ℝ) (a ζ : ℂ)
    {b aMinus aPlus τ Δ aStar Ccore Cgap : ℝ} (ell g : ℕ)
    (hb : 1 < b) (hτ : 0 ≤ τ) (haStar : 0 ≤ aStar)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (hcore : ∀ i : ℕ, i < ell → |Y i| ≤ aStar)
    (hmc : aStar + Δ + τ * b⁻¹ ^ g < 1 / 2)
    (hCcore : 0 ≤ Ccore)
    (hcurv : cosineCurvatureBound (aStar + Δ + τ * b⁻¹ ^ g) ≤ 2 * Ccore)
    (hCgap : 0 ≤ Cgap)
    (hquad : ∀ u : ℝ, |u| ≤ 2 * Δ + 2 * τ → cosinePotential u ≤ Cgap * u ^ 2) :
    directCoreAction (mirrorDifference Y ((ell + g : ℕ) : ℤ)) (ell + (ell + g)) ≤
      2 * directCoreAction Y ell +
      2 * Real.sqrt (Ccore * directCoreAction Y ell) *
        (directAlpha1 τ b⁻¹ ell g + directAlpha2 Δ τ b⁻¹ ζ ell g) +
      Ccore * (directAlpha1 τ b⁻¹ ell g ^ 2 + directAlpha2 Δ τ b⁻¹ ζ ell g ^ 2) +
      Cgap * directAlphaGap Δ τ b⁻¹ ζ g ^ 2 := by
  have hr0 : 0 ≤ b⁻¹ := (inv_pos.2 (by linarith : 0 < b)).le
  have hr1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  have hcores := direct_two_core_action_sum_le Y a ζ ell g hb hτ haStar hMinus hPlus
    hζ hne ha hleft hright hcore hmc hCcore hcurv
  have hgap : (∑ i ∈ Finset.range g,
      cosinePotential (mirrorDifference Y ((ell + g : ℕ) : ℤ) ((ell + i : ℕ) : ℤ))) ≤
      Cgap * directAlphaGap Δ τ b⁻¹ ζ g ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range g, cosinePotential (directGapTerm a aMinus aPlus b⁻¹ ζ ell g i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [directDifference_gap_eq Y b aMinus aPlus a ζ ell g i (Finset.mem_range.1 hi) hleft hright]
      _ ≤ ∑ i ∈ Finset.range g, Cgap * directGapTerm a aMinus aPlus b⁻¹ ζ ell g i ^ 2 :=
        Finset.sum_le_sum (fun i _ => hquad _
          (direct_gap_abs_le a ζ hr0 hr1 hτ hMinus hPlus hζ ha ell g i))
      _ = Cgap * (∑ i ∈ Finset.range g, directGapTerm a aMinus aPlus b⁻¹ ζ ell g i ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (direct_gap_sq_sum_le a ζ hr0 hr1 hτ hMinus hPlus hζ hne ha ell g) hCgap
  unfold directCoreAction
  rw [direct_action_partition]
  exact add_le_add hcores hgap

/-- The source direct-difference action estimate, derived from the actual tails and core. -/
theorem direct_difference_action_le (Y : ℤ → ℝ) (a ζ : ℂ)
    {b aMinus aPlus τ Δ aStar : ℝ} (ell g : ℕ)
    (hb : 1 < b) (hτ : 0 ≤ τ) (haStar : 0 ≤ aStar)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (hcore : ∀ i : ℕ, i < ell → |Y i| ≤ aStar)
    (hmc : aStar + Δ + τ * b⁻¹ ^ g < 1 / 2) (hmg : 2 * Δ + 2 * τ < 1 / 2) :
    directCoreAction (mirrorDifference Y ((ell + g : ℕ) : ℤ)) (ell + (ell + g)) ≤
      2 * directCoreAction Y ell +
      2 * Real.sqrt (directActionConstant (aStar + Δ + τ * b⁻¹ ^ g) * directCoreAction Y ell) *
        (directAlpha1 τ b⁻¹ ell g + directAlpha2 Δ τ b⁻¹ ζ ell g) +
      directActionConstant (aStar + Δ + τ * b⁻¹ ^ g) *
        (directAlpha1 τ b⁻¹ ell g ^ 2 + directAlpha2 Δ τ b⁻¹ ζ ell g ^ 2) +
      directActionConstant (2 * Δ + 2 * τ) * directAlphaGap Δ τ b⁻¹ ζ g ^ 2 := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  exact direct_difference_action_le_of_constants Y a ζ ell g hb hτ haStar hMinus hPlus
    hζ hne ha hleft hright hcore hmc (directActionConstant_nonneg _) (by
      unfold directActionConstant
      linarith) (directActionConstant_nonneg _)
    (fun u hu => direct_potential_le_quadratic_radius (by positivity) hmg hu)

/-- The certified constants 104 and 9.87 apply to the actual P2-sized radii. -/
theorem direct_difference_action_le_104_small_gap (Y : ℤ → ℝ) (a ζ : ℂ)
    {b aMinus aPlus τ Δ aStar : ℝ} (ell g : ℕ)
    (hb : 1 < b) (hτ : 0 ≤ τ) (haStar : 0 ≤ aStar)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (hcore : ∀ i : ℕ, i < ell → |Y i| ≤ aStar)
    (hmc : aStar + Δ + τ * b⁻¹ ^ g ≤ 2 / 5) (hmg : 2 * Δ + 2 * τ ≤ 1 / 1000) :
    directCoreAction (mirrorDifference Y ((ell + g : ℕ) : ℤ)) (ell + (ell + g)) ≤
      2 * directCoreAction Y ell +
      2 * Real.sqrt (104 * directCoreAction Y ell) *
        (directAlpha1 τ b⁻¹ ell g + directAlpha2 Δ τ b⁻¹ ζ ell g) +
      104 * (directAlpha1 τ b⁻¹ ell g ^ 2 + directAlpha2 Δ τ b⁻¹ ζ ell g ^ 2) +
      (987 / 100 : ℝ) * directAlphaGap Δ τ b⁻¹ ζ g ^ 2 := by
  have hr0 : 0 ≤ b⁻¹ := (inv_pos.2 (by linarith : 0 < b)).le
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hmc0 : 0 ≤ aStar + Δ + τ * b⁻¹ ^ g := by positivity
  have hcurv := direct_core_constant_le_104 hmc0 hmc
  apply direct_difference_action_le_of_constants Y a ζ ell g hb hτ haStar hMinus hPlus
    hζ hne ha hleft hright hcore (by linarith) (by norm_num)
    (by unfold directActionConstant at hcurv; linarith) (by norm_num)
  intro u hu
  exact cosinePotential_le_quadratic (hu.trans hmg)

/-- A certified core cap increases only the core-dependent terms of the source bound. -/
theorem direct_action_bound_mono_core {E Ecap Ccore Cgap α1 α2 αgap : ℝ}
    (hE : E ≤ Ecap) (hC : 0 ≤ Ccore) (hα1 : 0 ≤ α1) (hα2 : 0 ≤ α2) :
    2 * E + 2 * Real.sqrt (Ccore * E) * (α1 + α2) +
      Ccore * (α1 ^ 2 + α2 ^ 2) + Cgap * αgap ^ 2 ≤
    2 * Ecap + 2 * Real.sqrt (Ccore * Ecap) * (α1 + α2) +
      Ccore * (α1 ^ 2 + α2 ^ 2) + Cgap * αgap ^ 2 := by
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE hC)
  have hcross := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)) (add_nonneg hα1 hα2)
  linarith

/-- The numerical core certificate supplies only an upper bound for the actual core action. -/
theorem direct_difference_action_le_104_small_gap_of_core_le (Y : ℤ → ℝ) (a ζ : ℂ)
    {b aMinus aPlus τ Δ aStar Ecap : ℝ} (ell g : ℕ)
    (hb : 1 < b) (hτ : 0 ≤ τ) (haStar : 0 ≤ aStar)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (ha : ‖a‖ ≤ Δ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (hcore : ∀ i : ℕ, i < ell → |Y i| ≤ aStar)
    (hmc : aStar + Δ + τ * b⁻¹ ^ g ≤ 2 / 5) (hmg : 2 * Δ + 2 * τ ≤ 1 / 1000)
    (hEcap : directCoreAction Y ell ≤ Ecap) :
    directCoreAction (mirrorDifference Y ((ell + g : ℕ) : ℤ)) (ell + (ell + g)) ≤
      2 * Ecap + 2 * Real.sqrt (104 * Ecap) *
        (directAlpha1 τ b⁻¹ ell g + directAlpha2 Δ τ b⁻¹ ζ ell g) +
      104 * (directAlpha1 τ b⁻¹ ell g ^ 2 + directAlpha2 Δ τ b⁻¹ ζ ell g ^ 2) +
      (987 / 100 : ℝ) * directAlphaGap Δ τ b⁻¹ ζ g ^ 2 := by
  have hr0 : 0 ≤ b⁻¹ := (inv_pos.2 (by linarith : 0 < b)).le
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  exact (direct_difference_action_le_104_small_gap Y a ζ ell g hb hτ haStar hMinus hPlus
    hζ hne ha hleft hright hcore hmc hmg).trans
    (direct_action_bound_mono_core hEcap (by norm_num)
      (directAlpha1_nonneg hτ hr0 ell g) (directAlpha2_nonneg hΔ hτ hr0 ζ ell g))

/-- Delaying by at least the old core length places the two forcing supports in the new core. -/
theorem directDifference_forcing_supported (p0 p1 p2 p3 : ℤ) (Y : ℤ → ℝ) (ell g : ℕ)
    (hsupport : ∀ j : ℤ, j < 0 ∨ (ell : ℤ) ≤ j → quarticResidual p0 p1 p2 p3 Y j = 0) :
    ∀ j : ℤ, j < 0 ∨ ((ell + (ell + g) : ℕ) : ℤ) ≤ j →
      quarticResidual p0 p1 p2 p3 (mirrorDifference Y ((ell + g : ℕ) : ℤ)) j = 0 := by
  intro j hj
  rw [quarticResidual_mirrorDifference]
  have hj1 : j < 0 ∨ (ell : ℤ) ≤ j := by omega
  have hj2 : j - ((ell + g : ℕ) : ℤ) < 0 ∨ (ell : ℤ) ≤ j - ((ell + g : ℕ) : ℤ) := by omega
  rw [hsupport j hj1, hsupport _ hj2, sub_self]

/-- The disjoint translates cannot cancel an actual nonzero old forcing. -/
theorem directDifference_forcing_nonzero (p0 p1 p2 p3 : ℤ) (Y : ℤ → ℝ) (ell g : ℕ)
    (hsupport : ∀ j : ℤ, j < 0 ∨ (ell : ℤ) ≤ j → quarticResidual p0 p1 p2 p3 Y j = 0)
    (hnonzero : ∃ j : ℤ, quarticResidual p0 p1 p2 p3 Y j ≠ 0) :
    ∃ j : ℤ, quarticResidual p0 p1 p2 p3 (mirrorDifference Y ((ell + g : ℕ) : ℤ)) j ≠ 0 := by
  obtain ⟨j, hj⟩ := hnonzero
  have hjrange : ¬(j < 0 ∨ (ell : ℤ) ≤ j) := fun h => hj (hsupport j h)
  have hshift : j - ((ell + g : ℕ) : ℤ) < 0 := by omega
  refine ⟨j, ?_⟩
  rw [quarticResidual_mirrorDifference, hsupport _ (Or.inl hshift), sub_zero]
  exact hj

/-- The actual difference stays in the canonical centered interval, including both exterior tails. -/
theorem directDifference_abs_lt_half (Y : ℤ → ℝ) (a ζ : ℂ)
    {b aMinus aPlus τ Δ aStar : ℝ} (ell g : ℕ)
    (hb : 1 < b) (hτ : 0 ≤ τ)
    (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ)
    (hζ : ‖ζ‖ = 1) (ha : ‖a‖ ≤ Δ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (hcore : ∀ i : ℕ, i < ell → |Y i| ≤ aStar)
    (hmc : aStar + Δ + τ * b⁻¹ ^ g < 1 / 2) (hmg : 2 * Δ + 2 * τ < 1 / 2) :
    ∀ j : ℤ, |mirrorDifference Y ((ell + g : ℕ) : ℤ) j| < 1 / 2 := by
  have hb0 : 0 < b := by linarith
  have hr0 : 0 < b⁻¹ := inv_pos.2 hb0
  have hr1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hleftAbs (j : ℤ) (hj : j < 0) : |Y j| ≤ τ := by
    rw [hleft j hj, abs_mul, abs_of_pos (zpow_pos hb0 _)]
    calc
      _ ≤ τ * b ^ j := mul_le_mul_of_nonneg_right hMinus (zpow_pos hb0 _).le
      _ ≤ τ * 1 := mul_le_mul_of_nonneg_left (zpow_le_one_of_nonpos₀ hb.le hj.le) hτ
      _ = τ := mul_one _
  have hrightAbs (j : ℤ) (hj : (ell : ℤ) ≤ j) : |Y j| ≤ Δ + τ := by
    have hp : |aPlus * b⁻¹ ^ (j - ell)| ≤ τ := by
      rw [abs_mul, abs_of_pos (zpow_pos hr0 _)]
      calc
        _ ≤ τ * b⁻¹ ^ (j - ell) := mul_le_mul_of_nonneg_right hPlus (zpow_pos hr0 _).le
        _ ≤ τ * 1 := mul_le_mul_of_nonneg_left (zpow_le_one₀ hr0 hr1.le (by omega)) hτ
        _ = τ := mul_one _
    rw [hright j hj]
    exact (abs_add_le _ _).trans (add_le_add ((abs_neutralMode_le a ζ hζ j).trans ha) hp)
  intro j
  by_cases hj0 : j < 0
  · have hjshift : j - ((ell + g : ℕ) : ℤ) < 0 := by omega
    have ht : |mirrorDifference Y ((ell + g : ℕ) : ℤ) j| ≤ 2 * τ := by
      unfold mirrorDifference
      have htri : |Y j - Y (j - ((ell + g : ℕ) : ℤ))| ≤
          |Y j| + |Y (j - ((ell + g : ℕ) : ℤ))| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (Y j) (-Y (j - ((ell + g : ℕ) : ℤ)))
      linarith [hleftAbs j hj0, hleftAbs _ hjshift]
    linarith
  · lift j to ℕ using (by omega : 0 ≤ j)
    by_cases hjell : j < ell
    · rw [directDifference_first_core_eq Y b aMinus hleft ell g j hjell]
      have hu := direct_first_perturbation_abs_le hr0.le hr1 hτ hMinus ell g j hjell
      have hc := hcore j hjell
      have ht := abs_add_le (Y j) (directFirstPerturbation aMinus b⁻¹ ell g j)
      linarith
    · by_cases hjL : j < ell + g
      · have ht : j - ell < g := by omega
        have heq : ell + (j - ell) = j := by omega
        have hcoup := directDifference_gap_eq Y b aMinus aPlus a ζ ell g (j - ell) ht hleft hright
        rw [heq] at hcoup
        rw [hcoup]
        exact (direct_gap_abs_le a ζ hr0.le hr1 hτ hMinus hPlus hζ ha ell g (j - ell)).trans_lt hmg
      · by_cases hjend : j < ell + (ell + g)
        · have ht : j - (ell + g) < ell := by omega
          have heq : ell + g + (j - (ell + g)) = j := by omega
          have hcoup := directDifference_second_core_eq Y b aPlus a ζ ell g (j - (ell + g)) hright
          rw [heq] at hcoup
          rw [hcoup]
          have hu := direct_second_perturbation_abs_le a ζ hr0.le hr1 hτ hPlus hζ ha ell g (j - (ell + g))
          have hc := hcore (j - (ell + g)) ht
          have htri := abs_add_le (-Y ((j - (ell + g) : ℕ) : ℤ))
            (directSecondPerturbation a aPlus b⁻¹ ζ ell g (j - (ell + g)))
          rw [abs_neg] at htri
          linarith
        · have h1 : (ell : ℤ) ≤ (j : ℤ) := by omega
          have h2 : (ell : ℤ) ≤ (j : ℤ) - ((ell + g : ℕ) : ℤ) := by omega
          unfold mirrorDifference
          have htri : |Y j - Y ((j : ℤ) - ((ell + g : ℕ) : ℤ))| ≤
              |Y j| + |Y ((j : ℤ) - ((ell + g : ℕ) : ℤ))| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (Y j) (-Y ((j : ℤ) - ((ell + g : ℕ) : ℤ)))
          linarith [hrightAbs j h1, hrightAbs _ h2]

/-- The actual incoming real coefficient is multiplied by the source factor. -/
theorem directDifference_incoming (Y : ℤ → ℝ) {b : ℝ} (hb : b ≠ 0) (aMinus : ℝ)
    (ell g : ℕ) (hleft : ∀ j : ℤ, j < 0 → Y j = aMinus * b ^ j)
    (j : ℤ) (hj : j < 0) :
    mirrorDifference Y ((ell + g : ℕ) : ℤ) j =
      (aMinus * (1 - b⁻¹ ^ (ell + g))) * b ^ j := by
  have hshift : j - ((ell + g : ℕ) : ℤ) < 0 := by omega
  unfold mirrorDifference
  rw [hleft j hj, hleft _ hshift]
  exact expanding_mirror_difference b aMinus hb (ell + g) j

/-- The actual outgoing stable and neutral coefficients are the two source updates. -/
theorem directDifference_outgoing (Y : ℤ → ℝ) {b : ℝ} (hb : b ≠ 0) (aPlus : ℝ) (a ζ : ℂ)
    (hζ : ζ ≠ 0) (ell g : ℕ)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = neutralMode a ζ j + aPlus * b⁻¹ ^ (j - ell))
    (j : ℤ) (hj : ((ell + (ell + g) : ℕ) : ℤ) ≤ j) :
    mirrorDifference Y ((ell + g : ℕ) : ℤ) j =
      neutralMode (mirrorNeutralCoefficient a ζ ((ell + g : ℕ) : ℤ)) ζ j +
        (aPlus * (b⁻¹ ^ (ell + g) - 1)) * b⁻¹ ^ (j - ((ell + (ell + g) : ℕ) : ℤ)) := by
  have hj1 : (ell : ℤ) ≤ j := by omega
  have hj2 : (ell : ℤ) ≤ j - ((ell + g : ℕ) : ℤ) := by omega
  have he1 : j - (ell : ℤ) = ((ell + g : ℕ) : ℤ) +
      (j - ((ell + (ell + g) : ℕ) : ℤ)) := by omega
  have he2 : j - ((ell + g : ℕ) : ℤ) - (ell : ℤ) =
      j - ((ell + (ell + g) : ℕ) : ℤ) := by omega
  unfold mirrorDifference
  rw [hright j hj1, hright _ hj2, he1, he2, zpow_add₀ (inv_ne_zero hb), zpow_natCast,
    ← neutralMode_mirror_difference a ζ hζ ((ell + g : ℕ) : ℤ) j]
  ring

/-- Both actual real-tail updates decrease the modulus of their old coefficients. -/
theorem direct_real_tail_coefficients_le {b aMinus aPlus τ : ℝ}
    (hb : 1 < b) (hMinus : |aMinus| ≤ τ) (hPlus : |aPlus| ≤ τ) (L : ℕ) :
    |aMinus * (1 - b⁻¹ ^ L)| ≤ τ ∧ |aPlus * (b⁻¹ ^ L - 1)| ≤ τ := by
  have hr0 : 0 ≤ b⁻¹ := (inv_pos.2 (by linarith : 0 < b)).le
  have hp0 : 0 ≤ b⁻¹ ^ L := pow_nonneg hr0 _
  have hp1 : b⁻¹ ^ L ≤ 1 := pow_le_one₀ hr0 (inv_lt_one_of_one_lt₀ hb).le
  have hf1 : |1 - b⁻¹ ^ L| ≤ 1 := (abs_le).2 ⟨by linarith, by linarith⟩
  have hf2 : |b⁻¹ ^ L - 1| ≤ 1 := (abs_le).2 ⟨by linarith, by linarith⟩
  constructor
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hf1 (abs_nonneg aMinus)).trans (by simpa using hMinus)
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hf2 (abs_nonneg aPlus)).trans (by simpa using hPlus)

end Salem
