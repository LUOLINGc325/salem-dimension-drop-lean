module

public import Salem.DirectDifferenceAction
public import Salem.P2RootFactorization

@[expose] public section

namespace Salem

/-- The direct Taylor constant remains at most104 on the perturbed source
core radius0.400005. -/
theorem p2Direct_core_constant_le_104 {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ 80001/200000) :
    directActionConstant R ≤ 104 := by
  have harg : |Real.pi * R| ≤ (3927 / 1250 : ℝ) * (80001/200000) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hR0]
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hcos := cos_lower_degree_six_of_abs_le harg
    (show (3927 / 1250 : ℝ) * (80001/200000) ≤ Real.pi / 2 by
      nlinarith [Real.pi_gt_three])
  have hbound : (3088 / 10000 : ℝ) ≤ Real.cos (Real.pi * R) := by
    apply le_trans (show (3088 / 10000 : ℝ) ≤
      1 - ((3927 / 1250 : ℝ) * (80001/200000)) ^ 2 / 2 +
      ((3927 / 1250 : ℝ) * (80001/200000)) ^ 4 / 24 -
      ((3927 / 1250 : ℝ) * (80001/200000)) ^ 6 / 720 by norm_num) hcos
  have h := cosineCurvatureBound_le_of_cos_lower R (3088 / 10000) 208
    (by norm_num) hbound (by norm_num) (by nlinarith [Real.pi_lt_d4, Real.pi_pos])
  unfold directActionConstant
  linarith

/-- Every finite geometric square norm is at most5/4 for r≤3/5. -/
theorem p2Direct_geometric_factor_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (m : ℕ) :
    directGeometricFactor r m ≤ 5/4 := by
  have hr1 : r ≤ 1 := by linarith
  have hr2 : r^2 ≤ (9/25 : ℝ) := by nlinarith
  have hp0 : 0 ≤ r^(2*m) := pow_nonneg hr0 _
  have hp1 : r^(2*m) ≤ 1 := pow_le_one₀ hr0 hr1
  have hden : 0 < 1-r^2 := by linarith
  have hq0 : 0 ≤ (1-r^(2*m))/(1-r^2) := div_nonneg (by linarith) hden.le
  have hq : (1-r^(2*m))/(1-r^2) ≤ (25/16 : ℝ) :=
    (div_le_iff₀ hden).2 (by nlinarith)
  have hs := Real.sq_sqrt hq0
  have hn := Real.sqrt_nonneg ((1-r^(2*m))/(1-r^2))
  unfold directGeometricFactor
  nlinarith

/-- The source oscillatory square norm follows from the actual unit-root gap,
retaining the half-density term. -/
theorem p2Direct_oscillation_factor_le (ζ : ℂ) (hd : 19/10 ≤ ‖1-ζ^2‖)
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (hnum : (m : ℝ)/2+10/19 ≤ B^2) :
    directOscillationFactor ζ m ≤ B := by
  have hden : 0 < ‖1-ζ^2‖ := by linarith
  have hinv : 1/‖1-ζ^2‖ ≤ (10/19 : ℝ) :=
    (div_le_iff₀ hden).2 (by linarith)
  have hsq := directOscillationFactor_sq ζ m
  have hmin := min_le_right (m : ℝ) ((m : ℝ)/2+1/‖1-ζ^2‖)
  have hn := directOscillationFactor_nonneg ζ m
  nlinarith

/-- The actual explicit P₂ unit root has the exact source spectral-gap square. -/
theorem p2CoefficientZeta_gap_sq :
    ‖1-p2CoefficientZeta^2‖^2 = 1+2*Real.sqrt 2 := by
  have hs : (Real.sqrt 2 : ℝ)^2 = 2 := by norm_num
  have hu : p2CoefficientZeta.re^2+p2CoefficientZeta.im^2 = 1 := by
    have h := congrArg (fun x : ℝ => x^2) p2CoefficientZeta_unit.1
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hr : p2CoefficientZeta.re = (1-Real.sqrt 2)/2 := rfl
  have hsquare : (p2CoefficientZeta.re^2+p2CoefficientZeta.im^2)^2 = 1 := by rw [hu]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [hu, hsquare]

/-- In particular the actual P₂ neutral root has gap strictly greater than1.9. -/
theorem p2CoefficientZeta_gap_gt : (19/10 : ℝ) < ‖1-p2CoefficientZeta^2‖ := by
  have hs : (Real.sqrt 2 : ℝ)^2 = 2 := by norm_num
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hslo : (7/5 : ℝ) < Real.sqrt 2 := by nlinarith
  nlinarith [p2CoefficientZeta_gap_sq, norm_nonneg (1-p2CoefficientZeta^2)]

/-- The actual first-core geometric perturbation fits the source alpha1 cap. -/
theorem p2Direct_alpha1_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    directAlpha1 (1/10^24) r 2885 1846079336 ≤ (1/10^10 : ℝ) := by
  have hA := p2Direct_geometric_factor_le r hr0 hr 2885
  have hA0 := directGeometricFactor_nonneg r 2885
  have hp : r^(1846079336+1) ≤ 1 := pow_le_one₀ hr0 (by linarith)
  unfold directAlpha1
  calc
    _ ≤ (1/10^24 : ℝ)*1*(5/4) := by gcongr
    _ ≤ _ := by norm_num

/-- The actual P₂ second-core perturbation fits the178e−6 alpha2 cap. -/
theorem p2Direct_alpha2_bound (Δ r : ℝ) (hΔ : Δ ≤ 4674807/10^12)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    directAlpha2 Δ (1/10^24) r p2CoefficientZeta 2885 1846079336 ≤ (178/10^6 : ℝ) := by
  have hA := p2Direct_geometric_factor_le r hr0 hr 2885
  have hA0 := directGeometricFactor_nonneg r 2885
  have hZ := p2Direct_oscillation_factor_le p2CoefficientZeta
    p2CoefficientZeta_gap_gt.le 2885 38 (by norm_num) (by norm_num)
  have hZ0 := directOscillationFactor_nonneg p2CoefficientZeta 2885
  have hp : r^1846079336 ≤ 1 := pow_le_one₀ hr0 (by linarith)
  unfold directAlpha2
  calc
    _ ≤ (4674807/10^12 : ℝ)*38+(1/10^24)*1*(5/4) := by gcongr
    _ ≤ _ := by norm_num

/-- The actual long P₂ bridge retains the source half-density alpha-gap cap. -/
theorem p2Direct_alphaGap_bound (Δ r : ℝ) (hΔ : Δ ≤ 4674807/10^12)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    directAlphaGap Δ (1/10^24) r p2CoefficientZeta 1846079336 ≤ (142031/10^6 : ℝ) := by
  have hA := p2Direct_geometric_factor_le r hr0 hr 1846079336
  have hA0 := directGeometricFactor_nonneg r 1846079336
  have hZ := p2Direct_oscillation_factor_le p2CoefficientZeta
    p2CoefficientZeta_gap_gt.le 1846079336 30382 (by norm_num) (by norm_num)
  have hZ0 := directOscillationFactor_nonneg p2CoefficientZeta 1846079336
  unfold directAlphaGap
  calc
    _ ≤ (4674807/10^12 : ℝ)*30382+(1/10^24)*(1+3/5)*(5/4) := by gcongr
    _ ≤ _ := by norm_num

/-- The source core cap gives the needed coefficient100 in the Taylor cross term. -/
theorem p2Direct_sqrt_core_bound (C E : ℝ) (hC : C ≤ 104)
    (hE0 : 0 ≤ E) (hE : E ≤ 4743/200) : Real.sqrt (C*E) ≤ 50 := by
  have hm : C*E ≤ (2500 : ℝ) := by
    calc
      _ ≤ (104 : ℝ)*(4743/200) := mul_le_mul hC hE hE0 (by norm_num)
      _ ≤ _ := by norm_num
  have h := Real.sqrt_le_sqrt hm
  norm_num at h
  exact h

/-- The explicit fresh P₂ direct-difference budget is strictly below47.647. -/
theorem p2Direct_scalar_comparison :
    2*(4743/200 : ℝ) + 100*((1/10^10 : ℝ)+178/10^6) +
      104*((1/10^10 : ℝ)^2+(178/10^6)^2) +
      (987/100 : ℝ)*(142031/10^6)^2 < 47647/1000 := by norm_num

/-- The actual direct-difference action formula, under the certified source
parameter bounds, is strictly below47.647. The finite-core action cap remains
an explicit input to be supplied by the independent finite computation. -/
theorem p2Direct_action_budget_lt (E C G α1 α2 αg : ℝ)
    (hE0 : 0 ≤ E) (hE : E ≤ 4743/200) (hC : C ≤ 104) (hG : G ≤ 987/100)
    (hα10 : 0 ≤ α1) (hα1 : α1 ≤ 1/10^10)
    (hα20 : 0 ≤ α2) (hα2 : α2 ≤ 178/10^6)
    (hαg0 : 0 ≤ αg) (hαg : αg ≤ 142031/10^6) :
    2*E + 2*Real.sqrt (C*E)*(α1+α2) + C*(α1^2+α2^2) + G*αg^2 < 47647/1000 := by
  have hs := p2Direct_sqrt_core_bound C E hC hE0 hE
  calc
    _ ≤ 2*(4743/200 : ℝ) + 2*50*((1/10^10 : ℝ)+178/10^6) +
        104*((1/10^10 : ℝ)^2+(178/10^6)^2) +
        (987/100 : ℝ)*(142031/10^6)^2 := by gcongr
    _ = 2*(4743/200 : ℝ) + 100*((1/10^10 : ℝ)+178/10^6) +
        104*((1/10^10 : ℝ)^2+(178/10^6)^2) +
        (987/100 : ℝ)*(142031/10^6)^2 := by ring
    _ < _ := p2Direct_scalar_comparison

/-- The source core maximum and neutral amplitude imply the two perturbed
radius bounds used by the core Taylor and sharp gap estimates. -/
theorem p2Direct_radii_bounds (aStar Δ r : ℝ)
    (haStar : aStar ≤ 2/5) (hΔ : Δ ≤ 4674807/10^12)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    aStar+Δ+(1/10^24 : ℝ)*r^1846079336 ≤ 80001/200000 ∧
      2*Δ+2*(1/10^24 : ℝ) ≤ 1/1000 := by
  have hp : r^1846079336 ≤ 1 := pow_le_one₀ hr0 (by linarith)
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1/10^24)
  constructor <;> linarith

/-- The full localized action includes the already certified stable-tail budget. -/
theorem p2Direct_scalar_comparison_with_tails :
    2*(4743/200 : ℝ) + 100*((1/10^10 : ℝ)+178/10^6) +
      104*((1/10^10 : ℝ)^2+(178/10^6)^2) +
      (987/100 : ℝ)*(142031/10^6)^2 + 275/10^49 < 47647/1000 := by norm_num

/-- The exact source alphas and localized stable tails produce the complete
47.647 action allowance; only the independent finite-core action cap is required. -/
theorem p2Direct_source_full_budget_lt (E Δ r T : ℝ)
    (hE0 : 0 ≤ E) (hE : E ≤ 4743/200)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 4674807/10^12)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hT : T ≤ 275/10^49) :
    2*E + 2*Real.sqrt (104*E)*
      (directAlpha1 (1/10^24) r 2885 1846079336 +
        directAlpha2 Δ (1/10^24) r p2CoefficientZeta 2885 1846079336) +
      104*(directAlpha1 (1/10^24) r 2885 1846079336 ^ 2 +
        directAlpha2 Δ (1/10^24) r p2CoefficientZeta 2885 1846079336 ^ 2) +
      (987/100 : ℝ)*directAlphaGap Δ (1/10^24) r p2CoefficientZeta 1846079336 ^ 2 + T <
        47647/1000 := by
  have h1 := p2Direct_alpha1_bound r hr0 hr
  have h2 := p2Direct_alpha2_bound Δ r hΔ hr0 hr
  have hg := p2Direct_alphaGap_bound Δ r hΔ hr0 hr
  have h10 := directAlpha1_nonneg (by norm_num : (0 : ℝ) ≤ 1/10^24) hr0 2885 1846079336
  have h20 := directAlpha2_nonneg hΔ0 (by norm_num : (0 : ℝ) ≤ 1/10^24)
    hr0 p2CoefficientZeta 2885 1846079336
  have hg0 := directAlphaGap_nonneg hΔ0 (by norm_num : (0 : ℝ) ≤ 1/10^24)
    hr0 p2CoefficientZeta 1846079336
  have hs := p2Direct_sqrt_core_bound 104 E le_rfl hE0 hE
  calc
    _ ≤ 2*(4743/200 : ℝ) + 2*50*((1/10^10 : ℝ)+178/10^6) +
        104*((1/10^10 : ℝ)^2+(178/10^6)^2) +
        (987/100 : ℝ)*(142031/10^6)^2 + 275/10^49 := by gcongr
    _ = 2*(4743/200 : ℝ) + 100*((1/10^10 : ℝ)+178/10^6) +
        104*((1/10^10 : ℝ)^2+(178/10^6)^2) +
        (987/100 : ℝ)*(142031/10^6)^2 + 275/10^49 := by ring
    _ < _ := p2Direct_scalar_comparison_with_tails

end Salem
