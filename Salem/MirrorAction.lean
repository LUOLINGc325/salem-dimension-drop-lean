module

public import Salem.Restoration

@[expose] public section

open scoped BigOperators
open Set Filter Topology

namespace Salem

/-- The full neutral mode, before choosing a localized outgoing switch point. -/
noncomputable def neutralMode (z ζ : ℂ) (j : ℤ) : ℝ := (z * ζ ^ j).re

/-- The actual coefficient of the neutral difference mode. -/
noncomputable def mirrorNeutralCoefficient (z ζ : ℂ) (L : ℤ) : ℂ :=
  z * (1 - ζ ^ (-L))

/-- The actual difference trajectory, not a newly assumed centered profile. -/
noncomputable def mirrorDifference (Y : ℤ → ℝ) (L j : ℤ) : ℝ :=
  Y j - Y (j-L)

/-- Taking a delayed difference multiplies the full neutral coefficient by its
 exact return factor. -/
theorem neutralMode_mirror_difference (z ζ : ℂ) (hζ : ζ ≠ 0) (L j : ℤ) :
    neutralMode z ζ j - neutralMode z ζ (j-L) =
      neutralMode (mirrorNeutralCoefficient z ζ L) ζ j := by
  unfold neutralMode mirrorNeutralCoefficient
  rw [← Complex.sub_re]
  congr 1
  rw [show j-L = j+(-L) by ring, zpow_add₀ hζ]
  ring

/-- Unit-circle inversion preserves the exact return distance. -/
theorem norm_inverse_return (ζ : ℂ) (hζ : ‖ζ‖ = 1) (L : ℤ) :
    ‖1 - ζ ^ (-L)‖ = ‖1 - ζ ^ L‖ := by
  have hne : ζ ≠ 0 := by intro he; simp [he] at hζ
  have hp : ζ ^ L ≠ 0 := zpow_ne_zero L hne
  rw [zpow_neg]
  have heq : 1 - (ζ^L)⁻¹ = (ζ^L-1)/(ζ^L) := by field_simp
  rw [heq, norm_div, norm_zpow, hζ, one_zpow, div_one, norm_sub_rev]

/-- The new neutral amplitude is derived from the actual old mode coefficient. -/
theorem norm_mirrorNeutralCoefficient (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (L : ℤ) :
    ‖mirrorNeutralCoefficient z ζ L‖ = ‖z‖ * ‖1 - ζ ^ L‖ := by
  rw [mirrorNeutralCoefficient, norm_mul, norm_inverse_return ζ hζ L]

/-- The exact incoming real-tail coefficient of a delayed difference. -/
theorem expanding_mirror_difference (b c : ℝ) (hb : b ≠ 0) (L : ℕ) (j : ℤ) :
    c*b^j - c*b^(j-(L : ℤ)) = (c*(1-b⁻¹^L))*b^j := by
  rw [zpow_sub₀ hb]
  simp only [zpow_natCast, div_eq_mul_inv, inv_pow]
  ring

/-- Delayed differences preserve integer forcing with its actual shifted support. -/
theorem quarticResidual_mirrorDifference (p0 p1 p2 p3 : ℤ) (Y : ℤ → ℝ) (L j : ℤ) :
    quarticResidual p0 p1 p2 p3 (mirrorDifference Y L) j =
      quarticResidual p0 p1 p2 p3 Y j - quarticResidual p0 p1 p2 p3 Y (j-L) := by
  unfold quarticResidual mirrorDifference
  simp only [sub_add_eq_add_sub]
  ring

/-- Actual integer forcing of the original trajectory gives actual integer
 forcing of its mirror difference; no localized junction is omitted. -/
theorem mirrorDifference_integer_forcing (p0 p1 p2 p3 : ℤ) (Y : ℤ → ℝ) (L : ℤ)
    (hY : ∀ j : ℤ, ∃ m : ℤ, quarticResidual p0 p1 p2 p3 Y j = m) :
    ∀ j : ℤ, ∃ m : ℤ, quarticResidual p0 p1 p2 p3 (mirrorDifference Y L) j = m := by
  intro j
  obtain ⟨m, hm⟩ := hY j
  obtain ⟨m', hm'⟩ := hY (j-L)
  refine ⟨m-m', ?_⟩
  rw [quarticResidual_mirrorDifference, hm, hm']
  push_cast
  rfl

/-- Exact Fourier congruence is preserved by the true difference trajectory,
 with the derived incoming coefficient `c(1-r^L)`. -/
theorem mirrorDifference_congruent_expanding (b c : ℝ) (hb : b ≠ 0) (Y : ℤ → ℝ) (L : ℕ)
    (hY : ∀ j : ℤ, ∃ m : ℤ, Y j - c*b^j = m) :
    ∀ j : ℤ, ∃ m : ℤ,
      mirrorDifference Y L j - (c*(1-b⁻¹^L))*b^j = m := by
  intro j
  obtain ⟨m, hm⟩ := hY j
  obtain ⟨m', hm'⟩ := hY (j-(L : ℤ))
  refine ⟨m-m', ?_⟩
  have hexp := expanding_mirror_difference b c hb L j
  unfold mirrorDifference
  push_cast
  linarith

/-- The actual uniform second-derivative bound on a centered radius. -/
noncomputable def cosineCurvatureBound (R : ℝ) : ℝ :=
  2 * Real.pi ^ 2 / Real.cos (Real.pi*R) ^ 2

/-- Cosine stays positive and decreases with the absolute argument on a strict
 centered radius; this supplies all denominator and no-zero side conditions. -/
theorem cosine_radius_lower (R u : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ)) (hu : |u| ≤ R) :
    0 < Real.cos (Real.pi*R) ∧ Real.cos (Real.pi*R) ≤ Real.cos (Real.pi*u) := by
  have hpos : 0 < Real.cos (Real.pi*R) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  refine ⟨hpos, ?_⟩
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le (abs_nonneg u))
    (show Real.pi*R ≤ Real.pi by nlinarith [Real.pi_pos])
    (mul_le_mul_of_nonneg_left hu Real.pi_pos.le)
  have heq : Real.pi* |u| = |Real.pi*u| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rwa [heq, Real.cos_abs] at hc

/-- The exact second derivative is bounded by the actual secant-square constant. -/
theorem cosinePotential_second_le_radius (R u : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hu : |u| ≤ R) :
    0 ≤ 2 * Real.pi ^ 2 / Real.cos (Real.pi*u) ^ 2 ∧
      2 * Real.pi ^ 2 / Real.cos (Real.pi*u) ^ 2 ≤ cosineCurvatureBound R := by
  have hc := cosine_radius_lower R u hR0 hR hu
  have hpos : 0 < Real.cos (Real.pi*u) := hc.1.trans_le hc.2
  refine ⟨by positivity, ?_⟩
  unfold cosineCurvatureBound
  apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hc.1)
  nlinarith

/-- Smoothness of the actual potential on any strict centered radius. -/
theorem contDiffOn_cosinePotential_radius (n : ℕ∞) (R : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ)) :
    ContDiffOn ℝ n cosinePotential (Icc (-R) R) := by
  have hc : ContDiffOn ℝ n (fun u : ℝ => Real.cos (Real.pi*u)^2) (Icc (-R) R) := by fun_prop
  exact (hc.log (fun u hu => pow_ne_zero 2
    (ne_of_gt ((cosine_radius_lower R u hR0 hR (abs_le.mpr hu)).1.trans_le
      (cosine_radius_lower R u hR0 hR (abs_le.mpr hu)).2)))).neg

/-- The actual potential slope is Lipschitz on a strict centered radius. -/
theorem cosinePotentialSlope_lipschitz_radius (R x y : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |cosinePotentialSlope y - cosinePotentialSlope x| ≤ cosineCurvatureBound R * |y-x| := by
  have hne (u : ℝ) (hu : u ∈ Icc (-R) R) : Real.cos (Real.pi*u) ≠ 0 :=
    ne_of_gt ((cosine_radius_lower R u hR0 hR (abs_le.mpr hu)).1.trans_le
      (cosine_radius_lower R u hR0 hR (abs_le.mpr hu)).2)
  have hbound (u : ℝ) (hu : u ∈ Icc (-R) R) :
      ‖2 * Real.pi ^ 2 / Real.cos (Real.pi*u) ^ 2‖ ≤ cosineCurvatureBound R := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (cosinePotential_second_le_radius R u hR0 hR (abs_le.mpr hu)).2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_cosinePotentialSlope u (hne u hu)).hasDerivWithinAt)
    hbound (convex_Icc (-R) R) (abs_le.mp hx) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using h

/-- The linear bound on the actual slope starts at its exact zero at the origin. -/
theorem abs_cosinePotentialSlope_le_radius (R u : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hu : |u| ≤ R) : |cosinePotentialSlope u| ≤ cosineCurvatureBound R * |u| := by
  have h := cosinePotentialSlope_lipschitz_radius R 0 u hR0 hR (by simpa) hu
  simpa [cosinePotentialSlope] using h

/-- The actual one-sided Taylor bound on any strict centered radius. -/
theorem cosinePotential_taylor_le_radius (R x z : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hx : |x| ≤ R) (hxz : |x+z| ≤ R) :
    cosinePotential (x+z) ≤ cosinePotential x + cosinePotentialSlope x * z +
      cosineCurvatureBound R / 2 * z ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hseg : uIcc x (x+z) ⊆ Icc (-R) R := uIcc_subset_Icc (abs_le.mp hx) (abs_le.mp hxz)
  have hne : x ≠ x+z := by intro he; apply hz; linarith
  have hcos (u : ℝ) (hu : |u| ≤ R) : Real.cos (Real.pi*u) ≠ 0 :=
    ne_of_gt ((cosine_radius_lower R u hR0 hR hu).1.trans_le
      (cosine_radius_lower R u hR0 hR hu).2)
  have hd0 : iteratedDerivWithin 1 cosinePotential (uIcc x (x+z)) x = cosinePotentialSlope x := by
    rw [iteratedDerivWithin_one]
    exact (hasDerivAt_cosinePotential x (hcos x hx)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_uIcc hne) x left_mem_uIcc)
  have hpoly : taylorWithinEval cosinePotential 1 (uIcc x (x+z)) x (x+z) =
      cosinePotential x + cosinePotentialSlope x * z := by
    rw [show (1 : ℕ) = 0+1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd0]
    norm_num
    ring
  obtain ⟨u, hu, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := cosinePotential)
    (x₀ := x) (x := x+z) (n := 1) hne ((contDiffOn_cosinePotential_radius 2 R hR0 hR).mono hseg)
  have huabs : |u| ≤ R := abs_le.mpr (hseg (uIoo_subset_uIcc_self hu))
  rw [hpoly, iteratedDeriv_two_cosinePotential u (hcos u huabs)] at heq
  norm_num at heq
  have hsecond := (cosinePotential_second_le_radius R u hR0 hR huabs).2
  have hterm := mul_le_mul_of_nonneg_right hsecond (sq_nonneg z)
  nlinarith

/-- The exact mixed potential term is bounded by the uniform second derivative.
 This is derived from the mean value theorem rather than assumed as an action premise. -/
theorem cosinePotential_mixed_le_radius (R x z : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hxz : |x|+|z| ≤ R) :
    cosinePotential (x+z) ≤ cosinePotential x + cosinePotential z + cosineCurvatureBound R * |x*z| := by
  have hx : |x| ≤ R := by linarith [abs_nonneg z]
  have hz : |z| ≤ R := by linarith [abs_nonneg x]
  have hseg : uIcc 0 z ⊆ Icc (-|z|) |z| :=
    uIcc_subset_Icc (by constructor <;> linarith [abs_nonneg z]) (abs_le.mp le_rfl)
  have ht (t : ℝ) (ht : t ∈ uIcc 0 z) : |t| ≤ |z| := abs_le.mpr (hseg ht)
  have htR (t : ℝ) (ht' : t ∈ uIcc 0 z) : |t| ≤ R := (ht t ht').trans hz
  have hxtR (t : ℝ) (ht' : t ∈ uIcc 0 z) : |x+t| ≤ R :=
    (abs_add_le x t).trans ((add_le_add le_rfl (ht t ht')).trans hxz)
  have hcos (u : ℝ) (hu : |u| ≤ R) : Real.cos (Real.pi*u) ≠ 0 :=
    ne_of_gt ((cosine_radius_lower R u hR0 hR hu).1.trans_le
      (cosine_radius_lower R u hR0 hR hu).2)
  have hd (t : ℝ) (ht' : t ∈ uIcc 0 z) :
      HasDerivWithinAt (fun s => cosinePotential (x+s) - cosinePotential s)
        (cosinePotentialSlope (x+t) - cosinePotentialSlope t) (uIcc 0 z) t := by
    have h := ((hasDerivAt_cosinePotential (x+t) (hcos _ (hxtR t ht'))).comp t
      ((hasDerivAt_id t).const_add x)).sub (hasDerivAt_cosinePotential t (hcos _ (htR t ht')))
    convert h.hasDerivWithinAt using 1
    · funext s
      rfl
    · simp
  have hbound (t : ℝ) (ht' : t ∈ uIcc 0 z) :
      ‖cosinePotentialSlope (x+t) - cosinePotentialSlope t‖ ≤ cosineCurvatureBound R * |x| := by
    have h := cosinePotentialSlope_lipschitz_radius R t (x+t) hR0 hR (htR t ht') (hxtR t ht')
    simpa only [Real.norm_eq_abs, add_sub_cancel_right] using h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_uIcc 0 z)
    left_mem_uIcc right_mem_uIcc
  have hzero : cosinePotential 0 = 0 := by simp [cosinePotential]
  have ha : |cosinePotential (x+z) - cosinePotential z - cosinePotential x| ≤
      cosineCurvatureBound R * |x| * |z| := by
    simpa only [Real.norm_eq_abs, add_zero, sub_zero, hzero, mul_assoc] using h
  have hupper := (abs_le.mp ha).2
  rw [abs_mul]
  nlinarith

/-- The actual three-term bridge estimate separates its stable cross term,
 mixed neutral term, and sharp neutral square term. -/
theorem cosinePotential_gap_le_radius (R x z w : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hsmall : |x|+|z|+|w| ≤ R) :
    cosinePotential (x+z+w) - cosinePotential x - cosinePotential z ≤
      cosineCurvatureBound R * (|x*z| + (|x|+|z|)* |w| + w^2/2) := by
  have hC : 0 ≤ cosineCurvatureBound R := by unfold cosineCurvatureBound; positivity
  have hsum : |x|+|z| ≤ R := by linarith [abs_nonneg w]
  have hxz : |x+z| ≤ R := (abs_add_le x z).trans hsum
  have htotal : |x+z+w| ≤ R :=
    (abs_add_le (x+z) w).trans ((add_le_add (abs_add_le x z) le_rfl).trans hsmall)
  have hm := cosinePotential_mixed_le_radius R x z hR0 hR hsum
  have ht := cosinePotential_taylor_le_radius R (x+z) w hR0 hR hxz htotal
  have hs := abs_cosinePotentialSlope_le_radius R (x+z) hR0 hR hxz
  have hslope : cosinePotentialSlope (x+z)*w ≤ cosineCurvatureBound R*(|x|+|z|)* |w| := by
    calc
      _ ≤ |cosinePotentialSlope (x+z)*w| := le_abs_self _
      _ = |cosinePotentialSlope (x+z)| * |w| := abs_mul _ _
      _ ≤ (cosineCurvatureBound R* |x+z|)* |w| :=
        mul_le_mul_of_nonneg_right hs (abs_nonneg w)
      _ ≤ _ := by gcongr; exact abs_add_le x z
  nlinarith

/-- A positive rational lower bound for `1-π²R²` bounds the actual curvature. -/
theorem cosineCurvatureBound_le_of_radius_sq (R S P C : ℝ)
    (hR2 : R^2 ≤ S) (hpi : Real.pi^2 ≤ P) (hP : 0 ≤ P)
    (hden : 0 < 1-P*S) (hC : 0 ≤ C) (hcheck : 2*P ≤ C*(1-P*S)) :
    cosineCurvatureBound R ≤ C := by
  have hm := mul_le_mul hpi hR2 (sq_nonneg R) hP
  have hs := Real.sin_sq_le_sq (x := Real.pi*R)
  have hlower : 1-P*S ≤ Real.cos (Real.pi*R)^2 := by
    nlinarith [Real.cos_sq_add_sin_sq (Real.pi*R)]
  unfold cosineCurvatureBound
  apply (div_le_iff₀ (hden.trans_le hlower)).2
  have hmul := mul_le_mul_of_nonneg_left hlower hC
  nlinarith

/-- First-gap curvature with room for the full actual `Δ₀+2hr`, not a shortened radius. -/
theorem mirror_curvature_first_le (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ (223/10000 : ℝ)) :
    cosineCurvatureBound R ≤ (496/25 : ℝ) := by
  apply cosineCurvatureBound_le_of_radius_sq R ((223/10000 : ℝ)^2)
    ((31416/10000 : ℝ)^2) (496/25)
  · nlinarith
  · nlinarith [Real.pi_lt_d4, Real.pi_pos]
  all_goals norm_num

/-- The second-gap constant is strictly more precise than the restoration constant20. -/
theorem mirror_curvature_second_le (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ (121/10000 : ℝ)) :
    cosineCurvatureBound R ≤ (1977/100 : ℝ) := by
  apply cosineCurvatureBound_le_of_radius_sq R ((121/10000 : ℝ)^2)
    ((31416/10000 : ℝ)^2) (1977/100)
  · nlinarith
  · nlinarith [Real.pi_lt_d4, Real.pi_pos]
  all_goals norm_num

/-- An actual positive cosine enclosure controls curvature up to the core boundary. -/
theorem cosineCurvatureBound_le_of_cos_lower (R q C : ℝ) (hq : 0 < q)
    (hcos : q ≤ Real.cos (Real.pi*R)) (hC : 0 ≤ C) (hnum : 2*Real.pi^2 ≤ C*q^2) :
    cosineCurvatureBound R ≤ C := by
  have hc : 0 < Real.cos (Real.pi*R) := hq.trans_le hcos
  unfold cosineCurvatureBound
  apply (div_le_iff₀ (sq_pos_of_pos hc)).2
  have hs : q^2 ≤ Real.cos (Real.pi*R)^2 := by nlinarith
  exact hnum.trans (mul_le_mul_of_nonneg_left hs hC)

/-- The core Taylor radius supplied by a boundary distance `0.078` has curvature≤1350. -/
theorem mirror_core_curvature_le (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ (461/1000 : ℝ)) :
    cosineCurvatureBound R ≤ 1350 := by
  have harg : |Real.pi*R| ≤ (31416/10000 : ℝ)*(461/1000 : ℝ) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hR0]
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hcos := cos_lower_degree_six_of_abs_le harg
    (show (31416/10000 : ℝ)*(461/1000 : ℝ) ≤ Real.pi/2 by nlinarith [Real.pi_gt_three])
  have hbound : (121/1000 : ℝ) ≤ Real.cos (Real.pi*R) := by
    apply le_trans (show (121/1000 : ℝ) ≤
      1 - ((31416/10000 : ℝ)*(461/1000 : ℝ))^2/2 +
      ((31416/10000 : ℝ)*(461/1000 : ℝ))^4/24 -
      ((31416/10000 : ℝ)*(461/1000 : ℝ))^6/720 by norm_num) hcos
  apply cosineCurvatureBound_le_of_cos_lower R (121/1000) 1350 (by norm_num) hbound (by norm_num)
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

/-- The old core radius0.422 gives the actual `mathcal C` bound170; the potential
 second derivative is twice this constant. -/
theorem mirror_old_core_curvature_le (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ (211/500 : ℝ)) :
    cosineCurvatureBound R ≤ 340 := by
  have harg : |Real.pi*R| ≤ (31416/10000 : ℝ)*(211/500 : ℝ) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hR0]
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hcos := cos_lower_degree_six_of_abs_le harg
    (show (31416/10000 : ℝ)*(211/500 : ℝ) ≤ Real.pi/2 by nlinarith [Real.pi_gt_three])
  have hbound : (241/1000 : ℝ) ≤ Real.cos (Real.pi*R) := by
    apply le_trans (show (241/1000 : ℝ) ≤
      1 - ((31416/10000 : ℝ)*(211/500 : ℝ))^2/2 +
      ((31416/10000 : ℝ)*(211/500 : ℝ))^4/24 -
      ((31416/10000 : ℝ)*(211/500 : ℝ))^6/720 by norm_num) hcos
  apply cosineCurvatureBound_le_of_cos_lower R (241/1000) 340 (by norm_num) hbound (by norm_num)
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

/-- The actual potential dominates the squared sine, provided the cosine is nonzero. -/
theorem sin_sq_le_cosinePotential (u : ℝ) (hu : Real.cos (Real.pi*u) ≠ 0) :
    Real.sin (Real.pi*u)^2 ≤ cosinePotential u := by
  have hlog := Real.log_le_sub_one_of_pos (sq_pos_of_ne_zero hu)
  unfold cosinePotential
  nlinarith [Real.cos_sq_add_sin_sq (Real.pi*u)]

/-- The actual slope-square/action comparison used in the core Cauchy-Schwarz bound. -/
theorem cosinePotentialSlope_sq_le_action (R u : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hu : |u| ≤ R) :
    cosinePotentialSlope u ^ 2 ≤ 2 * cosineCurvatureBound R * cosinePotential u := by
  have hc := cosine_radius_lower R u hR0 hR hu
  have hcos : Real.cos (Real.pi*u) ≠ 0 := ne_of_gt (hc.1.trans_le hc.2)
  have hV := sin_sq_le_cosinePotential u hcos
  have hsecond := cosinePotential_second_le_radius R u hR0 hR hu
  have heq : cosinePotentialSlope u^2 =
      2 * (2*Real.pi^2/Real.cos (Real.pi*u)^2) * Real.sin (Real.pi*u)^2 := by
    unfold cosinePotentialSlope
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [heq]
  gcongr
  · linarith [hsecond.1, hsecond.2]
  · exact hsecond.2

/-- The core derivative sum is controlled by actual core action through
 Cauchy-Schwarz, with no assumed derivative certificate. -/
theorem core_slope_sum_sq_le {ι : Type*} (s : Finset ι) (Y : ι → ℝ)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ)) (hY : ∀ i ∈ s, |Y i| ≤ R) :
    (∑ i ∈ s, |cosinePotentialSlope (Y i)|)^2 ≤
      2 * cosineCurvatureBound R * (s.card : ℝ) * (∑ i ∈ s, cosinePotential (Y i)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => |cosinePotentialSlope (Y i)|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hp : (∑ i ∈ s, cosinePotentialSlope (Y i)^2) ≤
      2*cosineCurvatureBound R*(∑ i ∈ s, cosinePotential (Y i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => cosinePotentialSlope_sq_le_action R (Y i) hR0 hR (hY i hi))
  calc
    _ ≤ (∑ i ∈ s, cosinePotentialSlope (Y i)^2) * (s.card : ℝ) := hcs
    _ ≤ (2*cosineCurvatureBound R*(∑ i ∈ s, cosinePotential (Y i))) * (s.card : ℝ) := by gcongr
    _ = _ := by ring

/-- A concrete finite first core with the freshly certified action has derivative sum<473. -/
theorem mirror_first_core_slope_sum_lt (Y : Fin 27 → ℝ)
    (hY : ∀ i, |Y i| ≤ (211/500 : ℝ))
    (hE : (∑ i, cosinePotential (Y i)) ≤ (2429771/200000 : ℝ)) :
    (∑ i, |cosinePotentialSlope (Y i)|) < 473 := by
  have hsq := core_slope_sum_sq_le Finset.univ Y (211/500) (by norm_num) (by norm_num)
    (fun i _ => hY i)
  have hC := mirror_old_core_curvature_le (211/500) (by norm_num) le_rfl
  have hEnonneg : 0 ≤ ∑ i, cosinePotential (Y i) := by
    apply Finset.sum_nonneg
    intro i hi
    unfold cosinePotential
    exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hsq
  have hm := mul_le_mul_of_nonneg_right hC hEnonneg
  nlinarith

/-- The first mirror's length151 and fresh action bound give derivative sum<1600. -/
theorem mirror_second_core_slope_sum_lt (Y : Fin 151 → ℝ)
    (hY : ∀ i, |Y i| ≤ (211/500 : ℝ))
    (hE : (∑ i, cosinePotential (Y i)) ≤ (24366009/1000000 : ℝ)) :
    (∑ i, |cosinePotentialSlope (Y i)|) < 1600 := by
  have hsq := core_slope_sum_sq_le Finset.univ Y (211/500) (by norm_num) (by norm_num)
    (fun i _ => hY i)
  have hC := mirror_old_core_curvature_le (211/500) (by norm_num) le_rfl
  have hEnonneg : 0 ≤ ∑ i, cosinePotential (Y i) := by
    apply Finset.sum_nonneg
    intro i hi
    unfold cosinePotential
    exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hsq
  have hm := mul_le_mul_of_nonneg_right hC hEnonneg
  nlinarith

/-- The mirror bridge cost is summed over exactly `g=L-ell` sites. In particular,
 its neutral contribution retains the sharp factor `g/4`, not the full mirror delay. -/
theorem mirror_bridge_cost_sum_le (X Z : ℕ → ℝ) (h r Δ : ℝ) (a ζ : ℂ) (g : ℕ)
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hX : ∀ k < g, |X k| ≤ h*r^(k+1))
    (hZ : ∀ k < g, |Z k| ≤ h*r^(g-k))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1-ζ^2 ≠ 0) :
    (∑ k ∈ Finset.range g,
      (|X k * Z k| + (|X k|+|Z k|)* |(a*ζ^k).re| + (a*ζ^k).re^2/2)) ≤
      h^2*(g : ℝ)*r^(g+1) + 2*Δ*h*r/(1-r) +
        Δ^2*((g : ℝ)/4 + 1/(2*‖1-ζ^2‖)) := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hgeom : (∑ k ∈ Finset.range g, h*r^(k+1)) ≤ h*r/(1-r) := by
    have hs := stable_tail_abs_sum_le (fun k : ℕ => h*r^(k+1)) h r hh hr0 hr1
      (fun k => le_of_eq (abs_of_nonneg (by positivity))) g
    simpa only [abs_mul, abs_of_nonneg hh, abs_pow, abs_of_nonneg hr0] using hs
  have hSX : (∑ k ∈ Finset.range g, |X k|) ≤ h*r/(1-r) :=
    (Finset.sum_le_sum (fun k hk => hX k (Finset.mem_range.mp hk))).trans hgeom
  have hSZ : (∑ k ∈ Finset.range g, |Z k|) ≤ h*r/(1-r) := by
    calc
      _ ≤ ∑ k ∈ Finset.range g, h*r^(g-k) :=
        Finset.sum_le_sum (fun k hk => hZ k (Finset.mem_range.mp hk))
      _ = ∑ k ∈ Finset.range g, h*r^(k+1) := by
        rw [← Finset.sum_range_reflect (fun k => h*r^(k+1)) g]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < g := Finset.mem_range.mp hk
        congr 2
        omega
      _ ≤ _ := hgeom
  have hprod (k : ℕ) (hk : k < g) : |X k * Z k| ≤ h^2*r^(g+1) := by
    rw [abs_mul]
    calc
      _ ≤ (h*r^(k+1))*(h*r^(g-k)) := mul_le_mul (hX k hk) (hZ k hk)
        (abs_nonneg _) (by positivity)
      _ = h^2*(r^(k+1)*r^(g-k)) := by ring
      _ = _ := by rw [← pow_add, show k+1+(g-k) = g+1 by omega]
  have hSprod : (∑ k ∈ Finset.range g, |X k * Z k|) ≤ h^2*(g : ℝ)*r^(g+1) := by
    apply (Finset.sum_le_sum (fun k hk => hprod k (Finset.mem_range.mp hk))).trans_eq
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hw (k : ℕ) : |(a*ζ^k).re| ≤ Δ := by
    calc
      _ ≤ ‖a*ζ^k‖ := Complex.abs_re_le_norm _
      _ ≤ Δ := by simpa [norm_mul, norm_pow, hζ] using ha
  have hSmix : (∑ k ∈ Finset.range g, (|X k|+|Z k|)* |(a*ζ^k).re|) ≤
      2*Δ*h*r/(1-r) := by
    calc
      _ ≤ ∑ k ∈ Finset.range g, Δ*(|X k|+|Z k|) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (mul_le_mul_of_nonneg_left (hw k) (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq
          (mul_comm _ _)
      _ = Δ*((∑ k ∈ Finset.range g, |X k|)+(∑ k ∈ Finset.range g, |Z k|)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ Δ*(h*r/(1-r)+h*r/(1-r)) := by gcongr
      _ = _ := by ring
  have hSq : (∑ k ∈ Finset.range g, (a*ζ^k).re^2) ≤
      Δ^2*((g : ℝ)/2+1/‖1-ζ^2‖) := by
    apply (neutral_sq_sum_le a ζ hζ hne g).trans
    gcongr
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
  calc
    _ ≤ h^2*(g : ℝ)*r^(g+1) + 2*Δ*h*r/(1-r) +
        (Δ^2*((g : ℝ)/2+1/‖1-ζ^2‖))/2 := by gcongr
    _ = _ := by ring

/-- The actual mirror bridge action has the source bound over precisely `g` sites,
 derived from its two stable tails and full neutral mode. -/
theorem mirror_bridge_action_sum_le (X Z : ℕ → ℝ) (h r Δ R : ℝ) (a ζ : ℂ) (g : ℕ)
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hX : ∀ k < g, |X k| ≤ h*r^(k+1))
    (hZ : ∀ k < g, |Z k| ≤ h*r^(g-k))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1-ζ^2 ≠ 0)
    (hU : Δ+2*h*r ≤ R) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ)) :
    (∑ k ∈ Finset.range g, cosinePotential (X k + Z k + (a*ζ^k).re)) ≤
      (∑ k ∈ Finset.range g, cosinePotential (X k)) +
      (∑ k ∈ Finset.range g, cosinePotential (Z k)) +
      cosineCurvatureBound R * (h^2*(g : ℝ)*r^(g+1) + 2*Δ*h*r/(1-r) +
        Δ^2*((g : ℝ)/4 + 1/(2*‖1-ζ^2‖))) := by
  have hC : 0 ≤ cosineCurvatureBound R := by unfold cosineCurvatureBound; positivity
  have hXsmall (k : ℕ) (hk : k < g) : |X k| ≤ h*r := by
    apply (hX k hk).trans
    calc
      _ = (h*r)*r^k := by ring
      _ ≤ h*r := by
        simpa using mul_le_mul_of_nonneg_left (show r^k ≤ 1 from pow_le_one₀ hr0 hr1.le)
          (mul_nonneg hh hr0)
  have hZsmall (k : ℕ) (hk : k < g) : |Z k| ≤ h*r := by
    apply (hZ k hk).trans
    calc
      _ = h*r^((g-k-1)+1) := by congr 2; omega
      _ = (h*r)*r^(g-k-1) := by ring
      _ ≤ h*r := by
        simpa using mul_le_mul_of_nonneg_left (show r^(g-k-1) ≤ 1 from pow_le_one₀ hr0 hr1.le)
          (mul_nonneg hh hr0)
  have hw (k : ℕ) : |(a*ζ^k).re| ≤ Δ := by
    calc
      _ ≤ ‖a*ζ^k‖ := Complex.abs_re_le_norm _
      _ ≤ Δ := by simpa [norm_mul, norm_pow, hζ] using ha
  have hpoint (k : ℕ) (hk : k < g) :
      cosinePotential (X k+Z k+(a*ζ^k).re) ≤ cosinePotential (X k) + cosinePotential (Z k) +
        cosineCurvatureBound R * (|X k*Z k| + (|X k|+|Z k|)* |(a*ζ^k).re| + (a*ζ^k).re^2/2) := by
    have hs : |X k|+|Z k|+|(a*ζ^k).re| ≤ R := by
      linarith [hXsmall k hk, hZsmall k hk, hw k]
    have h := cosinePotential_gap_le_radius R (X k) (Z k) (a*ζ^k).re hR0 hR hs
    linarith
  have hcost := mirror_bridge_cost_sum_le X Z h r Δ a ζ g hh hr0 hr1 hX hZ ha hζ hne
  calc
    _ ≤ ∑ k ∈ Finset.range g, (cosinePotential (X k) + cosinePotential (Z k) +
        cosineCurvatureBound R * (|X k*Z k| + (|X k|+|Z k|)* |(a*ζ^k).re| + (a*ζ^k).re^2/2)) :=
      Finset.sum_le_sum (fun k hk => hpoint k (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range g, cosinePotential (X k)) +
        (∑ k ∈ Finset.range g, cosinePotential (Z k)) +
        cosineCurvatureBound R * (∑ k ∈ Finset.range g,
          (|X k*Z k| + (|X k|+|Z k|)* |(a*ζ^k).re| + (a*ζ^k).re^2/2)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- A genuine bounded perturbation has the derived Taylor action cost on a
 centered radius, retaining the actual base-point slope. -/
theorem cosinePotential_perturb_le_radius (R x z ε : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hx : |x| ≤ R) (hxz : |x+z| ≤ R) (hε : 0 ≤ ε) (hz : |z| ≤ ε) :
    cosinePotential (x+z) ≤ cosinePotential x + |cosinePotentialSlope x| * ε +
      cosineCurvatureBound R / 2 * ε^2 := by
  have hC : 0 ≤ cosineCurvatureBound R := by unfold cosineCurvatureBound; positivity
  have ht := cosinePotential_taylor_le_radius R x z hR0 hR hx hxz
  have hs : cosinePotentialSlope x*z ≤ |cosinePotentialSlope x| * ε := by
    calc
      _ ≤ |cosinePotentialSlope x*z| := le_abs_self _
      _ = |cosinePotentialSlope x| * |z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hsq : z^2 ≤ ε^2 := by nlinarith [sq_abs z, abs_nonneg z]
  have hquad := mul_le_mul_of_nonneg_left hsq (div_nonneg hC (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith

/-- The two actual mirror cores have the source Taylor action cost. The two
 perturbation radii are `ρ` and `ρ+Δplus`; no desired final action is a premise. -/
theorem mirror_two_core_action_sum_le {ι : Type*} (s : Finset ι) (Y u v : ι → ℝ)
    (R ρ Δplus : ℝ) (hR0 : 0 ≤ R) (hR : R < (1/2 : ℝ))
    (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δplus)
    (hY : ∀ i ∈ s, |Y i| ≤ R)
    (hYu : ∀ i ∈ s, |Y i+u i| ≤ R) (hYv : ∀ i ∈ s, |Y i+v i| ≤ R)
    (hu : ∀ i ∈ s, |u i| ≤ ρ) (hv : ∀ i ∈ s, |v i| ≤ ρ+Δplus) :
    (∑ i ∈ s, cosinePotential (Y i+u i)) + (∑ i ∈ s, cosinePotential (Y i+v i)) ≤
      2*(∑ i ∈ s, cosinePotential (Y i)) +
      (∑ i ∈ s, |cosinePotentialSlope (Y i)|)*(Δplus+2*ρ) +
      cosineCurvatureBound R*(s.card : ℝ)*(Δplus+ρ)^2 := by
  have hC : 0 ≤ cosineCurvatureBound R := by unfold cosineCurvatureBound; positivity
  have hquad : cosineCurvatureBound R/2*(ρ^2+(ρ+Δplus)^2) ≤
      cosineCurvatureBound R*(ρ+Δplus)^2 := by
    have hsq : ρ^2+(ρ+Δplus)^2 ≤ 2*(ρ+Δplus)^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq (div_nonneg hC (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have hpoint (i : ι) (hi : i ∈ s) :
      cosinePotential (Y i+u i) + cosinePotential (Y i+v i) ≤
        2*cosinePotential (Y i) + |cosinePotentialSlope (Y i)| * (Δplus+2*ρ) +
        cosineCurvatureBound R*(Δplus+ρ)^2 := by
    have h1 := cosinePotential_perturb_le_radius R (Y i) (u i) ρ hR0 hR
      (hY i hi) (hYu i hi) hρ (hu i hi)
    have h2 := cosinePotential_perturb_le_radius R (Y i) (v i) (ρ+Δplus) hR0 hR
      (hY i hi) (hYv i hi) (add_nonneg hρ hΔ) (hv i hi)
    nlinarith
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ s, (2*cosinePotential (Y i) + |cosinePotentialSlope (Y i)| * (Δplus+2*ρ) +
        cosineCurvatureBound R*(Δplus+ρ)^2) := Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        Finset.sum_const, nsmul_eq_mul]
      ring

/-- Exact indexing of a core `[0,ell-1]` and its two exterior half-lines. -/
noncomputable def localizedProfileIndex (ell : ℕ) : (Fin ell ⊕ (ℕ ⊕ ℕ)) ≃ ℤ where
  toFun := fun q => match q with
    | .inl j => (j : ℕ)
    | .inr (.inl n) => -1-(n : ℤ)
    | .inr (.inr n) => (ell : ℤ)+(n : ℤ)
  invFun := fun t => if h1 : t < 0 then .inr (.inl (-1-t).toNat)
    else if h2 : t < ell then .inl ⟨t.toNat, by omega⟩
    else .inr (.inr (t-(ell : ℤ)).toNat)
  left_inv := by
    rintro (j | (n | n))
    · simp only
      split_ifs with h1 h2
      · omega
      · congr 1
      · omega
    · simp only
      split_ifs with h1 h2
      · congr 2
        omega
      · omega
      · omega
    · simp only
      split_ifs with h1 h2
      · omega
      · omega
      · congr 2
        omega
  right_inv := by
    intro t
    simp only
    split_ifs with h1 h2
    all_goals simp only; omega

/-- An actual bilateral profile from its finite core and actual exterior tails. -/
noncomputable def localizedProfile (ell : ℕ) (Y : Fin ell → ℝ) (left right : ℕ → ℝ) (j : ℤ) : ℝ :=
  Sum.elim Y (Sum.elim left right) ((localizedProfileIndex ell).symm j)

/-- Core and exterior tail sums assemble to the true bilateral action. -/
theorem localizedProfile_action_hasSum (ell : ℕ) (Y : Fin ell → ℝ) (left right : ℕ → ℝ)
    (Tleft Tright : ℝ) (hleft : HasSum (fun k => cosinePotential (left k)) Tleft)
    (hright : HasSum (fun k => cosinePotential (right k)) Tright) :
    HasSum (fun j : ℤ => cosinePotential (localizedProfile ell Y left right j))
      ((∑ i : Fin ell, cosinePotential (Y i)) + Tleft + Tright) := by
  have htail : HasSum (fun q : ℕ ⊕ ℕ => cosinePotential (Sum.elim left right q)) (Tleft+Tright) :=
    HasSum.sum (f := fun q : ℕ ⊕ ℕ => cosinePotential (Sum.elim left right q)) hleft hright
  have hcore := hasSum_fintype (fun i : Fin ell => cosinePotential (Y i))
  have hfull : HasSum (fun q : Fin ell ⊕ (ℕ ⊕ ℕ) =>
      cosinePotential (Sum.elim Y (Sum.elim left right) q))
      ((∑ i : Fin ell, cosinePotential (Y i)) + (Tleft+Tright)) :=
    HasSum.sum (f := fun q : Fin ell ⊕ (ℕ ⊕ ℕ) =>
      cosinePotential (Sum.elim Y (Sum.elim left right) q)) hcore htail
  apply ((localizedProfileIndex ell).hasSum_iff (f := fun j : ℤ =>
    cosinePotential (localizedProfile ell Y left right j))).mp
  simpa only [Function.comp_def, localizedProfile, Equiv.symm_apply_apply, add_assoc] using hfull

/-- Concatenate the two perturbed mirror cores with exactly `g` bridge coordinates. -/
noncomputable def mirrorCore (ell g : ℕ) (first second : Fin ell → ℝ) (gap : Fin g → ℝ) :
    Fin (ell+(g+ell)) → ℝ := Fin.addCases first (Fin.addCases gap second)

/-- The actual concatenated core action splits into its two old-core copies and
 precisely the bridge of length `g`; it introduces no full-delay overcount. -/
theorem mirrorCore_action_sum (ell g : ℕ) (first second : Fin ell → ℝ) (gap : Fin g → ℝ) :
    (∑ i, cosinePotential (mirrorCore ell g first second gap i)) =
      (∑ i, cosinePotential (first i)) + (∑ i, cosinePotential (gap i)) +
        (∑ i, cosinePotential (second i)) := by
  simp [mirrorCore, Fin.sum_univ_add, add_assoc]

/-- On the actual canonical interval, the potential increases with the absolute
 coordinate. This controls the shrunken exterior tails after mirroring. -/
theorem cosinePotential_mono_abs (u v : ℝ) (hv : |v| < (1/2 : ℝ)) (huv : |u| ≤ |v|) :
    cosinePotential u ≤ cosinePotential v := by
  have hc := cosine_radius_lower |v| u (abs_nonneg _) hv huv
  have heq : Real.cos (Real.pi*|v|) = Real.cos (Real.pi*v) := by
    have h : Real.pi*|v| = |Real.pi*v| := by rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [h, Real.cos_abs]
  rw [heq] at hc
  have hsq : Real.cos (Real.pi*v)^2 ≤ Real.cos (Real.pi*u)^2 := by nlinarith [hc.1, hc.2]
  have hlog := Real.log_le_log (sq_pos_of_pos hc.1) hsq
  exact neg_le_neg hlog

/-- Equal absolute values give equal actual cosine potentials. -/
theorem cosinePotential_eq_of_abs_eq (u v : ℝ) (h : |u| = |v|) :
    cosinePotential u = cosinePotential v := by
  rcases abs_eq_abs.mp h with he | he
  · rw [he]
  · rw [he]
    simp [cosinePotential]

/-- A pointwise smaller actual exterior tail has a summable action no larger than
 the old tail; its sum is derived, not entered as a separate action certificate. -/
theorem tail_action_mono_abs (old new : ℕ → ℝ)
    (hold : Summable (fun k => cosinePotential (old k)))
    (hcenter : ∀ k, |old k| < (1/2 : ℝ)) (habs : ∀ k, |new k| ≤ |old k|) :
    Summable (fun k => cosinePotential (new k)) ∧
      (∑' k, cosinePotential (new k)) ≤ ∑' k, cosinePotential (old k) := by
  have hpoint (k : ℕ) : cosinePotential (new k) ≤ cosinePotential (old k) :=
    cosinePotential_mono_abs _ _ (hcenter k) (habs k)
  have h0 (k : ℕ) : 0 ≤ cosinePotential (new k) := by
    unfold cosinePotential
    exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  have hnew := Summable.of_nonneg_of_le h0 hpoint hold
  exact ⟨hnew, Summable.tsum_le_tsum hpoint hnew hold⟩

/-- A genuine localized mirror candidate made from two perturbed cores, its exact
 `g`-site bridge, and actual new exterior tails. No parity or reciprocity is built in. -/
noncomputable def mirrorLocalizedProfile (ell g : ℕ) (Y u v : Fin ell → ℝ)
    (X Z : ℕ → ℝ) (a ζ : ℂ) (left right : ℕ → ℝ) : ℤ → ℝ :=
  localizedProfile (ell+(g+ell))
    (mirrorCore ell g (fun i => Y i+u i) (fun i => Y i+v i)
      (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re)) left right

/-- The actual localized candidate has the source mirror action bound, including
 the baseline `2E` from two copies of the old core and four old-tail contributions.
 Every error term is derived from the actual core perturbations and bridge. -/
theorem mirrorLocalizedProfile_action_le (ell g : ℕ) (Y u v : Fin ell → ℝ)
    (old left right X Z : ℕ → ℝ) (a ζ : ℂ) (h r Δ ρ Δplus Rcore Rgap : ℝ)
    (hold : Summable (fun k => cosinePotential (old k)))
    (hcenter : ∀ k, |old k| < (1/2 : ℝ))
    (hleft : ∀ k, |left k| ≤ |old k|) (hright : ∀ k, |right k| ≤ |old k|)
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hold_bound : ∀ k, |old k| ≤ h*r^(k+1))
    (hX : ∀ k < g, |X k| = |old k|) (hZ : ∀ k < g, |Z k| = |old (g-1-k)|)
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1-ζ^2 ≠ 0)
    (hρ : 0 ≤ ρ) (hΔplus : 0 ≤ Δplus)
    (hRc0 : 0 ≤ Rcore) (hRc : Rcore < (1/2 : ℝ))
    (hY : ∀ i, |Y i| ≤ Rcore)
    (hYu : ∀ i, |Y i+u i| ≤ Rcore) (hYv : ∀ i, |Y i+v i| ≤ Rcore)
    (hu : ∀ i, |u i| ≤ ρ) (hv : ∀ i, |v i| ≤ ρ+Δplus)
    (hRg0 : 0 ≤ Rgap) (hRg : Rgap < (1/2 : ℝ)) (hU : Δ+2*h*r ≤ Rgap) :
    Summable (fun j : ℤ => cosinePotential (mirrorLocalizedProfile ell g Y u v X Z a ζ left right j)) ∧
    (∑' j : ℤ, cosinePotential (mirrorLocalizedProfile ell g Y u v X Z a ζ left right j)) ≤
      2*((∑ i, cosinePotential (Y i)) + 2*(∑' k, cosinePotential (old k))) +
      (∑ i, |cosinePotentialSlope (Y i)|)*(Δplus+2*ρ) +
      cosineCurvatureBound Rcore*(ell : ℝ)*(Δplus+ρ)^2 +
      cosineCurvatureBound Rgap*(h^2*(g : ℝ)*r^(g+1) + 2*Δ*h*r/(1-r) +
        Δ^2*((g : ℝ)/4 + 1/(2*‖1-ζ^2‖))) := by
  have hL := tail_action_mono_abs old left hold hcenter hleft
  have hRt := tail_action_mono_abs old right hold hcenter hright
  have hsum := localizedProfile_action_hasSum (ell+(g+ell))
    (mirrorCore ell g (fun i => Y i+u i) (fun i => Y i+v i)
      (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re)) left right
    (∑' k, cosinePotential (left k)) (∑' k, cosinePotential (right k)) hL.1.hasSum hRt.1.hasSum
  refine ⟨hsum.summable, ?_⟩
  change (∑' j : ℤ, cosinePotential (localizedProfile _ _ _ _ j)) ≤ _
  rw [hsum.tsum_eq, mirrorCore_action_sum]
  have htwo := mirror_two_core_action_sum_le Finset.univ Y u v Rcore ρ Δplus hRc0 hRc hρ hΔplus
    (fun i _ => hY i) (fun i _ => hYu i) (fun i _ => hYv i) (fun i _ => hu i) (fun i _ => hv i)
  norm_num only [Finset.card_univ, Fintype.card_fin] at htwo
  have hXB (k : ℕ) (hk : k < g) : |X k| ≤ h*r^(k+1) := by rw [hX k hk]; exact hold_bound k
  have hZB (k : ℕ) (hk : k < g) : |Z k| ≤ h*r^(g-k) := by
    rw [hZ k hk]
    convert hold_bound (g-1-k) using 1
    congr 2
    omega
  have hbridge := mirror_bridge_action_sum_le X Z h r Δ Rgap a ζ g hh hr0 hr1 hXB hZB
    ha hζ hne hU hRg0 hRg
  have hbase : (∑ k ∈ Finset.range g, cosinePotential (old k)) ≤ ∑' k, cosinePotential (old k) := by
    apply Summable.sum_le_tsum (Finset.range g) (fun k _ => ?_) hold
    unfold cosinePotential
    exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  have hVX : (∑ k ∈ Finset.range g, cosinePotential (X k)) ≤ ∑' k, cosinePotential (old k) := by
    apply le_trans (Finset.sum_le_sum (fun k hk =>
      (cosinePotential_eq_of_abs_eq (X k) (old k) (hX k (Finset.mem_range.mp hk))).le)) hbase
  have hVZ : (∑ k ∈ Finset.range g, cosinePotential (Z k)) ≤ ∑' k, cosinePotential (old k) := by
    calc
      _ = ∑ k ∈ Finset.range g, cosinePotential (old (g-1-k)) :=
        Finset.sum_congr rfl (fun k hk => cosinePotential_eq_of_abs_eq _ _ (hZ k (Finset.mem_range.mp hk)))
      _ = ∑ k ∈ Finset.range g, cosinePotential (old k) := Finset.sum_range_reflect (fun k => cosinePotential (old k)) g
      _ ≤ _ := hbase
  have hgap : (∑ i : Fin g, cosinePotential (X i+Z i+(a*ζ^(i : ℕ)).re)) =
      ∑ k ∈ Finset.range g, cosinePotential (X k+Z k+(a*ζ^k).re) :=
    Fin.sum_univ_eq_sum_range (fun k => cosinePotential (X k+Z k+(a*ζ^k).re)) g
  rw [hgap]
  linarith only [htwo, hbridge, hVX, hVZ, hL.2, hRt.2]

/-- The actual neutral mode is bounded uniformly by its actual complex amplitude. -/
theorem abs_neutralMode_le (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (j : ℤ) :
    |neutralMode z ζ j| ≤ ‖z‖ := by
  unfold neutralMode
  calc
    _ ≤ ‖z*ζ^j‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ := by simp [norm_zpow, hζ]

/-- An actual shifted incoming exponential is uniformly small over the entire core,
 with the gap exponent `L-ell+1`. -/
theorem mirror_core_shift_bound (b c h : ℝ) (hb : 1 < b) (hc : |c| ≤ h)
    (ell L : ℕ) (hL : ell ≤ L) (i : Fin ell) :
    |c*b^((i : ℕ)-(L : ℤ))| ≤ h*b⁻¹^(L-ell+1) := by
  have hb0 : 0 < b := by linarith
  have hr0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
  have hr1 : b⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hb).le
  have hh : 0 ≤ h := (abs_nonneg c).trans hc
  have heq : ((i : ℕ) : ℤ)-(L : ℤ) = -((L-(i : ℕ) : ℕ) : ℤ) := by omega
  rw [heq, zpow_neg, zpow_natCast, abs_mul, abs_inv, abs_pow, abs_of_pos hb0, ← inv_pow]
  apply (mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 _)).trans
  apply mul_le_mul_of_nonneg_left _ hh
  exact pow_le_pow_of_le_one hr0 hr1 (by omega)

/-- The two actual core perturbations inherit exactly the source radii `ρ` and
 `ρ+Δplus` from the incoming tail and the derived neutral difference coefficient. -/
theorem mirror_core_perturbation_bounds (b c h : ℝ) (hb : 1 < b) (hc : |c| ≤ h)
    (ell L : ℕ) (hL : ell ≤ L) (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (Δplus : ℝ)
    (hΔplus : ‖mirrorNeutralCoefficient z ζ L‖ ≤ Δplus) (i : Fin ell) :
    |-(c*b^((i : ℕ)-(L : ℤ)))| ≤ h*b⁻¹^(L-ell+1) ∧
    |-(c*b^((i : ℕ)-(L : ℤ))) - neutralMode (mirrorNeutralCoefficient z ζ L) ζ i| ≤
      h*b⁻¹^(L-ell+1)+Δplus := by
  have hs := mirror_core_shift_bound b c h hb hc ell L hL i
  refine ⟨by simpa only [abs_neg] using hs, ?_⟩
  calc
    _ ≤ |-(c*b^((i : ℕ)-(L : ℤ)))| + |neutralMode (mirrorNeutralCoefficient z ζ L) ζ i| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (-(c*b^((i : ℕ)-(L : ℤ)))) (-neutralMode (mirrorNeutralCoefficient z ζ L) ζ i)
    _ ≤ h*b⁻¹^(L-ell+1)+Δplus := by
      rw [abs_neg]
      exact add_le_add hs ((abs_neutralMode_le _ ζ hζ i).trans hΔplus)

/-- The sign-adjusted reflected second core has exactly the action of its
 unreflected perturbation, with its spatial order kept explicit. -/
theorem reflected_core_action_sum (ell : ℕ) (Y v : Fin ell → ℝ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    (∑ i : Fin ell, cosinePotential (-σ*(Y i.rev+v i.rev))) =
      ∑ i : Fin ell, cosinePotential (Y i+v i) := by
  have hp (x : ℝ) : cosinePotential (-σ*x) = cosinePotential x := by
    rcases hσ with rfl | rfl <;> simp [cosinePotential]
  simp_rw [hp]
  exact Equiv.sum_comp (Fin.revPerm (n := ell)) (fun i => cosinePotential (Y i+v i))

/-- The spatially reflected and sign-adjusted mirror candidate. Its second core
 is indexed in the actual reflected order, without assuming exact old-core symmetry. -/
noncomputable def mirrorReflectedLocalizedProfile (ell g : ℕ) (Y u v : Fin ell → ℝ)
    (X Z : ℕ → ℝ) (a ζ : ℂ) (σ : ℝ) (left right : ℕ → ℝ) : ℤ → ℝ :=
  localizedProfile (ell+(g+ell))
    (mirrorCore ell g (fun i => Y i+u i) (fun i => -σ*(Y i.rev+v i.rev))
      (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re)) left right

/-- The actual reflected candidate has the same full action as the analytic
 concatenation, by evenness and an exact finite-index reversal. -/
theorem mirrorReflectedLocalizedProfile_action_eq (ell g : ℕ) (Y u v : Fin ell → ℝ)
    (X Z : ℕ → ℝ) (a ζ : ℂ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (left right : ℕ → ℝ)
    (hleft : Summable (fun k => cosinePotential (left k)))
    (hright : Summable (fun k => cosinePotential (right k))) :
    Summable (fun j : ℤ => cosinePotential
      (mirrorReflectedLocalizedProfile ell g Y u v X Z a ζ σ left right j)) ∧
    (∑' j : ℤ, cosinePotential (mirrorReflectedLocalizedProfile ell g Y u v X Z a ζ σ left right j)) =
      ∑' j : ℤ, cosinePotential (mirrorLocalizedProfile ell g Y u v X Z a ζ left right j) := by
  have hE : (∑ i, cosinePotential (mirrorCore ell g (fun i => Y i+u i)
      (fun i => -σ*(Y i.rev+v i.rev)) (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re) i)) =
      ∑ i, cosinePotential (mirrorCore ell g (fun i => Y i+u i)
        (fun i => Y i+v i) (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re) i) := by
    rw [mirrorCore_action_sum, mirrorCore_action_sum, reflected_core_action_sum ell Y v σ hσ]
  have href := localizedProfile_action_hasSum (ell+(g+ell))
    (mirrorCore ell g (fun i => Y i+u i) (fun i => -σ*(Y i.rev+v i.rev))
      (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re)) left right
    (∑' k, cosinePotential (left k)) (∑' k, cosinePotential (right k)) hleft.hasSum hright.hasSum
  have hplain := localizedProfile_action_hasSum (ell+(g+ell))
    (mirrorCore ell g (fun i => Y i+u i) (fun i => Y i+v i)
      (fun i : Fin g => X i+Z i+(a*ζ^(i : ℕ)).re)) left right
    (∑' k, cosinePotential (left k)) (∑' k, cosinePotential (right k)) hleft.hasSum hright.hasSum
  rw [hE] at href
  exact ⟨href.summable, href.tsum_eq.trans hplain.tsum_eq.symm⟩

/-- Uniform coordinate bounds pass to the actual bilateral localized profile. -/
theorem localizedProfile_abs_le (ell : ℕ) (Y : Fin ell → ℝ) (left right : ℕ → ℝ) (B : ℝ)
    (hY : ∀ i, |Y i| ≤ B) (hleft : ∀ k, |left k| ≤ B) (hright : ∀ k, |right k| ≤ B) :
    ∀ j : ℤ, |localizedProfile ell Y left right j| ≤ B := by
  intro j
  unfold localizedProfile
  generalize (localizedProfileIndex ell).symm j = q
  rcases q with i | (k | k)
  · exact hY i
  · exact hleft k
  · exact hright k

/-- Bounds on the three actual finite regions pass to the concatenated mirror core. -/
theorem mirrorCore_abs_le (ell g : ℕ) (first second : Fin ell → ℝ) (gap : Fin g → ℝ) (B : ℝ)
    (hfirst : ∀ i, |first i| ≤ B) (hsecond : ∀ i, |second i| ≤ B) (hgap : ∀ i, |gap i| ≤ B) :
    ∀ i, |mirrorCore ell g first second gap i| ≤ B := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simpa [mirrorCore] using hfirst k
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro t
      simpa [mirrorCore] using hgap t
    · intro t
      simpa [mirrorCore] using hsecond t

/-- The reflected candidate has exactly the source minimum boundary margin,
 derived from the two core perturbations, actual bridge coordinates, and exterior tails. -/
theorem mirrorReflectedLocalizedProfile_margin (ell g : ℕ) (Y u v : Fin ell → ℝ)
    (X Z : ℕ → ℝ) (a ζ : ℂ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (left right : ℕ → ℝ)
    (θ ρ Δplus U tail : ℝ) (hΔ : 0 ≤ Δplus)
    (hY : ∀ i, |Y i| ≤ (1/2 : ℝ)-θ)
    (hu : ∀ i, |u i| ≤ ρ) (hv : ∀ i, |v i| ≤ ρ+Δplus)
    (hgap : ∀ i : Fin g, |X i+Z i+(a*ζ^(i : ℕ)).re| ≤ U)
    (hleft : ∀ k, |left k| ≤ tail) (hright : ∀ k, |right k| ≤ tail) :
    ∀ j : ℤ, |mirrorReflectedLocalizedProfile ell g Y u v X Z a ζ σ left right j| ≤
      (1/2 : ℝ) - min (θ-Δplus-ρ) (min ((1/2 : ℝ)-U) ((1/2 : ℝ)-tail)) := by
  let θnew := min (θ-Δplus-ρ) (min ((1/2 : ℝ)-U) ((1/2 : ℝ)-tail))
  have hm0 : θnew ≤ θ-Δplus-ρ := min_le_left _ _
  have hm1 : θnew ≤ (1/2 : ℝ)-U := (min_le_right _ _).trans (min_le_left _ _)
  have hm2 : θnew ≤ (1/2 : ℝ)-tail := (min_le_right _ _).trans (min_le_right _ _)
  apply localizedProfile_abs_le
  · apply mirrorCore_abs_le
    · intro i
      have h := abs_add_le (Y i) (u i)
      linarith [hY i, hu i]
    · intro i
      have h := abs_add_le (Y i.rev) (v i.rev)
      rcases hσ with rfl | rfl <;> simp only [neg_mul, one_mul, neg_neg, abs_neg] <;>
        linarith [hY i.rev, hv i.rev]
    · intro i
      linarith [hgap i]
  · intro k
    linarith [hleft k]
  · intro k
    linarith [hright k]

end Salem
