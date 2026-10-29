module

public import Salem.P1Analytic
public import Salem.BernoulliFourier

@[expose] public section

open scoped BigOperators
open Set Filter Topology

namespace Salem

/-- The exact slope of the logarithmic cosine potential away from its zeros. -/
noncomputable def cosinePotentialSlope (u : ℝ) : ℝ :=
  2 * Real.pi * Real.tan (Real.pi * u)

/-- The actual first derivative of the potential, with cosine zeros excluded. -/
theorem hasDerivAt_cosinePotential (u : ℝ) (hu : Real.cos (Real.pi * u) ≠ 0) :
    HasDerivAt cosinePotential (cosinePotentialSlope u) u := by
  have hc := (Real.hasDerivAt_cos (Real.pi * u)).comp u (hasDerivAt_const_mul Real.pi)
  have hd := ((hc.pow 2).log (pow_ne_zero 2 hu)).neg
  convert hd using 1
  · rfl
  · dsimp [cosinePotentialSlope]
    rw [Real.tan_eq_sin_div_cos]
    field_simp

/-- The actual derivative of the slope is the nonnegative secant-square expression. -/
theorem hasDerivAt_cosinePotentialSlope (u : ℝ) (hu : Real.cos (Real.pi * u) ≠ 0) :
    HasDerivAt cosinePotentialSlope (2 * Real.pi ^ 2 / Real.cos (Real.pi * u) ^ 2) u := by
  have hd := ((Real.hasDerivAt_tan hu).comp u (hasDerivAt_const_mul Real.pi)).const_mul
    (2 * Real.pi)
  unfold cosinePotentialSlope
  convert hd using 1
  · funext x
    rfl
  · ring

/-- A rational denominator bound valid on the whole sharp-restoration interval. -/
theorem cosine_sq_small_lower (u : ℝ) (hu : |u| ≤ (1 / 100 : ℝ)) :
    (999 / 1000 : ℝ) ≤ Real.cos (Real.pi * u) ^ 2 := by
  have hpi : Real.pi ^ 2 ≤ (99 / 10 : ℝ) := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) := by
    nlinarith [sq_abs u, abs_nonneg u]
  have hmul := mul_le_mul hpi hu2 (sq_nonneg u) (by norm_num : (0 : ℝ) ≤ 99 / 10)
  have hs := Real.sin_sq_le_sq (x := Real.pi * u)
  nlinarith [Real.cos_sq_add_sin_sq (Real.pi * u)]

/-- The exact second-derivative expression is bounded by `20`, retaining the
 quadratic coefficient `10` needed by the finite Fourier certificate. -/
theorem cosinePotentialSlope_derivative_le_twenty (u : ℝ) (hu : |u| ≤ (1 / 100 : ℝ)) :
    2 * Real.pi ^ 2 / Real.cos (Real.pi * u) ^ 2 ≤ 20 := by
  have hden := cosine_sq_small_lower u hu
  have hpi : Real.pi ^ 2 ≤ (99 / 10 : ℝ) := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  apply (div_le_iff₀ (by linarith : 0 < Real.cos (Real.pi * u) ^ 2)).2
  nlinarith

/-- The potential is smooth on the strict small-angle restoration interval. -/
theorem contDiffOn_cosinePotential_small (n : ℕ∞) :
    ContDiffOn ℝ n cosinePotential (Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ)) := by
  have hf : ContDiffOn ℝ n (fun u : ℝ => Real.cos (Real.pi * u) ^ 2)
      (Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ)) := by fun_prop
  have hn (u : ℝ) (hu : u ∈ Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ)) :
      Real.cos (Real.pi * u) ^ 2 ≠ 0 := by
    have h := cosine_sq_small_lower u (abs_le.mpr hu)
    linarith
  exact (hf.log hn).neg

/-- The true second derivative, obtained from a local identity rather than
 differentiating the totalized logarithm at a zero. -/
theorem iteratedDeriv_two_cosinePotential (u : ℝ) (hu : Real.cos (Real.pi * u) ≠ 0) :
    iteratedDeriv 2 cosinePotential u = 2 * Real.pi ^ 2 / Real.cos (Real.pi * u) ^ 2 := by
  have he : deriv cosinePotential =ᶠ[𝓝 u] cosinePotentialSlope := by
    have hc : ContinuousAt (fun x : ℝ => Real.cos (Real.pi * x)) u := by fun_prop
    filter_upwards [hc.eventually (eventually_ne_nhds hu)] with x hx
    exact (hasDerivAt_cosinePotential x hx).deriv
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact he.deriv_eq.trans (hasDerivAt_cosinePotentialSlope u hu).deriv

/-- The actual first derivative is bounded linearly from its zero value at the origin. -/
theorem abs_cosinePotentialSlope_le_twenty_mul_abs (u : ℝ) (hu : |u| ≤ (1 / 100 : ℝ)) :
    |cosinePotentialSlope u| ≤ 20 * |u| := by
  have hne (x : ℝ) (hx : x ∈ Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ)) :
      Real.cos (Real.pi * x) ≠ 0 := by
    have h := cosine_sq_small_lower x (abs_le.mpr hx)
    intro hz
    rw [hz] at h
    norm_num at h
  have hbound (x : ℝ) (hx : x ∈ Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ)) :
      ‖2 * Real.pi ^ 2 / Real.cos (Real.pi * x) ^ 2‖ ≤ 20 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cosinePotentialSlope_derivative_le_twenty x (abs_le.mpr hx)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hasDerivAt_cosinePotentialSlope x (hne x hx)).hasDerivWithinAt)
    hbound (convex_Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ))
    (show (0 : ℝ) ∈ Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ) by norm_num)
    (abs_le.mp hu)
  simpa [cosinePotentialSlope, Real.norm_eq_abs] using h

/-- The actual sharp Taylor perturbation estimate used in the finite restoration
 certificate, proved with quadratic coefficient `10` rather than an assumed remainder. -/
theorem cosinePotential_add_le_sharp (x z : ℝ)
    (hxz : |x| + |z| ≤ (1 / 100 : ℝ)) :
    cosinePotential (x + z) ≤ cosinePotential x + 20 * |x| * |z| + 10 * z ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hx : |x| ≤ (1 / 100 : ℝ) := by linarith [abs_nonneg z]
  have hsum : |x + z| ≤ (1 / 100 : ℝ) := (abs_add_le x z).trans hxz
  have hseg : uIcc x (x + z) ⊆ Icc (-(1 / 100 : ℝ)) (1 / 100 : ℝ) :=
    uIcc_subset_Icc (abs_le.mp hx) (abs_le.mp hsum)
  have hne : x ≠ x + z := by intro he; apply hz; linarith
  have hcos (u : ℝ) (hu : |u| ≤ (1 / 100 : ℝ)) : Real.cos (Real.pi * u) ≠ 0 := by
    have hc := cosine_sq_small_lower u hu
    intro he
    rw [he] at hc
    norm_num at hc
  have hd0 : iteratedDerivWithin 1 cosinePotential (uIcc x (x+z)) x =
      cosinePotentialSlope x := by
    rw [iteratedDerivWithin_one]
    exact (hasDerivAt_cosinePotential x (hcos x hx)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_uIcc hne) x left_mem_uIcc)
  have hpoly : taylorWithinEval cosinePotential 1 (uIcc x (x+z)) x (x+z) =
      cosinePotential x + cosinePotentialSlope x * z := by
    rw [show (1 : ℕ) = 0+1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd0]
    norm_num
    ring
  obtain ⟨u, hu, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := cosinePotential)
    (x₀ := x) (x := x+z) (n := 1) hne ((contDiffOn_cosinePotential_small 2).mono hseg)
  have huabs : |u| ≤ (1 / 100 : ℝ) := abs_le.mpr (hseg (uIoo_subset_uIcc_self hu))
  rw [hpoly, iteratedDeriv_two_cosinePotential u (hcos u huabs)] at heq
  norm_num at heq
  have hsecond := cosinePotentialSlope_derivative_le_twenty u huabs
  have hterm := mul_le_mul_of_nonneg_right hsecond (sq_nonneg z)
  have hslope : cosinePotentialSlope x * z ≤ 20 * |x| * |z| := by
    calc
      _ ≤ |cosinePotentialSlope x * z| := le_abs_self _
      _ = |cosinePotentialSlope x| * |z| := abs_mul _ _
      _ ≤ (20 * |x|) * |z| := mul_le_mul_of_nonneg_right
        (abs_cosinePotentialSlope_le_twenty_mul_abs x hx) (abs_nonneg z)
  nlinarith

/-- A unit complex geometric sum has a uniform nonresonant norm bound. -/
theorem norm_geometric_sum_sq_le (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hne : 1 - ζ ^ 2 ≠ 0) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, (ζ ^ 2) ^ k‖ ≤ 2 / ‖1 - ζ ^ 2‖ := by
  have heq := congrArg norm (geom_sum_mul_neg (ζ ^ 2) m)
  rw [norm_mul] at heq
  apply (le_div_iff₀ (norm_pos_iff.mpr hne)).2
  rw [heq]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(ζ ^ 2) ^ m‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hζ]

/-- The real square decomposes into its constant and double-frequency parts. -/
theorem twice_re_sq (z : ℂ) : 2 * z.re ^ 2 = ‖z‖ ^ 2 + (z ^ 2).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

/-- Exact decomposition of the oscillatory square sum, independent of phase. -/
theorem neutral_sq_sum_identity (a ζ : ℂ) (hζ : ‖ζ‖ = 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, (a * ζ ^ k).re ^ 2) =
      (m : ℝ) * ‖a‖ ^ 2 / 2 +
        ((a ^ 2) * (∑ k ∈ Finset.range m, (ζ ^ 2) ^ k)).re / 2 := by
  have hpoint (k : ℕ) : (a * ζ ^ k).re ^ 2 =
      ‖a‖ ^ 2 / 2 + ((a ^ 2) * (ζ ^ 2) ^ k).re / 2 := by
    have h := twice_re_sq (a * ζ ^ k)
    rw [norm_mul, norm_pow, hζ, one_pow, mul_one] at h
    have heq : (a * ζ ^ k) ^ 2 = a ^ 2 * (ζ ^ 2) ^ k := by ring
    rw [heq] at h
    linarith
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_div, ← Complex.re_sum, ← Finset.mul_sum]
  ring

/-- The exact neutral oscillation saves the factor `1/2` in the long quadratic
 restoration cost; its bounded nonresonant error is independent of `m`. -/
theorem neutral_sq_sum_le (a ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hne : 1 - ζ ^ 2 ≠ 0) (m : ℕ) :
    (∑ k ∈ Finset.range m, (a * ζ ^ k).re ^ 2) ≤
      ‖a‖ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
  rw [neutral_sq_sum_identity a ζ hζ m]
  have hgeometric := norm_geometric_sum_sq_le ζ hζ hne m
  have hre : ((a ^ 2) * (∑ k ∈ Finset.range m, (ζ ^ 2) ^ k)).re ≤
      ‖a‖ ^ 2 * (2 / ‖1 - ζ ^ 2‖) := by
    calc
      _ ≤ ‖(a ^ 2) * (∑ k ∈ Finset.range m, (ζ ^ 2) ^ k)‖ := Complex.re_le_norm _
      _ = ‖a‖ ^ 2 * ‖∑ k ∈ Finset.range m, (ζ ^ 2) ^ k‖ := by rw [norm_mul, norm_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeometric (sq_nonneg _)
  calc
    _ ≤ (m : ℝ) * ‖a‖ ^ 2 / 2 + (‖a‖ ^ 2 * (2 / ‖1 - ζ ^ 2‖)) / 2 := by linarith
    _ = _ := by ring

/-- The absolute stable tail has the exact geometric upper bound used in restoration. -/
theorem stable_tail_abs_sum_le (H : ℕ → ℝ) (h r : ℝ) (hh : 0 ≤ h)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hH : ∀ k, |H k| ≤ h * r ^ (k+1)) (m : ℕ) :
    (∑ k ∈ Finset.range m, |H k|) ≤ h * r / (1-r) := by
  have hs : Summable (fun k : ℕ => (h*r) * r ^ k) :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])).mul_left (h*r)
  calc
    _ ≤ ∑ k ∈ Finset.range m, (h*r) * r ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      convert hH k using 1
      ring
    _ ≤ ∑' k : ℕ, (h*r) * r ^ k :=
      Summable.sum_le_tsum (Finset.range m) (fun k _ => by positivity) hs
    _ = h*r/(1-r) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])]
      rfl

/-- The actual finite restored stable tail obeys the sharp oscillatory action bound. -/
theorem sharp_restoration_tail_sum_le (H : ℕ → ℝ) (h r Δ : ℝ) (a ζ : ℂ)
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hH : ∀ k, |H k| ≤ h * r ^ (k+1))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0)
    (hsmall : h*r + Δ ≤ (1 / 100 : ℝ)) (m : ℕ) :
    (∑ k ∈ Finset.range m, cosinePotential (H k + (a * ζ ^ k).re)) ≤
      (∑ k ∈ Finset.range m, cosinePotential (H k)) +
        20 * Δ * h * r / (1-r) +
        10 * Δ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hchi (k : ℕ) : |(a * ζ ^ k).re| ≤ Δ := by
    calc
      _ ≤ ‖a * ζ ^ k‖ := Complex.abs_re_le_norm _
      _ ≤ Δ := by simpa [norm_mul, norm_pow, hζ] using ha
  have hHsmall (k : ℕ) : |H k| ≤ h*r := by
    calc
      _ ≤ h * r ^ (k+1) := hH k
      _ = (h*r) * r ^ k := by ring
      _ ≤ h*r := by
        simpa using mul_le_mul_of_nonneg_left
          (show r ^ k ≤ 1 from pow_le_one₀ hr0 hr1.le) (mul_nonneg hh hr0)
  have hpoint (k : ℕ) :
      cosinePotential (H k + (a * ζ ^ k).re) ≤ cosinePotential (H k) +
        20 * |H k| * Δ + 10 * (a * ζ ^ k).re ^ 2 := by
    have hs : |H k| + |(a * ζ ^ k).re| ≤ (1 / 100 : ℝ) :=
      (add_le_add (hHsmall k) (hchi k)).trans hsmall
    exact (cosinePotential_add_le_sharp _ _ hs).trans (by gcongr; exact hchi k)
  have hsquare : (∑ k ∈ Finset.range m, (a * ζ ^ k).re ^ 2) ≤
      Δ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
    apply (neutral_sq_sum_le a ζ hζ hne m).trans
    gcongr
  have habs := stable_tail_abs_sum_le H h r hh hr0 hr1 hH m
  calc
    _ ≤ ∑ k ∈ Finset.range m,
        (cosinePotential (H k) + 20 * |H k| * Δ + 10 * (a * ζ ^ k).re ^ 2) :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (∑ k ∈ Finset.range m, cosinePotential (H k)) +
        20 * Δ * (∑ k ∈ Finset.range m, |H k|) +
        10 * (∑ k ∈ Finset.range m, (a * ζ ^ k).re ^ 2) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (∑ k ∈ Finset.range m, cosinePotential (H k)) +
        20 * Δ * (h*r/(1-r)) +
        10 * (Δ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖)) := by gcongr
    _ = _ := by ring

/-- An infinite left prefix of a summable nonnegative bilateral series is bounded
 by the full sum, with an explicit finite set of nonnegative point corrections. -/
theorem bilateral_prefix_bound_of_finite_corrections {ι : Type*} [Fintype ι]
    (f g : ℤ → ℝ) (e : ι → ℤ) (p : ι → ℝ) (n : ℤ)
    (hf : Summable f) (hf0 : ∀ j, 0 ≤ f j) (hg0 : ∀ j, 0 ≤ g j)
    (hp0 : ∀ i, 0 ≤ p i)
    (hpoint : ∀ j ≤ n, g j ≤ f j + ∑ i : ι, if j = e i then p i else 0) :
    Summable (fun k : ℕ => g (n-k)) ∧
      (∑' k : ℕ, g (n-k)) ≤ (∑' j : ℤ, f j) + ∑ i : ι, p i := by
  classical
  let C : ℤ → ℝ := fun j => ∑ i : ι, if j = e i then p i else 0
  have hC : HasSum C (∑ i : ι, p i) :=
    hasSum_sum (fun i _ => hasSum_ite_eq (e i) (p i))
  have hC0 (j : ℤ) : 0 ≤ C j := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hp0 i
    · exact le_rfl
  have hsum : HasSum (fun j => f j + C j) ((∑' j : ℤ, f j) + ∑ i : ι, p i) :=
    hf.hasSum.add hC
  have hinj : Function.Injective (fun k : ℕ => n - (k : ℤ)) := by
    intro a b hab
    change n - (a : ℤ) = n - (b : ℤ) at hab
    omega
  have hgp (k : ℕ) : g (n-k) ≤ f (n-k) + C (n-k) :=
    hpoint _ (by omega)
  have hg : Summable (fun k : ℕ => g (n-k)) :=
    Summable.of_nonneg_of_le (fun k => hg0 _) hgp (hsum.summable.comp_injective hinj)
  refine ⟨hg, ?_⟩
  have hbound := Summable.tsum_le_tsum_of_inj (fun k : ℕ => n - (k : ℤ)) hinj
    (fun j _ => add_nonneg (hf0 j) (hC0 j)) hgp hg hsum.summable
  exact hbound.trans_eq hsum.tsum_eq

/-- The monic quartic residual; boundary defects are kept explicit. -/
noncomputable def quarticResidual (p0 p1 p2 p3 : ℤ) (y : ℤ → ℝ) (j : ℤ) : ℝ :=
  y (j+4) + (p3 : ℝ) * y (j+3) + (p2 : ℝ) * y (j+2) +
    (p1 : ℝ) * y (j+1) + (p0 : ℝ) * y j

/-- Residuals are additive, so restoring an outgoing wave exposes rather than
 discards the localized profile's boundary defect. -/
theorem quarticResidual_add (p0 p1 p2 p3 : ℤ) (H w : ℤ → ℝ) (j : ℤ) :
    quarticResidual p0 p1 p2 p3 (fun k => H k + w k) j =
      quarticResidual p0 p1 p2 p3 H j + quarticResidual p0 p1 p2 p3 w j := by
  unfold quarticResidual
  ring

/-- The exact expanding exponential has zero residual at a real quartic root. -/
theorem quarticResidual_expanding_zero (p0 p1 p2 p3 : ℤ) (b c : ℝ) (hb : b ≠ 0)
    (hroot : b ^ 4 + (p3 : ℝ) * b ^ 3 + (p2 : ℝ) * b ^ 2 + (p1 : ℝ) * b + p0 = 0)
    (j : ℤ) : quarticResidual p0 p1 p2 p3 (fun k => c * b ^ k) j = 0 := by
  unfold quarticResidual
  simp only [zpow_add₀ hb, zpow_ofNat]
  calc
    _ = c * b ^ j * (b ^ 4 + (p3 : ℝ) * b ^ 3 + (p2 : ℝ) * b ^ 2 + (p1 : ℝ) * b + p0) := by ring
    _ = 0 := by rw [hroot, mul_zero]

/-- Four integer anchors and actual monic integer forcing generate an integer
 sequence; this constructor makes no finite-energy or global-profile assumption. -/
theorem integer_quartic_sequence (z : ℕ → ℝ) (p0 p1 p2 p3 : ℤ)
    (hbase : ∀ n < 4, ∃ m : ℤ, z n = m)
    (hforce : ∀ n : ℕ, ∃ m : ℤ,
      z (n+4) + (p3 : ℝ) * z (n+3) + (p2 : ℝ) * z (n+2) +
        (p1 : ℝ) * z (n+1) + (p0 : ℝ) * z n = m) :
    ∀ n : ℕ, ∃ m : ℤ, z n = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · exact hbase n hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (m := 4) (n := n) (by omega)
    obtain ⟨m, hm⟩ := hforce k
    obtain ⟨m0, hm0⟩ := ih k (by omega)
    obtain ⟨m1, hm1⟩ := ih (k+1) (by omega)
    obtain ⟨m2, hm2⟩ := ih (k+2) (by omega)
    obtain ⟨m3, hm3⟩ := ih (k+3) (by omega)
    refine ⟨m - p3*m3 - p2*m2 - p1*m1 - p0*m0, ?_⟩
    rw [hk, show 4+k = k+4 by omega]
    rw [hm3, hm2, hm1, hm0] at hm
    push_cast
    linarith

/-- Four exact left anchors and actual integer forcing restore the Fourier
 congruence. The residual hypothesis concerns the restored trajectory `y`, not `H`. -/
theorem quartic_forcing_congruent_expanding (p0 p1 p2 p3 : ℤ) (b c : ℝ) (hb : b ≠ 0)
    (hroot : b ^ 4 + (p3 : ℝ) * b ^ 3 + (p2 : ℝ) * b ^ 2 + (p1 : ℝ) * b + p0 = 0)
    (y : ℤ → ℝ)
    (hanchor : ∀ n : ℕ, n < 4 → y ((n : ℤ)-4) = c * b ^ ((n : ℤ)-4))
    (hforce : ∀ j : ℤ, -4 ≤ j → ∃ m : ℤ, quarticResidual p0 p1 p2 p3 y j = m) :
    ∀ j : ℤ, -4 ≤ j → ∃ m : ℤ, y j - c * b ^ j = m := by
  let z : ℕ → ℝ := fun n => y ((n : ℤ)-4) - c * b ^ ((n : ℤ)-4)
  have hbase (n : ℕ) (hn : n < 4) : ∃ m : ℤ, z n = m := by
    refine ⟨0, ?_⟩
    simp only [z, hanchor n hn, sub_self, Int.cast_zero]
  have hforcing (n : ℕ) : ∃ m : ℤ,
      z (n+4) + (p3 : ℝ) * z (n+3) + (p2 : ℝ) * z (n+2) +
        (p1 : ℝ) * z (n+1) + (p0 : ℝ) * z n = m := by
    obtain ⟨m, hm⟩ := hforce ((n : ℤ)-4) (by omega)
    have hz := quarticResidual_expanding_zero p0 p1 p2 p3 b c hb hroot ((n : ℤ)-4)
    have hd : quarticResidual p0 p1 p2 p3 (fun j => y j - c*b^j) ((n : ℤ)-4) = m := by
      unfold quarticResidual at hm hz ⊢
      linarith
    refine ⟨m, ?_⟩
    unfold quarticResidual at hd
    dsimp only [z]
    have hidx (d : ℕ) : ((n+d : ℕ) : ℤ)-4 = ((n : ℤ)-4)+(d : ℤ) := by push_cast; ring
    simp_rw [hidx]
    exact hd
  have hz := integer_quartic_sequence z p0 p1 p2 p3 hbase hforcing
  intro j hj
  let n := (j+4).toNat
  have hn : (n : ℤ)-4 = j := by dsimp [n]; omega
  simpa only [z, hn] using hz n

/-- An exact entire incoming left tail supplies the four anchors and also covers
 the remaining negative indices; no global integer forcing of a localized profile is inferred. -/
theorem quartic_forcing_global_congruent_expanding (p0 p1 p2 p3 : ℤ) (b c : ℝ) (hb : b ≠ 0)
    (hroot : b ^ 4 + (p3 : ℝ) * b ^ 3 + (p2 : ℝ) * b ^ 2 + (p1 : ℝ) * b + p0 = 0)
    (y : ℤ → ℝ) (hleft : ∀ j : ℤ, j < 0 → y j = c * b ^ j)
    (hforce : ∀ j : ℤ, -4 ≤ j → ∃ m : ℤ, quarticResidual p0 p1 p2 p3 y j = m) :
    ∀ j : ℤ, ∃ m : ℤ, y j - c * b ^ j = m := by
  have hcong := quartic_forcing_congruent_expanding p0 p1 p2 p3 b c hb hroot y
    (fun n hn => hleft _ (by omega)) hforce
  intro j
  by_cases hj : -4 ≤ j
  · exact hcong j hj
  · exact ⟨0, by rw [hleft j (by omega), sub_self, Int.cast_zero]⟩

/-- The outgoing neutral mode is switched on only after the localized core. -/
noncomputable def outgoingNeutralWave (a ζ : ℂ) (ell j : ℤ) : ℝ :=
  if ell ≤ j then (a * ζ ^ (j-ell)).re else 0

/-- An actual complex quartic root generates a homogeneous real neutral mode. -/
theorem quarticResidual_neutral_zero (p0 p1 p2 p3 : ℤ) (a ζ : ℂ) (hζ : ζ ≠ 0)
    (hroot : ζ ^ 4 + (p3 : ℂ) * ζ ^ 3 + (p2 : ℂ) * ζ ^ 2 + (p1 : ℂ) * ζ + p0 = 0)
    (j : ℤ) : quarticResidual p0 p1 p2 p3 (fun k => (a * ζ ^ k).re) j = 0 := by
  have heq : a * ζ ^ (j+4) + (p3 : ℂ) * (a * ζ ^ (j+3)) +
      (p2 : ℂ) * (a * ζ ^ (j+2)) + (p1 : ℂ) * (a * ζ ^ (j+1)) +
      (p0 : ℂ) * (a * ζ ^ j) = 0 := by
    simp only [zpow_add₀ hζ, zpow_ofNat]
    calc
      _ = a * ζ ^ j * (ζ ^ 4 + (p3 : ℂ) * ζ ^ 3 + (p2 : ℂ) * ζ ^ 2 + (p1 : ℂ) * ζ + p0) := by ring
      _ = 0 := by rw [hroot, mul_zero]
  have hr := congrArg Complex.re heq
  simpa [quarticResidual] using hr

/-- Before the four outgoing boundary windows, the switched-on wave has no residual. -/
theorem quarticResidual_outgoing_left_zero (p0 p1 p2 p3 : ℤ) (a ζ : ℂ) (ell j : ℤ)
    (hj : j+4 < ell) : quarticResidual p0 p1 p2 p3 (outgoingNeutralWave a ζ ell) j = 0 := by
  unfold quarticResidual outgoingNeutralWave
  split_ifs <;> try omega
  ring

/-- After its boundary windows the actual switched-on neutral mode is homogeneous. -/
theorem quarticResidual_outgoing_right_zero (p0 p1 p2 p3 : ℤ) (a ζ : ℂ) (hζ : ζ ≠ 0)
    (hroot : ζ ^ 4 + (p3 : ℂ) * ζ ^ 3 + (p2 : ℂ) * ζ ^ 2 + (p1 : ℂ) * ζ + p0 = 0)
    (ell j : ℤ) (hj : ell ≤ j) :
    quarticResidual p0 p1 p2 p3 (outgoingNeutralWave a ζ ell) j = 0 := by
  have h := quarticResidual_neutral_zero p0 p1 p2 p3 a ζ hζ hroot (j-ell)
  unfold quarticResidual outgoingNeutralWave
  simp only [show ell ≤ j+4 by omega, show ell ≤ j+3 by omega, show ell ≤ j+2 by omega,
    show ell ≤ j+1 by omega, hj, ite_true]
  simpa only [quarticResidual, sub_add_eq_add_sub] using h

/-- The first four switch-on residuals are explicit, and must be cancelled by
 the actual localized junction rather than silently declared integer. -/
theorem quarticResidual_outgoing_boundary (p0 p1 p2 p3 : ℤ) (a ζ : ℂ) (ell : ℤ) :
    quarticResidual p0 p1 p2 p3 (outgoingNeutralWave a ζ ell) (ell-4) = a.re ∧
    quarticResidual p0 p1 p2 p3 (outgoingNeutralWave a ζ ell) (ell-3) =
      (a*ζ).re + (p3 : ℝ)*a.re ∧
    quarticResidual p0 p1 p2 p3 (outgoingNeutralWave a ζ ell) (ell-2) =
      (a*ζ^2).re + (p3 : ℝ)*(a*ζ).re + (p2 : ℝ)*a.re ∧
    quarticResidual p0 p1 p2 p3 (outgoingNeutralWave a ζ ell) (ell-1) =
      (a*ζ^3).re + (p3 : ℝ)*(a*ζ^2).re + (p2 : ℝ)*(a*ζ).re + (p1 : ℝ)*a.re := by
  have hi (k : ℤ) : ell-k+4 = ell+(4-k) := by ring
  have hi3 (k : ℤ) : ell-k+3 = ell+(3-k) := by ring
  have hi2 (k : ℤ) : ell-k+2 = ell+(2-k) := by ring
  have hi1 (k : ℤ) : ell-k+1 = ell+(1-k) := by ring
  have hw (k : ℤ) : outgoingNeutralWave a ζ ell (ell+k) =
      if 0 ≤ k then (a*ζ^k).re else 0 := by
    unfold outgoingNeutralWave
    simp
  simp only [quarticResidual]
  simp only [hi, hi3, hi2, hi1]
  norm_num [hw, outgoingNeutralWave]

/-- Actual restored forcing follows from incoming/interior forcing and four
 explicit localized-junction cancellations. No integer-forcing claim is made for `H`
 at those four junction indices. -/
theorem quartic_forcing_restored_of_boundary (p0 p1 p2 p3 : ℤ) (H : ℤ → ℝ)
    (a ζ : ℂ) (hζ : ζ ≠ 0)
    (hroot : ζ ^ 4 + (p3 : ℂ) * ζ ^ 3 + (p2 : ℂ) * ζ ^ 2 + (p1 : ℂ) * ζ + p0 = 0)
    (ell : ℤ)
    (houtside : ∀ j : ℤ, j+4 < ell ∨ ell ≤ j →
      ∃ m : ℤ, quarticResidual p0 p1 p2 p3 H j = m)
    (hb0 : ∃ m : ℤ, quarticResidual p0 p1 p2 p3 H (ell-4) + a.re = m)
    (hb1 : ∃ m : ℤ, quarticResidual p0 p1 p2 p3 H (ell-3) +
      ((a*ζ).re + (p3 : ℝ)*a.re) = m)
    (hb2 : ∃ m : ℤ, quarticResidual p0 p1 p2 p3 H (ell-2) +
      ((a*ζ^2).re + (p3 : ℝ)*(a*ζ).re + (p2 : ℝ)*a.re) = m)
    (hb3 : ∃ m : ℤ, quarticResidual p0 p1 p2 p3 H (ell-1) +
      ((a*ζ^3).re + (p3 : ℝ)*(a*ζ^2).re + (p2 : ℝ)*(a*ζ).re + (p1 : ℝ)*a.re) = m) :
    ∀ j : ℤ, ∃ m : ℤ,
      quarticResidual p0 p1 p2 p3 (fun k => H k + outgoingNeutralWave a ζ ell k) j = m := by
  intro j
  rw [quarticResidual_add]
  by_cases hl : j+4 < ell
  · rw [quarticResidual_outgoing_left_zero p0 p1 p2 p3 a ζ ell j hl, add_zero]
    exact houtside j (Or.inl hl)
  by_cases hr : ell ≤ j
  · rw [quarticResidual_outgoing_right_zero p0 p1 p2 p3 a ζ hζ hroot ell j hr, add_zero]
    exact houtside j (Or.inr hr)
  have hb := quarticResidual_outgoing_boundary p0 p1 p2 p3 a ζ ell
  have hj : j = ell-4 ∨ j = ell-3 ∨ j = ell-2 ∨ j = ell-1 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · rwa [hb.1]
  · rwa [hb.2.1]
  · rwa [hb.2.2.1]
  · rwa [hb.2.2.2]

/-- Uniform summation of the two explicit nonnegative restoration costs. -/
theorem sharp_restoration_cost_sum_le (H : ℕ → ℝ) (h r Δ : ℝ) (a ζ : ℂ)
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hH : ∀ k, |H k| ≤ h * r ^ (k+1))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0) (m : ℕ) :
    (∑ k ∈ Finset.range m, (20 * |H k| * Δ + 10 * (a * ζ ^ k).re ^ 2)) ≤
      20 * Δ * h * r / (1-r) + 10 * Δ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have habs := stable_tail_abs_sum_le H h r hh hr0 hr1 hH m
  have hsquare : (∑ k ∈ Finset.range m, (a * ζ ^ k).re ^ 2) ≤
      Δ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
    apply (neutral_sq_sum_le a ζ hζ hne m).trans
    gcongr
  calc
    _ = 20 * Δ * (∑ k ∈ Finset.range m, |H k|) +
        10 * (∑ k ∈ Finset.range m, (a * ζ ^ k).re ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 20 * Δ * (h*r/(1-r)) +
        10 * (Δ ^ 2 * ((m : ℝ) / 2 + 1 / ‖1 - ζ ^ 2‖)) := by gcongr
    _ = _ := by ring

/-- The sharp restoration theorem for every true infinite left prefix. The baseline
 is the actual full bilateral action of `H`; only its outgoing stable tail is perturbed. -/
theorem sharp_restoration_bilateral_prefix_sum_le (H : ℤ → ℝ) (h r Δ : ℝ) (a ζ : ℂ)
    (ell J : ℕ) (hVH : Summable (fun j : ℤ => cosinePotential (H j)))
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hH : ∀ k : ℕ, |H ((ell : ℤ)+k)| ≤ h * r ^ (k+1))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0)
    (hsmall : h*r + Δ ≤ (1 / 100 : ℝ)) (n : ℤ) (hn : n ≤ J) :
    Summable (fun k : ℕ => cosinePotential
      (H (n-k) + outgoingNeutralWave a ζ ell (n-k))) ∧
    (∑' k : ℕ, cosinePotential (H (n-k) + outgoingNeutralWave a ζ ell (n-k))) ≤
      (∑' j : ℤ, cosinePotential (H j)) + 20 * Δ * h * r / (1-r) +
        10 * Δ ^ 2 * (((J : ℝ)+1) / 2 + 1 / ‖1 - ζ ^ 2‖) := by
  classical
  have hΔ : 0 ≤ Δ := (norm_nonneg a).trans ha
  have hV0 (u : ℝ) : 0 ≤ cosinePotential u := by
    unfold cosinePotential
    exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  let e : Fin (J+1) → ℤ := fun i => (ell : ℤ) + (i : ℕ)
  let p : Fin (J+1) → ℝ := fun i =>
    20 * |H (e i)| * Δ + 10 * (a * ζ ^ (i : ℕ)).re ^ 2
  have hp0 (i : Fin (J+1)) : 0 ≤ p i := by dsimp [p]; positivity
  have hC0 (j : ℤ) : 0 ≤ ∑ i : Fin (J+1), if j = e i then p i else 0 := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hp0 i
    · exact le_rfl
  have hpoint (j : ℤ) (hj : j ≤ n) :
      cosinePotential (H j + outgoingNeutralWave a ζ ell j) ≤ cosinePotential (H j) +
        ∑ i : Fin (J+1), if j = e i then p i else 0 := by
    by_cases hl : j < ell
    · rw [outgoingNeutralWave, ite_eq_right (by omega), add_zero]
      exact le_add_of_nonneg_right (hC0 j)
    let q : ℕ := (j-(ell : ℤ)).toNat
    have hq : q < J+1 := by dsimp [q]; omega
    let i : Fin (J+1) := ⟨q, hq⟩
    have hji : j = e i := by dsimp [e, i, q]; omega
    have hHi : |H j| ≤ h*r := by
      have hhq := hH q
      rw [hji]
      change |H ((ell : ℤ)+q)| ≤ h*r
      apply hhq.trans
      calc
        _ = (h*r)*r^q := by ring
        _ ≤ h*r := by
          simpa using mul_le_mul_of_nonneg_left
            (show r^q ≤ 1 from pow_le_one₀ hr0 hr1.le) (mul_nonneg hh hr0)
    have hchi : |(a*ζ^q).re| ≤ Δ := by
      calc
        _ ≤ ‖a*ζ^q‖ := Complex.abs_re_le_norm _
        _ ≤ Δ := by simpa [norm_mul, norm_pow, hζ] using ha
    have hwi : outgoingNeutralWave a ζ ell j = (a*ζ^q).re := by
      unfold outgoingNeutralWave
      rw [ite_eq_left (by omega)]
      have he : j-(ell : ℤ) = (q : ℤ) := by dsimp [q]; omega
      rw [he, zpow_natCast]
    have hterm : p i ≤ ∑ i' : Fin (J+1), if j = e i' then p i' else 0 := by
      have hs := Finset.single_le_sum
        (s := Finset.univ) (f := fun i' : Fin (J+1) => if j = e i' then p i' else 0)
        (fun i' _ => by split_ifs; exact hp0 i'; exact le_rfl) (Finset.mem_univ i)
      simpa only [hji, ite_true] using hs
    rw [hwi]
    calc
      _ ≤ cosinePotential (H j) + 20 * |H j| * |(a*ζ^q).re| + 10 * (a*ζ^q).re^2 :=
        cosinePotential_add_le_sharp _ _ ((add_le_add hHi hchi).trans hsmall)
      _ ≤ cosinePotential (H j) + p i := by
        dsimp [p, i]
        rw [← hji]
        nlinarith [mul_le_mul_of_nonneg_left hchi (show 0 ≤ 20 * |H j| by positivity)]
      _ ≤ _ := add_le_add le_rfl hterm
  have hb := bilateral_prefix_bound_of_finite_corrections
    (fun j => cosinePotential (H j))
    (fun j => cosinePotential (H j + outgoingNeutralWave a ζ ell j)) e p n
    hVH (fun j => hV0 _) (fun j => hV0 _) hp0 hpoint
  have hpSum : (∑ i : Fin (J+1), p i) =
      ∑ k ∈ Finset.range (J+1),
        (20 * |H ((ell : ℤ)+k)| * Δ + 10 * (a*ζ^k).re^2) := by
    exact Fin.sum_univ_eq_sum_range (fun k =>
      20 * |H ((ell : ℤ)+k)| * Δ + 10 * (a*ζ^k).re^2) (J+1)
  have hpBound := sharp_restoration_cost_sum_le (fun k => H ((ell : ℤ)+k))
    h r Δ a ζ hh hr0 hr1 hH ha hζ hne (J+1)
  refine ⟨hb.1, ?_⟩
  rw [hpSum] at hb
  have hres := hb.2.trans (add_le_add le_rfl hpBound)
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hres

/-- Coarse common bounds on the stable contraction and unit-root separation
 retain the exact sharp-restoration constants needed by both Appendix certificates. -/
theorem sharp_restoration_budget_le_coarse (E Δ h J r d : ℝ)
    (hΔ : 0 ≤ Δ) (hh : 0 ≤ h) (_hr0 : 0 ≤ r) (hr : r ≤ 3 / 5) (hd : 1 ≤ d) :
    E + 20 * Δ * h * r / (1-r) + 10 * Δ ^ 2 * ((J+1)/2 + 1/d) ≤
      E + 30 * Δ * h + 10 * Δ ^ 2 * ((J+1)/2 + 1) := by
  have hratio : r / (1-r) ≤ (3 / 2 : ℝ) :=
    (div_le_iff₀ (by linarith : 0 < 1-r)).2 (by linarith)
  have hdinv : 1/d ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
  calc
    _ = E + (20*Δ*h) * (r/(1-r)) + 10*Δ^2*((J+1)/2+1/d) := by ring
    _ ≤ E + (20*Δ*h) * (3/2) + 10*Δ^2*((J+1)/2+1) := by gcongr
    _ = _ := by ring

/-- The first Appendix Fourier budget is strictly below `51.18` with the source
 values `J₁=2·10²⁵`, `Δ₁=9.498·10⁻¹⁴`, and `h₁=10⁻²`. -/
theorem sharp_restoration_p1_budget_lt (r d : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 1 ≤ d) :
    (5027/100 : ℝ) + 20 * (9498 / 10^17 : ℝ) * (1/100 : ℝ) * r / (1-r) +
      10 * (9498 / 10^17 : ℝ)^2 * (((2*10^25 : ℝ)+1)/2 + 1/d) < 2559/50 := by
  apply (sharp_restoration_budget_le_coarse (5027/100) (9498/10^17) (1/100)
    (2*10^25) r d (by norm_num) (by norm_num) hr0 hr hd).trans_lt
  norm_num

/-- The second Appendix Fourier budget is strictly below `47.63` with the source
 values `J₂=10²⁶`, `Δ₂=1.105305·10⁻¹⁵`, and `h₂=10⁻²³`. -/
theorem sharp_restoration_p2_budget_lt (r d : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 1 ≤ d) :
    (5953342/125000 : ℝ) + 20 * (1105305 / 10^21 : ℝ) * (1/10^23 : ℝ) * r / (1-r) +
      10 * (1105305 / 10^21 : ℝ)^2 * (((10^26 : ℝ)+1)/2 + 1/d) < 4763/100 := by
  apply (sharp_restoration_budget_le_coarse (5953342/125000) (1105305/10^21) (1/10^23)
    (10^26) r d (by norm_num) (by norm_num) hr0 hr hd).trans_lt
  norm_num

/-- A finite exact power comparison bounds an exponential times a squared modulus. -/
theorem exp_mul_sq_lt_one_of_power_comparison (a q : ℝ) (m n : ℕ) (hn : n ≠ 0)
    (hq : Real.exp 1 ≤ q) (hnum : q ^ m * a ^ (2*n) < 1) :
    Real.exp ((m : ℝ)/n) * a ^ 2 < 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have heq : (n : ℝ) * ((m : ℝ)/n) = m := by field_simp
  have hpow : (Real.exp ((m : ℝ)/n) * a ^ 2) ^ n ≤ q ^ m * a ^ (2*n) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, heq]
    have hexp : Real.exp (m : ℝ) ≤ q ^ m := by
      have h := pow_le_pow_left₀ (Real.exp_pos 1).le hq m
      simpa only [← Real.exp_nat_mul, mul_one] using h
    exact mul_le_mul_of_nonneg_right hexp (by rw [pow_mul]; positivity)
  apply lt_of_pow_lt_pow_left₀ n (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_pow] using hpow.trans_lt hnum

/-- A coarser freshly certified first-configuration action up to `50.3` still
 leaves room for the unchanged modulus `a₁`, using total threshold `51.22`. -/
theorem sharp_restoration_p1_budget_lt_relaxed (E r d : ℝ) (hE : E ≤ 503/10)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 1 ≤ d) :
    E + 20 * (9498 / 10^17 : ℝ) * (1/100 : ℝ) * r / (1-r) +
      10 * (9498 / 10^17 : ℝ)^2 * (((2*10^25 : ℝ)+1)/2 + 1/d) < 2561/50 := by
  apply (sharp_restoration_budget_le_coarse E (9498/10^17) (1/100)
    (2*10^25) r d (by norm_num) (by norm_num) hr0 hr hd).trans_lt
  linarith

/-- A second-configuration action up to `47.63` still leaves room for the
 unchanged modulus `a₂`, using total threshold `47.64`. -/
theorem sharp_restoration_p2_budget_lt_relaxed (E r d : ℝ) (hE : E ≤ 4763/100)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 1 ≤ d) :
    E + 20 * (1105305 / 10^21 : ℝ) * (1/10^23 : ℝ) * r / (1-r) +
      10 * (1105305 / 10^21 : ℝ)^2 * (((10^26 : ℝ)+1)/2 + 1/d) < 1191/25 := by
  apply (sharp_restoration_budget_le_coarse E (1105305/10^21) (1/10^23)
    (10^26) r d (by norm_num) (by norm_num) hr0 hr hd).trans_lt
  linarith

set_option exponentiation.threshold 5000 in
/-- The unchanged first modulus satisfies its rigorous exponential comparison
 even at the relaxed action threshold `51.22`. -/
theorem restoration_p1_exp_modulus_lt_one :
    Real.exp (2561/50 : ℝ) * (3 / (4*10^11) : ℝ)^2 < 1 := by
  apply exp_mul_sq_lt_one_of_power_comparison (3/(4*10^11)) (87/32) 2561 50
    (by norm_num)
  · linarith [Real.exp_one_lt_d9]
  · norm_num

set_option exponentiation.threshold 5000 in
/-- The unchanged second modulus satisfies its rigorous exponential comparison
 even at the relaxed action threshold `47.64`. -/
theorem restoration_p2_exp_modulus_lt_one :
    Real.exp (1191/25 : ℝ) * (9 / (2*10^11) : ℝ)^2 < 1 := by
  have h := exp_mul_sq_lt_one_of_power_comparison (9/(2*10^11)) (87/32) 4764 100
    (by norm_num) (by linarith [Real.exp_one_lt_d9]) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A squared Fourier bound converts to a strict modulus bound by an exact
 exponential comparison. -/
theorem modulus_gt_of_exp_action (s a L : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hscalar : Real.exp L * a ^ 2 < 1) (haction : Real.exp (-L) ≤ s ^ 2) : a < s := by
  have ha2 : a ^ 2 < Real.exp (-L) := by
    rw [Real.exp_neg, ← one_div]
    apply (lt_div_iff₀ (Real.exp_pos L)).2
    nlinarith
  nlinarith

/-- The first paper modulus is available at every coefficient with the rigorous
 relaxed action budget; no numerical Fourier assertion is assumed. -/
theorem restoration_p1_modulus_gt (s A : ℝ) (hs : 0 ≤ s) (hA : A ≤ 2561/50)
    (haction : Real.exp (-A) ≤ s ^ 2) : (3 / (4*10^11) : ℝ) < s := by
  apply modulus_gt_of_exp_action s (3/(4*10^11)) (2561/50) hs (by norm_num)
    restoration_p1_exp_modulus_lt_one
  exact (Real.exp_le_exp.mpr (neg_le_neg hA)).trans haction

/-- The second paper modulus is likewise unchanged at the relaxed action budget. -/
theorem restoration_p2_modulus_gt (s A : ℝ) (hs : 0 ≤ s) (hA : A ≤ 1191/25)
    (haction : Real.exp (-A) ≤ s ^ 2) : (9 / (2*10^11) : ℝ) < s := by
  apply modulus_gt_of_exp_action s (9/(2*10^11)) (1191/25) hs (by norm_num)
    restoration_p2_exp_modulus_lt_one
  exact (Real.exp_le_exp.mpr (neg_le_neg hA)).trans haction

/-- Optional second-configuration slack: an actual action up to `47.64` still
 restores below `47.645`, without changing the final modulus. -/
theorem sharp_restoration_p2_budget_lt_backup (E r d : ℝ) (hE : E ≤ 1191/25)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 1 ≤ d) :
    E + 20 * (1105305 / 10^21 : ℝ) * (1/10^23 : ℝ) * r / (1-r) +
      10 * (1105305 / 10^21 : ℝ)^2 * (((10^26 : ℝ)+1)/2 + 1/d) < 9529/200 := by
  apply (sharp_restoration_budget_le_coarse E (1105305/10^21) (1/10^23)
    (10^26) r d (by norm_num) (by norm_num) hr0 hr hd).trans_lt
  linarith

set_option exponentiation.threshold 10000 in
/-- A tighter rational exponential enclosure certifies the unchanged second
 modulus at the optional `47.645` threshold. -/
theorem restoration_p2_exp_modulus_lt_one_backup :
    Real.exp (9529/200 : ℝ) * (9 / (2*10^11) : ℝ)^2 < 1 := by
  apply exp_mul_sq_lt_one_of_power_comparison (9/(2*10^11)) (27183/10000) 9529 200
    (by norm_num)
  · linarith [Real.exp_one_lt_d9]
  · norm_num

/-- The optional larger second action threshold preserves exactly `a₂`. -/
theorem restoration_p2_modulus_gt_backup (s A : ℝ) (hs : 0 ≤ s) (hA : A ≤ 9529/200)
    (haction : Real.exp (-A) ≤ s ^ 2) : (9 / (2*10^11) : ℝ) < s := by
  apply modulus_gt_of_exp_action s (9/(2*10^11)) (9529/200) hs (by norm_num)
    restoration_p2_exp_modulus_lt_one_backup
  exact (Real.exp_le_exp.mpr (neg_le_neg hA)).trans haction

/-- Strict centering of the incoming localized profile and a small restored tail
 prove strict centering of the true restored trajectory, including every outgoing index. -/
theorem restored_trajectory_centered (H : ℤ → ℝ) (h r Δ : ℝ) (a ζ : ℂ) (ell : ℕ)
    (hleft : ∀ j : ℤ, j < ell → |H j| < (1/2 : ℝ))
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hH : ∀ k : ℕ, |H ((ell : ℤ)+k)| ≤ h * r ^ (k+1))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hsmall : h*r + Δ ≤ (1/100 : ℝ)) :
    ∀ j : ℤ, |H j + outgoingNeutralWave a ζ ell j| < (1/2 : ℝ) := by
  intro j
  by_cases hl : j < ell
  · rw [outgoingNeutralWave, ite_eq_right (by omega), add_zero]
    exact hleft j hl
  let q := (j-(ell : ℤ)).toNat
  have hj : j = (ell : ℤ)+(q : ℤ) := by dsimp [q]; omega
  have hHi : |H j| ≤ h*r := by
    rw [hj]
    apply (hH q).trans
    calc
      _ = (h*r)*r^q := by ring
      _ ≤ h*r := by
        simpa using mul_le_mul_of_nonneg_left
          (show r^q ≤ 1 from pow_le_one₀ hr0 hr1.le) (mul_nonneg hh hr0)
  have hw : |outgoingNeutralWave a ζ ell j| ≤ Δ := by
    rw [outgoingNeutralWave, ite_eq_left (by omega)]
    calc
      _ ≤ ‖a*ζ^(j-(ell : ℤ))‖ := Complex.abs_re_le_norm _
      _ ≤ Δ := by simpa [norm_mul, norm_zpow, hζ] using ha
  exact ((abs_add_le _ _).trans ((add_le_add hHi hw).trans hsmall)).trans_lt (by norm_num)

/-- Integer congruence preserves both the actual potential and the condition
 excluding cosine zeros. This lemma does not totalize an infinite action. -/
theorem cosinePotential_congruence (u v : ℝ) (h : ∃ m : ℤ, u-v = m) :
    cosinePotential u = cosinePotential v ∧
      (Real.cos (Real.pi*u) = 0 ↔ Real.cos (Real.pi*v) = 0) := by
  obtain ⟨m, hm⟩ := h
  have heq : u = v+m := by linarith
  have hd := Real.cos_add_int_mul_two_pi (2*(Real.pi*v)) m
  have harg : 2*(Real.pi*(v+m)) = 2*(Real.pi*v) + m*(2*Real.pi) := by ring
  rw [← harg] at hd
  have hsquare : Real.cos (Real.pi*u)^2 = Real.cos (Real.pi*v)^2 := by
    rw [heq]
    nlinarith [Real.cos_two_mul (Real.pi*(v+m)), Real.cos_two_mul (Real.pi*v)]
  constructor
  · unfold cosinePotential
    rw [hsquare]
  · constructor
    · intro hz
      apply sq_eq_zero_iff.mp
      rw [← hsquare, hz]
      norm_num
    · intro hz
      apply sq_eq_zero_iff.mp
      rw [hsquare, hz]
      norm_num

/-- The actual restored trajectory and its explicitly proved Fourier congruence
 give the Bernoulli coefficient bound. The action bound is derived from restoration,
 and strict centering proves the required exclusion of cosine zeros. -/
theorem sharp_restoration_fourier_bound (b c : ℝ) (hb : 1 < b)
    (H : ℤ → ℝ) (h r Δ : ℝ) (a ζ : ℂ) (ell J : ℕ)
    (hVH : Summable (fun j : ℤ => cosinePotential (H j)))
    (hleft : ∀ j : ℤ, j < ell → |H j| < (1/2 : ℝ))
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hH : ∀ k : ℕ, |H ((ell : ℤ)+k)| ≤ h * r ^ (k+1))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0)
    (hsmall : h*r + Δ ≤ (1/100 : ℝ))
    (hcong : ∀ j : ℤ, ∃ m : ℤ,
      H j + outgoingNeutralWave a ζ ell j - c*b^j = m)
    (n : ℕ) (hn : n ≤ J) :
    Real.exp (-((∑' j : ℤ, cosinePotential (H j)) + 20 * Δ * h * r / (1-r) +
      10 * Δ ^ 2 * (((J : ℝ)+1) / 2 + 1 / ‖1 - ζ ^ 2‖))) ≤
      ‖MeasureTheory.charFun (ElementaryCore.bernoulliLaw b) (Real.pi * (c*b^n))‖ ^ 2 := by
  have hb0 : b ≠ 0 := by linarith
  have hcenter := restored_trajectory_centered H h r Δ a ζ ell hleft hh hr0 hr1 hH ha hζ hsmall
  have hcos (j : ℤ) : Real.cos (Real.pi*(H j + outgoingNeutralWave a ζ ell j)) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    have h := abs_lt.mp (hcenter j)
    constructor <;> nlinarith [Real.pi_pos]
  have hpow (k : ℕ) : (c*b^n)*b⁻¹^k = c*b^((n : ℤ)-(k : ℤ)) := by
    rw [zpow_sub₀ hb0]
    simp only [zpow_natCast, div_eq_mul_inv, inv_pow]
    ring
  have hphase (k : ℕ) :
      cosinePotential ((c*b^n)*b⁻¹^k) =
        cosinePotential (H ((n : ℤ)-k) + outgoingNeutralWave a ζ ell ((n : ℤ)-k)) ∧
      (Real.cos (Real.pi*((c*b^n)*b⁻¹^k)) = 0 ↔
        Real.cos (Real.pi*(H ((n : ℤ)-k) + outgoingNeutralWave a ζ ell ((n : ℤ)-k))) = 0) := by
    apply cosinePotential_congruence
    obtain ⟨m, hm⟩ := hcong ((n : ℤ)-k)
    refine ⟨-m, ?_⟩
    rw [hpow]
    push_cast
    linarith
  have haction := sharp_restoration_bilateral_prefix_sum_le H h r Δ a ζ ell J hVH
    hh hr0 hr1 hH ha hζ hne hsmall (n : ℤ) (by exact_mod_cast hn)
  apply exp_neg_action_le_norm_charFun_sq b hb (c*b^n)
  · intro k hk
    exact hcos _ ((hphase k).2.mp hk)
  · intro m
    have hV0 (k : ℕ) : 0 ≤ cosinePotential
        (H ((n : ℤ)-k) + outgoingNeutralWave a ζ ell ((n : ℤ)-k)) := by
      unfold cosinePotential
      exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
    have hfinite := Summable.sum_le_tsum (Finset.range m) (fun k _ => hV0 k) haction.1
    have hv (k : ℕ) := (hphase k).1
    simpa only [hv] using hfinite.trans haction.2

/-- The restored Fourier bound can be supplied by exact incoming exponential
 data and actual integer forcing. The localized profile is never treated as if it
 already had the outgoing neutral term or globally integer forcing. -/
theorem sharp_restoration_fourier_bound_of_forcing (p0 p1 p2 p3 : ℤ) (b c : ℝ) (hb : 1 < b)
    (hroot : b ^ 4 + (p3 : ℝ) * b ^ 3 + (p2 : ℝ) * b ^ 2 + (p1 : ℝ) * b + p0 = 0)
    (H : ℤ → ℝ) (h r Δ : ℝ) (a ζ : ℂ) (ell J : ℕ)
    (hVH : Summable (fun j : ℤ => cosinePotential (H j)))
    (hincoming : ∀ j : ℤ, j < 0 → H j = c*b^j)
    (hleft : ∀ j : ℤ, j < ell → |H j| < (1/2 : ℝ))
    (hh : 0 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hH : ∀ k : ℕ, |H ((ell : ℤ)+k)| ≤ h * r ^ (k+1))
    (ha : ‖a‖ ≤ Δ) (hζ : ‖ζ‖ = 1) (hne : 1 - ζ ^ 2 ≠ 0)
    (hsmall : h*r + Δ ≤ (1/100 : ℝ))
    (hforce : ∀ j : ℤ, -4 ≤ j → ∃ m : ℤ,
      quarticResidual p0 p1 p2 p3 (fun k => H k + outgoingNeutralWave a ζ ell k) j = m)
    (n : ℕ) (hn : n ≤ J) :
    Real.exp (-((∑' j : ℤ, cosinePotential (H j)) + 20 * Δ * h * r / (1-r) +
      10 * Δ ^ 2 * (((J : ℝ)+1) / 2 + 1 / ‖1 - ζ ^ 2‖))) ≤
      ‖MeasureTheory.charFun (ElementaryCore.bernoulliLaw b) (Real.pi * (c*b^n))‖ ^ 2 := by
  have hcong := quartic_forcing_global_congruent_expanding p0 p1 p2 p3 b c
    (by linarith) hroot (fun j => H j + outgoingNeutralWave a ζ ell j) (by
      intro j hj
      rw [outgoingNeutralWave, ite_eq_right (by omega), add_zero, hincoming j hj]) hforce
  exact sharp_restoration_fourier_bound b c hb H h r Δ a ζ ell J hVH hleft hh hr0 hr1
    hH ha hζ hne hsmall hcong n hn

/-- Absolute-value frequency normalization preserves the actual characteristic
 modulus, so the restoration coefficients use precisely the paper's frequencies. -/
theorem norm_charFun_mul_abs (μ : MeasureTheory.Measure ℝ) (t c : ℝ) :
    ‖MeasureTheory.charFun μ (t*|c|)‖ = ‖MeasureTheory.charFun μ (t*c)‖ := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
  · rw [abs_of_neg (by linarith : c < 0), show t*(-c) = -(t*c) by ring,
      MeasureTheory.charFun_neg]
    simp

end Salem
