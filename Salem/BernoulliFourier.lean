module

public import Salem.ElementaryGeneric
public import Salem.P1Analytic

@[expose] public section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set Filter Topology ProbabilityTheory

namespace Salem

/-- The finite real prefix of the corrected pointwise Bernoulli series. -/
noncomputable def bernoulliPrefix (β : ℝ) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, β⁻¹ ^ k * ω k

/-- One symmetric sign has characteristic function `cos t` in the probability
 convention `E exp(i*t*X)`, with no factor `2π`. -/
theorem charFun_signMeasure (t : ℝ) :
    charFun ElementaryCore.signMeasure t = (Real.cos t : ℂ) := by
  rw [charFun_apply_real, ElementaryCore.signMeasure, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac]
    norm_num [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_neg]
    ring
  all_goals exact (integrable_dirac (by simp)).smul_measure (by finiteness)

/-- The sign coordinates have their actual product-law independence. -/
theorem iIndepFun_signCoordinates :
    iIndepFun (fun k (ω : ℕ → ℝ) => ω k) ElementaryCore.signProcess := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ => ElementaryCore.signMeasure)
    (X := fun (_ : ℕ) (x : ℝ) => x) (by fun_prop)

/-- The true finite-prefix characteristic function factors into its independent
 symmetric sign factors. -/
theorem charFun_bernoulliPrefix (β : ℝ) (n : ℕ) (t : ℝ) :
    charFun (Measure.map (bernoulliPrefix β n) ElementaryCore.signProcess) t =
      ∏ k ∈ Finset.range n, (Real.cos (t * β⁻¹ ^ k) : ℂ) := by
  have hi : iIndepFun (fun k (ω : ℕ → ℝ) => β⁻¹ ^ k * ω k)
      ElementaryCore.signProcess :=
    iIndepFun_signCoordinates.comp (fun k (x : ℝ) => β⁻¹ ^ k * x) (by fun_prop)
  have heq := (hi.restrict (Finset.range n)).charFun_map_fun_finsetSum_eq_prod
    (by intro k hk; exact ((measurable_pi_apply k).const_mul _).aemeasurable)
  unfold bernoulliPrefix
  calc
    _ = ∏ k ∈ Finset.range n,
        charFun (Measure.map (fun (ω : ℕ → ℝ) => β⁻¹ ^ k * ω k)
          ElementaryCore.signProcess) t := by
      simpa only [Finset.prod_apply] using congrFun heq t
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [charFun_map_mul_comp (measurable_pi_apply k).aemeasurable,
        show Measure.map (fun (ω : ℕ → ℝ) => ω k) ElementaryCore.signProcess =
          ElementaryCore.signMeasure from
          Measure.infinitePi_map_eval (fun _ : ℕ => ElementaryCore.signMeasure) k,
        charFun_signMeasure]
      rw [mul_comm (β⁻¹ ^ k) t]

lemma measurable_bernoulliPrefix (β : ℝ) (n : ℕ) : Measurable (bernoulliPrefix β n) := by
  unfold bernoulliPrefix
  fun_prop

/-- The actual finite prefixes converge almost surely to the actual pointwise series. -/
theorem ae_tendsto_bernoulliPrefix (β : ℝ) (hβ : 1 < β) :
    ∀ᵐ ω ∂ElementaryCore.signProcess, Tendsto (fun n => bernoulliPrefix β n ω) atTop
      (𝓝 (ElementaryCore.bernoulliSeries β ω)) := by
  filter_upwards [ElementaryCore.ae_signProcess_abs_one] with ω hω
  have h := (ElementaryCore.summable_bernoulliSeries_of_signs β hβ ω hω).hasSum.tendsto_sum_nat
  simpa only [bernoulliPrefix, ElementaryCore.bernoulliSeries, mul_comm] using h

/-- Dominated convergence passes finite-prefix characteristic functions to the
 characteristic function of the explicit infinite-series law. -/
theorem tendsto_charFun_bernoulliPrefix (β : ℝ) (hβ : 1 < β) (t : ℝ) :
    Tendsto (fun n => charFun (Measure.map (bernoulliPrefix β n) ElementaryCore.signProcess) t)
      atTop (𝓝 (charFun (ElementaryCore.bernoulliLaw β) t)) := by
  have hpre (n : ℕ) :
      charFun (Measure.map (bernoulliPrefix β n) ElementaryCore.signProcess) t =
        ∫ ω, Complex.exp ((t * bernoulliPrefix β n ω : ℝ) * Complex.I)
          ∂ElementaryCore.signProcess := by
    rw [charFun_apply_real, integral_map_of_stronglyMeasurable
      (measurable_bernoulliPrefix β n) (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have hser : charFun (ElementaryCore.bernoulliLaw β) t =
      ∫ ω, Complex.exp ((t * ElementaryCore.bernoulliSeries β ω : ℝ) * Complex.I)
        ∂ElementaryCore.signProcess := by
    rw [ElementaryCore.bernoulliLaw, charFun_apply_real, integral_map_of_stronglyMeasurable
      (ElementaryCore.measurable_bernoulliSeries β) (by fun_prop)]
    simp only [Complex.ofReal_mul]
  simp_rw [hpre, hser]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact ((show Measurable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) from
      by fun_prop).comp (measurable_bernoulliPrefix β n)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact Filter.Eventually.of_forall (fun ω => (Complex.norm_exp_ofReal_mul_I _).le)
  · filter_upwards [ae_tendsto_bernoulliPrefix β hβ] with ω hω
    have hc : Continuous (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) := by fun_prop
    exact hc.continuousAt.tendsto.comp hω

/-- The cosine factors form a genuine unconditional infinite product; their
 deviations from one are bounded by a summable geometric sequence. -/
theorem multipliable_bernoulliCosine (β : ℝ) (hβ : 1 < β) (t : ℝ) :
    Multipliable (fun k : ℕ => Real.cos (t * β⁻¹ ^ k)) := by
  have hq : 0 < β⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : |β⁻¹| < 1 := by
    rw [abs_of_pos hq]
    exact inv_lt_one_of_one_lt₀ hβ
  have hgeo : Summable (fun k : ℕ => |t| * β⁻¹ ^ k) :=
    (summable_geometric_of_abs_lt_one hq1).mul_left |t|
  have hdev : Summable (fun k : ℕ => ‖Real.cos (t * β⁻¹ ^ k) - 1‖) := by
    apply hgeo.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    have h := Real.abs_cos_sub_cos_le (t * β⁻¹ ^ k) 0
    simpa only [Real.norm_eq_abs, Real.cos_zero, sub_zero, abs_mul, abs_pow,
      abs_of_pos hq] using h
  convert multipliable_one_add_of_summable hdev using 1
  ext k
  ring

/-- The actual iid sign-series characteristic function is its cosine product.
 This uses the probability convention `exp(i*t*x)` throughout. -/
theorem charFun_bernoulliLaw_eq_tprod (β : ℝ) (hβ : 1 < β) (t : ℝ) :
    charFun (ElementaryCore.bernoulliLaw β) t =
      ((∏' k : ℕ, Real.cos (t * β⁻¹ ^ k)) : ℝ) := by
  have hchar := tendsto_charFun_bernoulliPrefix β hβ t
  simp_rw [charFun_bernoulliPrefix] at hchar
  have hprod := (multipliable_bernoulliCosine β hβ t).hasProd.map
    Complex.ofRealHom Complex.continuous_ofReal
  have hlim : Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n,
      (Real.cos (t * β⁻¹ ^ k) : ℂ)) atTop
      (𝓝 (((∏' k : ℕ, Real.cos (t * β⁻¹ ^ k)) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealHom_eq_coe] using hprod.tendsto_prod_nat
  exact tendsto_nhds_unique hchar hlim

/-- Squared cosine is exactly the exponential of the negative real potential,
 under the essential condition excluding the totalized value `Real.log 0`. -/
theorem cos_sq_eq_exp_neg_potential (u : ℝ)
    (hu : Real.cos (Real.pi * u) ≠ 0) :
    Real.cos (Real.pi * u) ^ 2 = Real.exp (-cosinePotential u) := by
  unfold cosinePotential
  rw [neg_neg, Real.exp_log (sq_pos_of_ne_zero hu)]

/-- Exact finite cosine-action identity, with every zero excluded explicitly. -/
theorem cosine_prod_sq_eq_exp_neg_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ k ∈ s, Real.cos (Real.pi * u k) ≠ 0) :
    (∏ k ∈ s, Real.cos (Real.pi * u k)) ^ 2 =
      Real.exp (-(∑ k ∈ s, cosinePotential (u k))) := by
  rw [← Finset.prod_pow, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_congr rfl (fun k hk => cos_sq_eq_exp_neg_potential (u k) (hu k hk))

/-- An actual upper bound on every finite cosine action gives the true Fourier
 magnitude bound. The no-zero premise makes the real logarithmic potential faithful. -/
theorem exp_neg_action_le_norm_charFun_sq (β : ℝ) (hβ : 1 < β) (t A : ℝ)
    (hcos : ∀ k : ℕ, Real.cos (Real.pi * (t * β⁻¹ ^ k)) ≠ 0)
    (hA : ∀ n : ℕ, (∑ k ∈ Finset.range n, cosinePotential (t * β⁻¹ ^ k)) ≤ A) :
    Real.exp (-A) ≤ ‖charFun (ElementaryCore.bernoulliLaw β) (Real.pi * t)‖ ^ 2 := by
  have hlim := (multipliable_bernoulliCosine β hβ (Real.pi * t)).hasProd.tendsto_prod_nat
  have hfin (n : ℕ) : Real.exp (-A) ≤
      (∏ k ∈ Finset.range n, Real.cos (Real.pi * t * β⁻¹ ^ k)) ^ 2 := by
    calc
      _ ≤ Real.exp (-(∑ k ∈ Finset.range n, cosinePotential (t * β⁻¹ ^ k))) :=
        Real.exp_le_exp.mpr (neg_le_neg (hA n))
      _ = _ := by
        symm
        simpa only [mul_assoc] using cosine_prod_sq_eq_exp_neg_sum (Finset.range n)
          (fun k => t * β⁻¹ ^ k) (fun k _ => hcos k)
  have hb := ge_of_tendsto (hlim.pow 2) (Filter.Eventually.of_forall hfin)
  rw [charFun_bernoulliLaw_eq_tprod β hβ (Real.pi * t)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb

/-- The real part of the characteristic function is the paper's cosine expectation. -/
theorem charFun_re_eq_integral_cos (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (charFun μ t).re = ∫ x, Real.cos (t * x) ∂μ := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [charFun_apply_real]
  simp only [← Complex.ofReal_mul]
  calc
    _ = ∫ x, (Complex.exp ((t * x : ℝ) * Complex.I)).re ∂μ := (integral_re hi).symm
    _ = _ := by simp only [Complex.exp_ofReal_mul_I_re]

/-- The true real Fourier transform `E cos(tW)` is the same convergent cosine product. -/
theorem integral_cos_bernoulliLaw_eq_tprod (β : ℝ) (hβ : 1 < β) (t : ℝ) :
    (∫ x, Real.cos (t * x) ∂ElementaryCore.bernoulliLaw β) =
      ∏' k : ℕ, Real.cos (t * β⁻¹ ^ k) := by
  let : IsProbabilityMeasure (ElementaryCore.bernoulliLaw β) := by
    unfold ElementaryCore.bernoulliLaw
    infer_instance
  rw [← charFun_re_eq_integral_cos, charFun_bernoulliLaw_eq_tprod β hβ t]
  simp

/-- Bounded actual prefix actions form a summable nonnegative potential series. -/
theorem summable_cosinePotential_of_prefix_bound (u : ℕ → ℝ) (A : ℝ)
    (hA : ∀ n : ℕ, (∑ k ∈ Finset.range n, cosinePotential (u k)) ≤ A) :
    Summable (fun k => cosinePotential (u k)) := by
  apply summable_of_sum_range_le (fun k => ?_) hA
  unfold cosinePotential
  exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))

/-- The actual infinite cosine-action identity. Its nonzero hypothesis explicitly
 excludes the spurious totalized value of `Real.log 0`. -/
theorem norm_charFun_sq_eq_exp_neg_tsum_action (β : ℝ) (hβ : 1 < β) (t : ℝ)
    (hcos : ∀ k : ℕ, Real.cos (Real.pi * (t * β⁻¹ ^ k)) ≠ 0)
    (hV : Summable (fun k : ℕ => cosinePotential (t * β⁻¹ ^ k))) :
    ‖charFun (ElementaryCore.bernoulliLaw β) (Real.pi * t)‖ ^ 2 =
      Real.exp (-(∑' k : ℕ, cosinePotential (t * β⁻¹ ^ k))) := by
  have hp := (multipliable_bernoulliCosine β hβ (Real.pi * t)).hasProd.tendsto_prod_nat
  have ha := Real.continuous_exp.continuousAt.tendsto.comp hV.hasSum.tendsto_sum_nat.neg
  have heq (n : ℕ) :
      (∏ k ∈ Finset.range n, Real.cos (Real.pi * t * β⁻¹ ^ k)) ^ 2 =
        Real.exp (-(∑ k ∈ Finset.range n, cosinePotential (t * β⁻¹ ^ k))) := by
    simpa only [mul_assoc] using cosine_prod_sq_eq_exp_neg_sum (Finset.range n)
      (fun k => t * β⁻¹ ^ k) (fun k _ => hcos k)
  have hlim : Tendsto (fun n : ℕ =>
      (∏ k ∈ Finset.range n, Real.cos (Real.pi * t * β⁻¹ ^ k)) ^ 2) atTop
      (𝓝 (Real.exp (-(∑' k : ℕ, cosinePotential (t * β⁻¹ ^ k))))) := by
    simpa only [heq, Function.comp_def] using ha
  have hval := tendsto_nhds_unique (hp.pow 2) hlim
  rw [charFun_bernoulliLaw_eq_tprod β hβ (Real.pi * t)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hval

/-- Integer translation preserves the squared cosine appearing in the action. -/
theorem cos_pi_sq_add_int (u : ℝ) (m : ℤ) :
    Real.cos (Real.pi * (u + m)) ^ 2 = Real.cos (Real.pi * u) ^ 2 := by
  have hz := Real.cos_add_int_mul_two_pi (2 * (Real.pi * u)) m
  have heq : 2 * (Real.pi * (u + m)) = 2 * (Real.pi * u) + m * (2 * Real.pi) := by ring
  rw [← heq] at hz
  nlinarith [Real.cos_two_mul (Real.pi * (u + m)), Real.cos_two_mul (Real.pi * u)]

/-- The real potential is genuinely integer-periodic, including its totalized values. -/
theorem cosinePotential_add_int (u : ℝ) (m : ℤ) :
    cosinePotential (u + m) = cosinePotential u := by
  unfold cosinePotential
  rw [cos_pi_sq_add_int]

/-- A strictly centered coordinate cannot hit a zero of its cosine. -/
theorem cos_pi_ne_zero_of_abs_lt_half (u : ℝ) (hu : |u| < (1 / 2 : ℝ)) :
    Real.cos (Real.pi * u) ≠ 0 := by
  have hc : 0 < Real.cos (Real.pi * u) := by
    apply Real.cos_pos_of_mem_Ioo
    have h := abs_lt.mp hu
    constructor <;> nlinarith [Real.pi_pos]
  exact ne_of_gt hc

/-- Integer congruence transfers a centered trajectory's actual finite action
 bound to the Fourier coefficient of the true Bernoulli-series law. -/
theorem exp_neg_centeredAction_le_norm_charFun_sq (β : ℝ) (hβ : 1 < β)
    (t A : ℝ) (y : ℕ → ℝ)
    (hcong : ∀ k : ℕ, ∃ m : ℤ, t * β⁻¹ ^ k = y k + m)
    (hcenter : ∀ k : ℕ, |y k| < (1 / 2 : ℝ))
    (hA : ∀ n : ℕ, (∑ k ∈ Finset.range n, cosinePotential (y k)) ≤ A) :
    Real.exp (-A) ≤ ‖charFun (ElementaryCore.bernoulliLaw β) (Real.pi * t)‖ ^ 2 := by
  have hs (k : ℕ) : Real.cos (Real.pi * (t * β⁻¹ ^ k)) ^ 2 =
      Real.cos (Real.pi * y k) ^ 2 := by
    obtain ⟨m, hm⟩ := hcong k
    rw [hm, cos_pi_sq_add_int]
  have hV (k : ℕ) : cosinePotential (t * β⁻¹ ^ k) = cosinePotential (y k) := by
    unfold cosinePotential
    rw [hs k]
  apply exp_neg_action_le_norm_charFun_sq β hβ t A
  · intro k hk
    have hsq := hs k
    rw [hk, zero_pow (by norm_num : 2 ≠ 0)] at hsq
    exact (pow_ne_zero 2 (cos_pi_ne_zero_of_abs_lt_half (y k) (hcenter k))) hsq.symm
  · intro n
    simpa only [hV] using hA n

end Salem
