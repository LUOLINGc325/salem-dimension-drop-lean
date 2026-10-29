module

public import Mathlib
public import Mathlib.Probability.ProductMeasure

@[expose] public section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set Filter Topology

namespace Salem.ElementaryCore

/-- Symmetric law of one real sign. -/
noncomputable def signMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure signMeasure := by
  constructor
  rw [signMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _)]
  simpa [smul_eq_mul, one_div] using ENNReal.inv_two_add_inv_two

/-- Infinite iid real sign process. -/
noncomputable def signProcess : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => signMeasure)

instance : IsProbabilityMeasure signProcess := by
  dsimp [signProcess]
  infer_instance

/-- Pointwise sum of the real sign series. -/
noncomputable def bernoulliSeries (β : ℝ) : (ℕ → ℝ) → ℝ :=
  fun ω => ∑' k : ℕ, ω k * β⁻¹ ^ k

lemma measurable_bernoulliSeries (β : ℝ) : Measurable (bernoulliSeries β) := by
  unfold bernoulliSeries
  apply Measurable.tsum
  intro k
  fun_prop

/-- The explicitly constructed sign-series law. -/
noncomputable def bernoulliLaw (β : ℝ) : Measure ℝ :=
  Measure.map (bernoulliSeries β) signProcess

/-- Almost every coordinate of the iid sign process has absolute value one. -/
theorem ae_signProcess_abs_one : ∀ᵐ ω ∂signProcess, ∀ n : ℕ, |ω n| = 1 := by
  apply ae_all_iff.2
  intro n
  have hs : ∀ᵐ x ∂signMeasure, |x| = 1 := by
    simp [signMeasure, ae_add_measure_iff]
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => signMeasure) n).quasiMeasurePreserving.ae hs

/-- The actual pointwise digit series converges whenever all digits are signs. -/
theorem summable_bernoulliSeries_of_signs (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
    (hω : ∀ n, |ω n| = 1) : Summable (fun k => ω k * β⁻¹ ^ k) := by
  have hb : |β⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one hβ))]
    exact inv_lt_one_of_one_lt₀ hβ
  apply Summable.of_norm
  convert (summable_geometric_of_abs_lt_one hb) using 1
  ext k
  rw [norm_mul, Real.norm_eq_abs, hω k, one_mul]
  simp [abs_of_pos (lt_trans zero_lt_one hβ)]

/-- Uniform geometric bound for every sign sequence. -/
theorem abs_bernoulliSeries_le (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
    (hω : ∀ n, |ω n| = 1) : |bernoulliSeries β ω| ≤ (1 - β⁻¹)⁻¹ := by
  have hq : 0 < β⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hβ)
  have hb : |β⁻¹| < 1 := by
    rw [abs_of_pos hq]
    exact inv_lt_one_of_one_lt₀ hβ
  have hnorm : (fun k => ‖ω k * β⁻¹ ^ k‖) = (fun k : ℕ => β⁻¹ ^ k) := by
    ext k
    rw [norm_mul, Real.norm_eq_abs, hω k, one_mul]
    simp [abs_of_pos (lt_trans zero_lt_one hβ)]
  calc
    |bernoulliSeries β ω| ≤ ∑' k, ‖ω k * β⁻¹ ^ k‖ :=
      norm_tsum_le_tsum_norm (by rw [hnorm]; exact summable_geometric_of_abs_lt_one hb)
    _ = (1 - β⁻¹)⁻¹ := by rw [hnorm, tsum_geometric_of_abs_lt_one hb]

/-- The remainder after the first `n` digits is a scaled copy of a sign series. -/
theorem bernoulliSeries_sub_partialSum (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
    (hω : ∀ k, |ω k| = 1) (n : ℕ) :
    bernoulliSeries β ω - ∑ k ∈ Finset.range n, ω k * β⁻¹ ^ k =
      β⁻¹ ^ n * bernoulliSeries β (fun k => ω (k+n)) := by
  have hs := summable_bernoulliSeries_of_signs β hβ ω hω
  have heq : bernoulliSeries β ω = (∑ k ∈ Finset.range n, ω k * β⁻¹ ^ k) +
      β⁻¹ ^ n * bernoulliSeries β (fun k => ω (k+n)) := by
    unfold bernoulliSeries
    rw [← hs.sum_add_tsum_nat_add n]
    congr 1
    rw [← tsum_mul_left]
    congr 1
    ext k
    rw [pow_add]
    ring
  linarith

/-- Every cylinder of length `n` maps into a closed interval of geometric radius. -/
theorem abs_bernoulliSeries_sub_partialSum_le (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
    (hω : ∀ k, |ω k| = 1) (n : ℕ) :
    |bernoulliSeries β ω - ∑ k ∈ Finset.range n, ω k * β⁻¹ ^ k| ≤
      (1 - β⁻¹)⁻¹ * β⁻¹ ^ n := by
  rw [bernoulliSeries_sub_partialSum β hβ ω hω n, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ β)) n)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (abs_bernoulliSeries_le β hβ (fun k => ω (k+n)) (fun k => hω (k+n)))
    (pow_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ β)) n)

/-- The two real digits parametrized by a Boolean. -/
def signDigit (b : Bool) : ℝ := if b then 1 else -1

/-- Prefix sums, before merging coincident values. -/
noncomputable def signPrefix (β : ℝ) (n : ℕ) (v : Fin n → Bool) : ℝ :=
  ∑ k : Fin n, signDigit (v k) * β⁻¹ ^ (k : ℕ)

/-- Geometric cylinder interval for a prefix. -/
noncomputable def signCylinder (β : ℝ) (n : ℕ) (v : Fin n → Bool) : Set ℝ :=
  Icc (signPrefix β n v - (1 - β⁻¹)⁻¹ * β⁻¹ ^ n)
      (signPrefix β n v + (1 - β⁻¹)⁻¹ * β⁻¹ ^ n)

/-- The Borel digit attractor obtained from all finite cylinder covers. -/
noncomputable def signAttractor (β : ℝ) : Set ℝ :=
  ⋂ n : ℕ, ⋃ v : Fin n → Bool, signCylinder β n v

theorem measurableSet_signAttractor (β : ℝ) : MeasurableSet (signAttractor β) := by
  apply MeasurableSet.iInter
  intro n
  exact MeasurableSet.iUnion (fun _ => measurableSet_Icc)

theorem bernoulliSeries_mem_signAttractor (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
    (hω : ∀ k, |ω k| = 1) : bernoulliSeries β ω ∈ signAttractor β := by
  classical
  apply Set.mem_iInter.2
  intro n
  let v : Fin n → Bool := fun k => decide (ω k = 1)
  have hv (k : Fin n) : signDigit (v k) = ω k := by
    have hk := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 (hω k)
    rcases hk with hk | hk
    · norm_num [signDigit, v, hk]
    · norm_num [signDigit, v, hk]
  have hp : signPrefix β n v = ∑ k ∈ Finset.range n, ω k * β⁻¹ ^ k := by
    unfold signPrefix
    simp_rw [hv]
    exact Fin.sum_univ_eq_sum_range (fun k => ω k * β⁻¹ ^ k) n
  apply Set.mem_iUnion.2 ⟨v, ?_⟩
  change bernoulliSeries β ω ∈ Icc _ _
  have ht := abs_bernoulliSeries_sub_partialSum_le β hβ ω hω n
  rw [← hp, abs_le] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem bernoulliLaw_signAttractor (β : ℝ) (hβ : 1 < β) :
    bernoulliLaw β (signAttractor β) = 1 := by
  rw [bernoulliLaw,
    Measure.map_apply (measurable_bernoulliSeries β) (measurableSet_signAttractor β)]
  apply (mem_ae_iff_prob_eq_one ((measurableSet_signAttractor β).preimage
    (measurable_bernoulliSeries β))).1
  filter_upwards [ae_signProcess_abs_one] with ω hω
  exact bernoulliSeries_mem_signAttractor β hβ ω hω

/-- Each cylinder has its asserted geometric diameter, including before separation. -/
theorem ediam_signCylinder (β : ℝ) (n : ℕ) (v : Fin n → Bool) :
    Metric.ediam (signCylinder β n v) =
      ENNReal.ofReal (2 * (1 - β⁻¹)⁻¹ * β⁻¹ ^ n) := by
  unfold signCylinder
  rw [Real.ediam_Icc]
  congr 1
  ring

/-- At the similarity dimension, the number of cylinders exactly cancels shrinkage. -/
theorem inv_rpow_similarityDimension (β : ℝ) (hβ : 1 < β) :
    (β⁻¹ : ℝ) ^ (Real.log 2 / Real.log β) = (2 : ℝ)⁻¹ := by
  rw [Real.rpow_def_of_pos (inv_pos.mpr (by linarith)), Real.log_inv]
  have hlog : Real.log β ≠ 0 := ne_of_gt (Real.log_pos hβ)
  have heq : -Real.log β * (Real.log 2 / Real.log β) = -Real.log 2 := by
    field_simp
  rw [heq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Uniform finite Hausdorff cost of all prefix cylinders at the critical exponent. -/
theorem signCylinder_hausdorffCost_le (β : ℝ) (hβ : 1 < β) (n : ℕ) :
    (∑ v : Fin n → Bool, Metric.ediam (signCylinder β n v) ^
      (Real.log 2 / Real.log β)) ≤
        ENNReal.ofReal (2 * (1 - β⁻¹)⁻¹) ^ (Real.log 2 / Real.log β) := by
  have hq : 0 < β⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  have hd : 0 ≤ Real.log 2 / Real.log β := div_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg hβ.le)
  have hC : 0 ≤ 2 * (1 - β⁻¹)⁻¹ := by positivity
  have hqp : ENNReal.ofReal β⁻¹ ^ (Real.log 2 / Real.log β) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_rpow_of_pos hq, inv_rpow_similarityDimension β hβ]
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simp_rw [ediam_signCylinder, ENNReal.ofReal_mul hC,
    ENNReal.ofReal_pow hq.le, ENNReal.mul_rpow_of_nonneg _ _ hd,
    ← ENNReal.rpow_natCast_mul, mul_comm (n : ℝ), ENNReal.rpow_mul_natCast, hqp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hcancel : (2 : ℝ≥0∞)^n * ((2 : ℝ≥0∞)⁻¹)^n = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_pow]
  calc
    _ = (ENNReal.ofReal (2 * (1 - β⁻¹)⁻¹) ^ (Real.log 2 / Real.log β)) *
        ((2 : ℝ≥0∞)^n * ((2 : ℝ≥0∞)⁻¹)^n) := by ring
    _ ≤ _ := by rw [hcancel, mul_one]

/-- The digit attractor has at most its similarity dimension. -/
theorem dimH_signAttractor_le (β : ℝ) (hβ : 1 < β) :
    dimH (signAttractor β) ≤ ENNReal.ofReal (Real.log 2 / Real.log β) := by
  have hq : 0 < β⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  have hd : 0 ≤ Real.log 2 / Real.log β := div_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg hβ.le)
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (1 - β⁻¹)⁻¹ * β⁻¹ ^ n))
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul
      (2 * (1 - β⁻¹)⁻¹))
    simpa using h
  have hH := Measure.hausdorffMeasure_le_liminf_sum (Real.log 2 / Real.log β)
    (signAttractor β) (fun n : ℕ => ENNReal.ofReal (2 * (1 - β⁻¹)⁻¹ * β⁻¹ ^ n)) hr
    (fun n v => signCylinder β n v)
    (Filter.Eventually.of_forall (fun n v => (ediam_signCylinder β n v).le))
    (Filter.Eventually.of_forall (fun n => Set.iInter_subset (fun m =>
      ⋃ v : Fin m → Bool, signCylinder β m v) n))
  have hcost : liminf (fun n : ℕ => ∑ v : Fin n → Bool,
      Metric.ediam (signCylinder β n v) ^ (Real.log 2 / Real.log β)) atTop ≤
      ENNReal.ofReal (2 * (1 - β⁻¹)⁻¹) ^ (Real.log 2 / Real.log β) := by
    simpa only [liminf_const] using Filter.liminf_le_liminf (f := atTop)
      (Filter.Eventually.of_forall (fun n => signCylinder_hausdorffCost_le β hβ n))
  have hfin : Measure.hausdorffMeasure (Real.log 2 / Real.log β) (signAttractor β) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt (hH.trans hcost)
      (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.ofReal_ne_top))
  have hdim := dimH_le_of_hausdorffMeasure_ne_top
    (d := ⟨Real.log 2 / Real.log β, hd⟩) hfin
  convert hdim using 1
  exact ENNReal.ofReal_eq_coe_nnreal hd


end Salem.ElementaryCore

namespace Salem

/-- The explicit iid Bernoulli series law has a Borel full-mass set whose Hausdorff
 dimension is at most `log 2 / log β`. This statement has no project dependencies. -/
theorem explicit_bernoulliSeries_fullMass_dim_bound (β : ℝ) (hβ : 1 < β) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.map (fun ω : ℕ → ℝ => ∑' k : ℕ, ω k * β⁻¹ ^ k)
        (Measure.infinitePi (fun _ : ℕ =>
          (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
            (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)))) F = 1 ∧
      dimH F ≤ ENNReal.ofReal (Real.log 2 / Real.log β) := by
  exact ⟨ElementaryCore.signAttractor β, ElementaryCore.measurableSet_signAttractor β,
    ElementaryCore.bernoulliLaw_signAttractor β hβ, ElementaryCore.dimH_signAttractor_le β hβ⟩

end Salem
