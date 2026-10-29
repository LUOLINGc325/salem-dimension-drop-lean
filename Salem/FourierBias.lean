module

public import Mathlib

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The binary logarithmic gain in v2 Lemma `lem:entropy`. -/
noncomputable def fourierBiasGain (a : ℝ) : ℝ :=
  ((1 + a) * Real.log (1 + a) + (1 - a) * Real.log (1 - a)) / 2

/-- The logarithm of a biased factor dominates the chord between its two
endpoint values. This is the pointwise analytic step in the Fourier-bias proof. -/
theorem log_one_add_mul_ge_chord {a t : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (htlo : -1 ≤ t) (hthi : t ≤ 1) :
    (1 + t) / 2 * Real.log (1 + a) + (1 - t) / 2 * Real.log (1 - a) ≤
      Real.log (1 + a * t) := by
  have hplus : (1 + a) ∈ Set.Ioi (0 : ℝ) := by simpa using (show 0 < 1 + a by linarith)
  have hminus : (1 - a) ∈ Set.Ioi (0 : ℝ) := by simpa using (show 0 < 1 - a by linarith)
  have hweightplus : 0 ≤ (1 + t) / 2 := by linarith
  have hweightminus : 0 ≤ (1 - t) / 2 := by linarith
  have hweights : (1 + t) / 2 + (1 - t) / 2 = 1 := by ring
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hplus hminus
    hweightplus hweightminus hweights
  have harg : (1 + t) / 2 * (1 + a) + (1 - t) / 2 * (1 - a) = 1 + a * t := by ring
  simpa only [smul_eq_mul, harg] using h

/-- If a bounded observable has mean at least `a`, the expected logarithm of
its positive biased factor is at least the paper's explicit gain `Ψ(a)`. -/
theorem finite_log_bias_lower_bound {ι : Type*} [Fintype ι]
    {p t : ι → ℝ} {a : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : ∀ i, -1 ≤ t i ∧ t i ≤ 1) (hmean : a ≤ ∑ i, p i * t i) :
    fourierBiasGain a ≤ ∑ i, p i * Real.log (1 + a * t i) := by
  have hlog : Real.log (1 - a) ≤ Real.log (1 + a) :=
    Real.log_le_log (by linarith) (by linarith)
  have hchord :
      (∑ i, p i * ((1 + t i) / 2 * Real.log (1 + a) +
        (1 - t i) / 2 * Real.log (1 - a))) ≤
      ∑ i, p i * Real.log (1 + a * t i) := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (log_one_add_mul_ge_chord ha ha1 (ht i).1 (ht i).2) (hp i))
  have heq : (∑ i, p i * ((1 + t i) / 2 * Real.log (1 + a) +
      (1 - t i) / 2 * Real.log (1 - a))) =
      (Real.log (1 + a) + Real.log (1 - a)) / 2 +
        (∑ i, p i * t i) * (Real.log (1 + a) - Real.log (1 - a)) / 2 := by
    calc
      _ = ∑ i, (p i * ((Real.log (1 + a) + Real.log (1 - a)) / 2) +
          (p i * t i) * ((Real.log (1 + a) - Real.log (1 - a)) / 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp_sum]; ring
  rw [heq] at hchord
  have hmono := mul_le_mul_of_nonneg_right hmean (sub_nonneg.mpr hlog)
  dsimp [fourierBiasGain]
  nlinarith [hchord, hmono]

/-- The paper's gain dominates the explicit quadratic Fourier penalty. -/
theorem half_sq_le_fourierBiasGain {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    a ^ 2 / 2 ≤ fourierBiasGain a := by
  let G : ℝ → ℝ := fun x => fourierBiasGain x - x ^ 2 / 2
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc 0 a) :
      HasDerivAt G ((Real.log (1 + x) - Real.log (1 - x)) / 2 - x) x := by
    have hplus : 1 + x ≠ 0 := by linarith [hx.1]
    have hminus : 1 - x ≠ 0 := by linarith [hx.2]
    have hp := (Real.hasDerivAt_mul_log hplus).comp x ((hasDerivAt_id x).const_add 1)
    have hm := (Real.hasDerivAt_mul_log hminus).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have hraw := ((hp.add hm).div_const 2).sub ((hasDerivAt_pow 2 x).div_const 2)
    change HasDerivAt G _ x at hraw
    convert hraw using 1; ring
  have hnonneg (x : ℝ) (hx : x ∈ Set.Icc 0 a) :
      0 ≤ (Real.log (1 + x) - Real.log (1 - x)) / 2 - x := by
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 ha1
    have hden : 0 < 1 - x := by linarith
    have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ 2 * x / (1 - x) by positivity)
    have harg : 1 + 2 * x / (1 - x) = (1 + x) / (1 - x) := by field_simp; ring
    have hval : 2 * (2 * x / (1 - x)) / (2 * x / (1 - x) + 2) = 2 * x := by
      field_simp
      ring
    rw [harg, hval, Real.log_div (by linarith : 1 + x ≠ 0) hden.ne'] at hh
    linarith
  have hmono : MonotoneOn G (Set.Icc 0 a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
    · intro x hx
      exact (hderiv x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hnonneg x (interior_subset hx)
  have hh := hmono (show (0 : ℝ) ∈ Set.Icc 0 a by simp [ha])
    (show a ∈ Set.Icc 0 a by simp [ha]) ha
  simpa [G, fourierBiasGain] using hh

/-- A lower bound on an actual finite cosine Fourier coefficient selects a
sign whose logarithmic factor has the paper's positive expected gain. -/
theorem finite_cosine_log_bias {ι : Type*} [Fintype ι]
    {p x : ι → ℝ} {a ξ : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hfourier : a ≤ |∑ i, p i * Real.cos (ξ * x i)|) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      fourierBiasGain a ≤ ∑ i, p i * Real.log (1 + a * (σ * Real.cos (ξ * x i))) := by
  let b : ℝ := ∑ i, p i * Real.cos (ξ * x i)
  change a ≤ |b| at hfourier
  by_cases hb : 0 ≤ b
  · refine ⟨1, Or.inl rfl, ?_⟩
    apply finite_log_bias_lower_bound hp hp_sum ha ha1
    · intro i
      simpa using ⟨Real.neg_one_le_cos (ξ * x i), Real.cos_le_one (ξ * x i)⟩
    · simpa only [one_mul, abs_of_nonneg hb] using hfourier
  · have hbneg : b < 0 := lt_of_not_ge hb
    refine ⟨-1, Or.inr rfl, ?_⟩
    apply finite_log_bias_lower_bound hp hp_sum ha ha1
    · intro i
      have hlo := Real.neg_one_le_cos (ξ * x i)
      have hhi := Real.cos_le_one (ξ * x i)
      constructor <;> linarith
    · have hsum : (∑ i, p i * (-1 * Real.cos (ξ * x i))) = -b := by
        simp [b, mul_neg, Finset.sum_neg_distrib]
      rw [hsum]
      simpa only [abs_of_neg hbneg] using hfourier

/-- The finite-law positive trigonometric product in v2 Lemma `lem:entropy`:
each biased Fourier coefficient contributes at least `Ψ(a)`, and hence `a²/2`,
to the actual expected logarithm of the product. -/
theorem finite_fourier_log_product_lower_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p x : ι → ℝ} {a : ℝ} (ξ : κ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hfourier : ∀ j, a ≤ |∑ i, p i * Real.cos (ξ j * x i)|) :
    ∃ σ : κ → ℝ, (∀ j, σ j = 1 ∨ σ j = -1) ∧
      (∀ i, 0 < ∏ j, (1 + a * (σ j * Real.cos (ξ j * x i)))) ∧
      (Fintype.card κ : ℝ) * fourierBiasGain a ≤
        ∑ i, p i * Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x i)))) ∧
      (Fintype.card κ : ℝ) * a ^ 2 / 2 ≤
        ∑ i, p i * Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x i)))) := by
  classical
  have hchoice (j : κ) := finite_cosine_log_bias hp hp_sum ha ha1 (hfourier j)
  choose σ hsign hgain using hchoice
  have ht (i : ι) (j : κ) :
      -1 ≤ σ j * Real.cos (ξ j * x i) ∧ σ j * Real.cos (ξ j * x i) ≤ 1 := by
    have hlo := Real.neg_one_le_cos (ξ j * x i)
    have hhi := Real.cos_le_one (ξ j * x i)
    rcases hsign j with h | h <;> rw [h] <;> constructor <;> linarith
  have hpos (i : ι) (j : κ) : 0 < 1 + a * (σ j * Real.cos (ξ j * x i)) := by
    have hh := mul_le_mul_of_nonneg_left (ht i j).1 ha
    nlinarith [hh]
  have hlog (i : ι) :
      Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x i)))) =
      ∑ j, Real.log (1 + a * (σ j * Real.cos (ξ j * x i))) :=
    Real.log_prod (fun j _ => (hpos i j).ne')
  have hbound : (Fintype.card κ : ℝ) * fourierBiasGain a ≤
      ∑ i, p i * Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x i)))) := by
    calc
      _ = ∑ _j : κ, fourierBiasGain a := by simp
      _ ≤ ∑ j, ∑ i, p i * Real.log (1 + a * (σ j * Real.cos (ξ j * x i))) :=
        Finset.sum_le_sum (fun j _ => hgain j)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [hlog, Finset.mul_sum]
  refine ⟨σ, hsign, (fun i => Finset.prod_pos (fun j _ => hpos i j)), hbound, ?_⟩
  have hh := mul_le_mul_of_nonneg_left (half_sq_le_fourierBiasGain ha ha1)
    (show (0 : ℝ) ≤ Fintype.card κ by positivity)
  nlinarith [hh, hbound]

open MeasureTheory in
/-- The logarithm of a biased bounded observable is integrable under every
finite measure. The strict bound `a < 1` keeps its argument uniformly positive. -/
theorem integrable_log_biased_observable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {t : Ω → ℝ} {a : ℝ}
    (htmeas : AEMeasurable t μ) (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : ∀ x, -1 ≤ t x ∧ t x ≤ 1) :
    Integrable (fun x => Real.log (1 + a * t x)) μ := by
  have harg (x : Ω) : 1 - a ≤ 1 + a * t x ∧ 1 + a * t x ≤ 1 + a := by
    have hl := mul_le_mul_of_nonneg_left (ht x).1 ha
    have hu := mul_le_mul_of_nonneg_left (ht x).2 ha
    constructor <;> nlinarith
  have hpos (x : Ω) : 0 < 1 + a * t x := by linarith [(harg x).1]
  have hlogs (x : Ω) :
      Real.log (1 - a) ≤ Real.log (1 + a * t x) ∧
      Real.log (1 + a * t x) ≤ Real.log (1 + a) :=
    ⟨Real.log_le_log (by linarith) (harg x).1,
      Real.log_le_log (hpos x) (harg x).2⟩
  have hlogmeas : AEMeasurable (fun x => Real.log (1 + a * t x)) μ := by fun_prop
  have hlogint : Integrable (fun x => Real.log (1 + a * t x)) μ := by
    apply (integrable_const (|Real.log (1 - a)| + |Real.log (1 + a)|)).mono'
      hlogmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hl := neg_abs_le (Real.log (1 - a))
    have hu := le_abs_self (Real.log (1 + a))
    constructor <;> linarith [(hlogs x).1, (hlogs x).2,
      abs_nonneg (Real.log (1 - a)), abs_nonneg (Real.log (1 + a))]
  exact hlogint

open MeasureTheory in
/-- The expected-log gain for a bounded observable under an actual probability
measure, as used for the infinite Bernoulli-convolution law in the paper. -/
theorem integral_log_bias_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {t : Ω → ℝ} {a : ℝ}
    (htmeas : AEMeasurable t μ) (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : ∀ x, -1 ≤ t x ∧ t x ≤ 1) (hmean : a ≤ ∫ x, t x ∂μ) :
    fourierBiasGain a ≤ ∫ x, Real.log (1 + a * t x) ∂μ := by
  have htint : Integrable t μ :=
    (integrable_const (1 : ℝ)).mono' htmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using abs_le.mpr (ht x))
  have hlogint := integrable_log_biased_observable μ htmeas ha ha1 ht
  let c₀ : ℝ := (Real.log (1 + a) + Real.log (1 - a)) / 2
  let c₁ : ℝ := (Real.log (1 + a) - Real.log (1 - a)) / 2
  have hc₁ : 0 ≤ c₁ := by
    have := Real.log_le_log (show 0 < 1 - a by linarith) (show 1 - a ≤ 1 + a by linarith)
    dsimp [c₁]
    linarith
  have hchordint : Integrable (fun x => c₀ + t x * c₁) μ :=
    (integrable_const c₀).add (htint.mul_const c₁)
  have hchord : (∫ x, c₀ + t x * c₁ ∂μ) ≤
      ∫ x, Real.log (1 + a * t x) ∂μ := by
    apply integral_mono hchordint hlogint
    intro x
    have hh := log_one_add_mul_ge_chord ha ha1 (ht x).1 (ht x).2
    dsimp [c₀, c₁]
    nlinarith [hh]
  rw [integral_add (integrable_const c₀) (htint.mul_const c₁), integral_const,
    integral_mul_const, probReal_univ, one_smul] at hchord
  have hh := mul_le_mul_of_nonneg_right hmean hc₁
  dsimp [c₀, c₁, fourierBiasGain] at *
  nlinarith [hh, hchord]

open MeasureTheory in
/-- An actual cosine Fourier coefficient of a probability measure selects the
sign used in the paper's positive trigonometric product. -/
theorem integral_cosine_log_bias (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a ξ : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hfourier : a ≤ |∫ x, Real.cos (ξ * x) ∂μ|) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      fourierBiasGain a ≤ ∫ x, Real.log (1 + a * (σ * Real.cos (ξ * x))) ∂μ := by
  let b : ℝ := ∫ x, Real.cos (ξ * x) ∂μ
  change a ≤ |b| at hfourier
  by_cases hb : 0 ≤ b
  · refine ⟨1, Or.inl rfl, ?_⟩
    apply integral_log_bias_lower_bound μ (by fun_prop) ha ha1
    · intro x
      simpa using ⟨Real.neg_one_le_cos (ξ * x), Real.cos_le_one (ξ * x)⟩
    · simpa only [one_mul, abs_of_nonneg hb] using hfourier
  · have hbneg : b < 0 := lt_of_not_ge hb
    refine ⟨-1, Or.inr rfl, ?_⟩
    apply integral_log_bias_lower_bound μ (by fun_prop) ha ha1
    · intro x
      have hlo := Real.neg_one_le_cos (ξ * x)
      have hhi := Real.cos_le_one (ξ * x)
      constructor <;> linarith
    · have heq : (∫ x, -1 * Real.cos (ξ * x) ∂μ) = -b := by
        simp only [neg_one_mul, integral_neg, b]
      rw [heq]
      simpa only [abs_of_neg hbneg] using hfourier

open MeasureTheory in
/-- The probability-measure version of the first step of v2 Lemma `lem:entropy`.
Biased cosine Fourier coefficients give a strictly positive trigonometric product
whose logarithm has expectation at least `M Ψ(a)`, hence at least `M a²/2`. -/
theorem integral_fourier_log_product_lower_bound {κ : Type*} [Fintype κ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a : ℝ} (ξ : κ → ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hfourier : ∀ j, a ≤ |∫ x, Real.cos (ξ j * x) ∂μ|) :
    ∃ σ : κ → ℝ, (∀ j, σ j = 1 ∨ σ j = -1) ∧
      (∀ x, 0 < ∏ j, (1 + a * (σ j * Real.cos (ξ j * x)))) ∧
      Integrable (fun x => Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x))))) μ ∧
      (Fintype.card κ : ℝ) * fourierBiasGain a ≤
        ∫ x, Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x)))) ∂μ ∧
      (Fintype.card κ : ℝ) * a ^ 2 / 2 ≤
        ∫ x, Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x)))) ∂μ := by
  classical
  have hchoice (j : κ) := integral_cosine_log_bias μ ha ha1 (hfourier j)
  choose σ hsign hgain using hchoice
  have ht (x : ℝ) (j : κ) :
      -1 ≤ σ j * Real.cos (ξ j * x) ∧ σ j * Real.cos (ξ j * x) ≤ 1 := by
    have hlo := Real.neg_one_le_cos (ξ j * x)
    have hhi := Real.cos_le_one (ξ j * x)
    rcases hsign j with h | h <;> rw [h] <;> constructor <;> linarith
  have hpos (x : ℝ) (j : κ) : 0 < 1 + a * (σ j * Real.cos (ξ j * x)) := by
    have hh := mul_le_mul_of_nonneg_left (ht x j).1 ha
    nlinarith [hh]
  have hlog (x : ℝ) :
      Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x)))) =
      ∑ j, Real.log (1 + a * (σ j * Real.cos (ξ j * x))) :=
    Real.log_prod (fun j _ => (hpos x j).ne')
  have hint (j : κ) : Integrable (fun x => Real.log (1 + a * (σ j * Real.cos (ξ j * x)))) μ :=
    integrable_log_biased_observable μ (by fun_prop) ha ha1 (fun x => ht x j)
  have hprodint : Integrable (fun x => Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x))))) μ := by
    simp_rw [hlog]
    exact integrable_finsetSum _ (fun j _ => hint j)
  have hbound : (Fintype.card κ : ℝ) * fourierBiasGain a ≤
      ∫ x, Real.log (∏ j, (1 + a * (σ j * Real.cos (ξ j * x)))) ∂μ := by
    calc
      _ = ∑ _j : κ, fourierBiasGain a := by simp
      _ ≤ ∑ j, ∫ x, Real.log (1 + a * (σ j * Real.cos (ξ j * x))) ∂μ :=
        Finset.sum_le_sum (fun j _ => hgain j)
      _ = _ := by
        simp_rw [hlog]
        rw [integral_finsetSum _ (fun j _ => hint j)]
  refine ⟨σ, hsign, (fun x => Finset.prod_pos (fun j _ => hpos x j)), hprodint, hbound, ?_⟩
  have hh := mul_le_mul_of_nonneg_left (half_sq_le_fourierBiasGain ha ha1)
    (show (0 : ℝ) ≤ Fintype.card κ by positivity)
  nlinarith [hh, hbound]

end Salem
