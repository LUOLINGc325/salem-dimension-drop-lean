module

public import Salem.FiniteEntropy

@[expose] public section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set Filter Topology ProbabilityTheory

namespace Salem

/-- The probability of a finite word in an iid finite-alphabet process. -/
noncomputable def wordProbability {ι : Type*} (p : ι → ℝ) (n : ℕ)
    (w : Fin n → ι) : ℝ := ∏ j, p (w j)

theorem wordProbability_nonneg {ι : Type*} {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (n : ℕ) (w : Fin n → ι) :
    0 ≤ wordProbability p n w :=
  Finset.prod_nonneg (fun _ _ => hp _)

theorem wordProbability_pos {ι : Type*} {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (n : ℕ) (w : Fin n → ι) :
    0 < wordProbability p n w :=
  Finset.prod_pos (fun _ _ => hp _)

/-- All finite-word probabilities sum to one, with no separation assumption on digits. -/
theorem sum_wordProbability {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∑ i, p i = 1) (n : ℕ) :
    ∑ w : Fin n → ι, wordProbability p n w = 1 := by
  classical
  simpa [wordProbability, hp] using (Fintype.prod_sum (fun _ : Fin n => p)).symm

/-- Typical words are specified using their actual merged atom probabilities. -/
noncomputable def typicalWords {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (H ε : ℝ) (n : ℕ) : Finset (Fin n → ι) :=
  Finset.univ.filter (fun w => Real.exp (-(n : ℝ) * (H + ε)) ≤ wordProbability p n w)

/-- The typical set has the entropy cardinality bound from v2 Lemma `lem:block`. -/
theorem card_typicalWords_le {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (H ε : ℝ) (n : ℕ) :
    ((typicalWords p H ε n).card : ℝ) ≤ Real.exp ((n : ℝ) * (H + ε)) := by
  classical
  have hsumle : ∑ w ∈ typicalWords p H ε n, wordProbability p n w ≤ 1 := by
    rw [← sum_wordProbability hsum n]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun w _ _ => wordProbability_nonneg hp n w)
  have hlow : ((typicalWords p H ε n).card : ℝ) *
      Real.exp (-(n : ℝ) * (H + ε)) ≤ 1 := by
    calc
      _ = ∑ _w ∈ typicalWords p H ε n, Real.exp (-(n : ℝ) * (H + ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ typicalWords p H ε n, wordProbability p n w := by
        apply Finset.sum_le_sum
        intro w hw
        exact (Finset.mem_filter.1 hw).2
      _ ≤ 1 := hsumle
  have heq : Real.exp (-(n : ℝ) * (H + ε)) *
      Real.exp ((n : ℝ) * (H + ε)) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [Real.exp_pos ((n : ℝ) * (H + ε))]

/-- Additivity of information for a positive finite word law. -/
theorem neg_log_wordProbability {ι : Type*} {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (n : ℕ) (w : Fin n → ι) :
    -Real.log (wordProbability p n w) = ∑ j, -Real.log (p (w j)) := by
  rw [wordProbability, Real.log_prod (fun j _ => (hp (w j)).ne')]
  simp

/-- Convergence of the empirical information implies eventual typicality. -/
theorem eventually_mem_typicalWords_of_tendsto {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {H ε : ℝ} (hε : 0 < ε)
    (ω : ℕ → ι)
    (hω : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, -Real.log (p (ω j))) / n)
      atTop (𝓝 H)) :
    ∀ᶠ n : ℕ in atTop,
      (fun j : Fin n => ω j) ∈ typicalWords p H ε n := by
  classical
  filter_upwards [hω.eventually (gt_mem_nhds (by linarith : H < H + ε)),
    eventually_gt_atTop 0] with n hn hnpos
  apply Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.2 hnpos
  have hsum : (∑ j : Fin n, -Real.log (p (ω j))) < (n : ℝ) * (H + ε) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => -Real.log (p (ω j))) n]
    exact (div_lt_iff₀ hnreal).1 hn |>.trans_eq (mul_comm _ _)
  have hlog := neg_log_wordProbability hp n (fun j : Fin n => ω j)
  have hpos := wordProbability_pos hp n (fun j : Fin n => ω j)
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  linarith

/-- The one-coordinate information has exactly the actual finite Shannon mean. -/
theorem integral_information_eq_finiteEntropy {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsFiniteMeasure ν] (p : ι → ℝ)
    (hmass : ∀ i, ν.real {i} = p i) :
    (∫ i, -Real.log (p i) ∂ν) = finiteEntropy p := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro i _
  rw [hmass]
  simp [Real.negMulLog, smul_eq_mul]

/-- The strong law for information of an actual finite-alphabet iid product law. -/
theorem ae_information_average_tendsto {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (p : ι → ℝ)
    (hmass : ∀ i, ν.real {i} = p i) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, -Real.log (p (ω j))) / n)
        atTop (𝓝 (finiteEntropy p)) := by
  let f : ι → ℝ := fun i => -Real.log (p i)
  have hf : Measurable f := measurable_of_countable f
  have heval (j : ℕ) := measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j
  have hindep := iIndepFun_infinitePi (P := fun _ : ℕ => ν)
    (X := fun _ : ℕ => f) (fun _ => hf)
  have hident (j : ℕ) : IdentDistrib (fun ω : ℕ → ι => f (ω j))
      (fun ω : ℕ → ι => f (ω 0))
      (Measure.infinitePi (fun _ : ℕ => ν)) (Measure.infinitePi (fun _ : ℕ => ν)) :=
    ((heval j).hasLaw.identDistrib (heval 0).hasLaw).comp hf
  have hmean : (∫ ω : ℕ → ι, f (ω 0) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      finiteEntropy p := by
    have hid : IdentDistrib (fun ω : ℕ → ι => f (ω 0)) f
        (Measure.infinitePi (fun _ : ℕ => ν)) ν :=
      ((heval 0).hasLaw.identDistrib (HasLaw.id (μ := ν))).comp hf
    exact hid.integral_eq.trans (integral_information_eq_finiteEntropy ν p hmass)
  have hs := strong_law_ae_real (fun j (ω : ℕ → ι) => f (ω j))
    ((heval 0).integrable_comp_of_integrable (Integrable.of_finite (f := f)))
    (fun _ _ h => hindep.indepFun h) hident
  simpa only [hmean] using hs

/-- Almost every iid sequence has typical prefixes at all sufficiently large lengths. -/
theorem ae_eventually_mem_typicalWords {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∀ i, ν.real {i} = p i)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ν),
      ∀ᶠ n : ℕ in atTop,
        (fun j : Fin n => ω j) ∈ typicalWords p (finiteEntropy p) ε n := by
  filter_upwards [ae_information_average_tendsto ν p hmass] with ω hω
  exact eventually_mem_typicalWords_of_tendsto hp hε ω hω

/-- The critical Hausdorff cost cancels exponential word growth against geometric shrinkage. -/
theorem entropy_critical_cost {a K q : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hq : 0 < q) (hq1 : q < 1) (n : ℕ) :
    ENNReal.ofReal (Real.exp ((n : ℝ) * a)) *
        ENNReal.ofReal (K * q ^ n) ^ (a / (-Real.log q)) =
      ENNReal.ofReal K ^ (a / (-Real.log q)) := by
  have hl : 0 < -Real.log q := neg_pos.2 (Real.log_neg hq hq1)
  have hd : 0 ≤ a / (-Real.log q) := div_nonneg ha hl.le
  have hqp : ENNReal.ofReal q ^ (a / (-Real.log q)) =
      ENNReal.ofReal (Real.exp (-a)) := by
    rw [ENNReal.ofReal_rpow_of_pos hq, Real.rpow_def_of_pos hq]
    congr 2
    field_simp [ne_of_lt (Real.log_neg hq hq1)]
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_pow hq.le,
    ENNReal.mul_rpow_of_nonneg _ _ hd,
    ← ENNReal.rpow_natCast_mul]
  rw [mul_comm (n : ℝ) (a / (-Real.log q)), ENNReal.rpow_mul_natCast, hqp,
    Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_nonneg _)]
  have hcancel : ENNReal.ofReal (Real.exp a) ^ n *
      ENNReal.ofReal (Real.exp (-a)) ^ n = 1 := by
    rw [← mul_pow, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp
  calc
    _ = ENNReal.ofReal K ^ (a / (-Real.log q)) *
        (ENNReal.ofReal (Real.exp a) ^ n * ENNReal.ofReal (Real.exp (-a)) ^ n) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- Points lying in a finite cover at every sufficiently large scale. -/
def eventualCover {κ : ℕ → Type*} (C : (n : ℕ) → κ n → Set ℝ) : Set ℝ :=
  ⋃ k : ℕ, ⋂ n : ℕ, ⋂ (_ : k ≤ n), ⋃ i : κ n, C n i

theorem measurableSet_eventualCover {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (C : (n : ℕ) → κ n → Set ℝ) (hC : ∀ n i, MeasurableSet (C n i)) :
    MeasurableSet (eventualCover C) := by
  exact MeasurableSet.iUnion (fun _ => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => MeasurableSet.iUnion (hC _))))

/-- Finite covers with entropy growth and geometric diameters give the critical dimension bound. -/
theorem dimH_eventualCover_le {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (C : (n : ℕ) → κ n → Set ℝ) {a K q : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hq : 0 < q) (hq1 : q < 1)
    (hcard : ∀ n, (Fintype.card (κ n) : ℝ) ≤ Real.exp ((n : ℝ) * a))
    (hdiam : ∀ n i, Metric.ediam (C n i) ≤ ENNReal.ofReal (K * q ^ n)) :
    dimH (eventualCover C) ≤ ENNReal.ofReal (a / (-Real.log q)) := by
  have hd : 0 ≤ a / (-Real.log q) :=
    div_nonneg ha (neg_pos.2 (Real.log_neg hq hq1)).le
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (K * q ^ n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul K)
  have hcost (n : ℕ) :
      (∑ i : κ n, Metric.ediam (C n i) ^ (a / (-Real.log q))) ≤
        ENNReal.ofReal K ^ (a / (-Real.log q)) := by
    calc
      _ ≤ ∑ _i : κ n, ENNReal.ofReal (K * q ^ n) ^ (a / (-Real.log q)) :=
        Finset.sum_le_sum (fun i _ => ENNReal.rpow_le_rpow (hdiam n i) hd)
      _ = (Fintype.card (κ n) : ℝ≥0∞) *
          ENNReal.ofReal (K * q ^ n) ^ (a / (-Real.log q)) := by simp
      _ ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * a)) *
          ENNReal.ofReal (K * q ^ n) ^ (a / (-Real.log q)) := by
        apply mul_le_mul_left
        exact_mod_cast ENNReal.ofReal_le_ofReal (hcard n)
      _ = _ := entropy_critical_cost ha hK hq hq1 n
  unfold eventualCover
  rw [dimH_iUnion]
  apply iSup_le
  intro k
  have hcover : ∀ᶠ n : ℕ in atTop,
      (⋂ m : ℕ, ⋂ (_ : k ≤ m), ⋃ i : κ m, C m i) ⊆ ⋃ i : κ n, C n i := by
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (Set.iInter_subset _ n).trans (Set.iInter_subset _ hn)
  have hH := Measure.hausdorffMeasure_le_liminf_sum (a / (-Real.log q))
    (⋂ m : ℕ, ⋂ (_ : k ≤ m), ⋃ i : κ m, C m i)
    (fun n : ℕ => ENNReal.ofReal (K * q ^ n)) hr C
    (Filter.Eventually.of_forall hdiam) hcover
  have hcost' : liminf (fun n : ℕ => ∑ i : κ n,
      Metric.ediam (C n i) ^ (a / (-Real.log q))) atTop ≤
      ENNReal.ofReal K ^ (a / (-Real.log q)) := by
    simpa only [liminf_const] using Filter.liminf_le_liminf (f := atTop)
      (Filter.Eventually.of_forall hcost)
  have hfin : Measure.hausdorffMeasure (a / (-Real.log q))
      (⋂ m : ℕ, ⋂ (_ : k ≤ m), ⋃ i : κ m, C m i) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (hH.trans hcost')
      (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.ofReal_ne_top))
  have hdim := dimH_le_of_hausdorffMeasure_ne_top (d := ⟨a / (-Real.log q), hd⟩) hfin
  convert hdim using 1
  exact ENNReal.ofReal_eq_coe_nnreal hd

/-- The actual cylinder interval of a finite word. -/
def entropyCylinder {ι : Type*} (c : (n : ℕ) → (Fin n → ι) → ℝ)
    (K q : ℝ) (n : ℕ) (w : Fin n → ι) : Set ℝ :=
  Icc (c n w - K * q ^ n) (c n w + K * q ^ n)

theorem ediam_entropyCylinder {ι : Type*}
    (c : (n : ℕ) → (Fin n → ι) → ℝ) (K q : ℝ) (n : ℕ) (w : Fin n → ι) :
    Metric.ediam (entropyCylinder c K q n w) = ENNReal.ofReal (2 * K * q ^ n) := by
  rw [entropyCylinder, Real.ediam_Icc]
  congr 1
  ring

/-- The eventual cover made from typical words and their actual cylinder intervals. -/
noncomputable def entropyTypicalCover {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (H ε : ℝ) (c : (n : ℕ) → (Fin n → ι) → ℝ) (K q : ℝ) : Set ℝ :=
  eventualCover (fun n (w : typicalWords p H ε n) => entropyCylinder c K q n w)

theorem measurableSet_entropyTypicalCover {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (H ε : ℝ) (c : (n : ℕ) → (Fin n → ι) → ℝ) (K q : ℝ) :
    MeasurableSet (entropyTypicalCover p H ε c K q) := by
  apply measurableSet_eventualCover
  intro n w
  exact measurableSet_Icc

theorem finiteEntropy_nonneg_of_probability {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    0 ≤ finiteEntropy p := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hp i)
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

/-- The Hausdorff dimension of the typical-cylinder construction at any positive error. -/
theorem dimH_entropyTypicalCover_le {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {ε K q : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (hq : 0 < q) (hq1 : q < 1)
    (c : (n : ℕ) → (Fin n → ι) → ℝ) :
    dimH (entropyTypicalCover p (finiteEntropy p) ε c K q) ≤
      ENNReal.ofReal ((finiteEntropy p + ε) / (-Real.log q)) := by
  apply dimH_eventualCover_le (K := 2 * K) (q := q) _
    (by linarith [finiteEntropy_nonneg_of_probability hp hsum])
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK) hq hq1
  · intro n
    simpa only [Fintype.card_coe] using card_typicalWords_le hp hsum (finiteEntropy p) ε n
  · intro n w
    exact (ediam_entropyCylinder c K q n w).le

/-- The iid series map lies in the typical interval cover almost surely. -/
theorem map_entropyTypicalCover_eq_one {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∀ i, ν.real {i} = p i)
    (S : (ℕ → ι) → ℝ) (hS : Measurable S)
    (c : (n : ℕ) → (Fin n → ι) → ℝ) (K q : ℝ)
    (happrox : ∀ ω n, |S ω - c n (fun j : Fin n => ω j)| ≤ K * q ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map S
      (entropyTypicalCover p (finiteEntropy p) ε c K q) = 1 := by
  rw [Measure.map_apply hS (measurableSet_entropyTypicalCover _ _ _ _ _ _)]
  apply (mem_ae_iff_prob_eq_one ((measurableSet_entropyTypicalCover _ _ _ _ _ _).preimage hS)).1
  filter_upwards [ae_eventually_mem_typicalWords ν p hp hmass hε] with ω hω
  rcases eventually_atTop.1 hω with ⟨k, hk⟩
  apply Set.mem_iUnion.2 ⟨k, ?_⟩
  apply Set.mem_iInter.2
  intro n
  apply Set.mem_iInter.2
  intro hn
  apply Set.mem_iUnion.2 ⟨⟨fun j : Fin n => ω j, hk n hn⟩, ?_⟩
  change S ω ∈ Icc _ _
  have ht := abs_le.1 (happrox ω n)
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Intersecting the countably many positive-error covers attains the exact entropy dimension. -/
theorem exists_full_mass_entropy_cover_of_cylinder_approximation
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∀ i, ν.real {i} = p i)
    (S : (ℕ → ι) → ℝ) (hS : Measurable S)
    (c : (n : ℕ) → (Fin n → ι) → ℝ) {K q : ℝ}
    (hK : 0 ≤ K) (hq : 0 < q) (hq1 : q < 1)
    (happrox : ∀ ω n, |S ω - c n (fun j : Fin n => ω j)| ≤ K * q ^ n) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.infinitePi (fun _ : ℕ => ν)).map S F = 1 ∧
      dimH F ≤ ENNReal.ofReal (finiteEntropy p / (-Real.log q)) := by
  have hsum : ∑ i, p i = 1 := by
    simpa only [hmass, Finset.coe_univ, probReal_univ] using
      (sum_measureReal_singleton (μ := ν) (Finset.univ : Finset ι))
  let E (k : ℕ) := entropyTypicalCover p (finiteEntropy p) (1 / ((k : ℝ) + 1)) c K q
  have hEmeas (k : ℕ) : MeasurableSet (E k) :=
    measurableSet_entropyTypicalCover _ _ _ _ _ _
  have hEone (k : ℕ) :
      (Measure.infinitePi (fun _ : ℕ => ν)).map S (E k) = 1 :=
    map_entropyTypicalCover_eq_one ν p hp hmass S hS c K q happrox (by positivity)
  let F := ⋂ k : ℕ, E k
  have hFmeas : MeasurableSet F := MeasurableSet.iInter hEmeas
  refine ⟨F, hFmeas, ?_, ?_⟩
  · apply (mem_ae_iff_prob_eq_one hFmeas).1
    have hall := ae_all_iff.2 (fun k => (mem_ae_iff_prob_eq_one (hEmeas k)).2 (hEone k))
    exact hall.mono (fun _ hx => Set.mem_iInter.2 hx)
  · have hbound (k : ℕ) : dimH F ≤
        ENNReal.ofReal ((finiteEntropy p + 1 / ((k : ℝ) + 1)) / (-Real.log q)) :=
      (dimH_mono (Set.iInter_subset E k)).trans
        (dimH_entropyTypicalCover_le (fun i => (hp i).le) hsum (by positivity) hK hq hq1 c)
    have ht : Tendsto (fun k : ℕ =>
        ENNReal.ofReal ((finiteEntropy p + 1 / ((k : ℝ) + 1)) / (-Real.log q)))
        atTop (𝓝 (ENNReal.ofReal (finiteEntropy p / (-Real.log q)))) := by
      apply ENNReal.tendsto_ofReal
      simpa using (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const (-Real.log q)
    exact ge_of_tendsto' ht hbound

/-- A concrete finite bound for all digit values. -/
noncomputable def alphabetBound {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ :=
  ∑ i, |b i|

theorem alphabetBound_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ alphabetBound b := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem abs_le_alphabetBound {ι : Type*} [Fintype ι] (b : ι → ℝ) (i : ι) :
    |b i| ≤ alphabetBound b := by
  exact Finset.single_le_sum (f := fun j => |b j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- The actual pointwise geometric digit series for a finite alphabet. -/
noncomputable def alphabetSeries {ι : Type*} (b : ι → ℝ) (q : ℝ) (ω : ℕ → ι) : ℝ :=
  ∑' j : ℕ, b (ω j) * q ^ j

noncomputable def alphabetPrefix {ι : Type*} (b : ι → ℝ) (q : ℝ)
    (n : ℕ) (w : Fin n → ι) : ℝ :=
  ∑ j : Fin n, b (w j) * q ^ (j : ℕ)

theorem norm_alphabet_term_le {ι : Type*} [Fintype ι] (b : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (ω : ℕ → ι) (j : ℕ) :
    ‖b (ω j) * q ^ j‖ ≤ alphabetBound b * q ^ j := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq j)]
  exact mul_le_mul_of_nonneg_right (abs_le_alphabetBound b (ω j)) (pow_nonneg hq j)

theorem summable_alphabetSeries {ι : Type*} [Fintype ι] (b : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (ω : ℕ → ι) :
    Summable (fun j : ℕ => b (ω j) * q ^ j) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hq hq1).mul_left (alphabetBound b))
    (norm_alphabet_term_le b hq ω)

theorem abs_alphabetSeries_le {ι : Type*} [Fintype ι] (b : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (ω : ℕ → ι) :
    |alphabetSeries b q ω| ≤ alphabetBound b * (1 - q)⁻¹ :=
  tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq hq1).mul_left (alphabetBound b))
    (norm_alphabet_term_le b hq ω)

/-- Every finite-alphabet cylinder is contained in its explicit geometric interval. -/
theorem abs_alphabetSeries_sub_prefix_le {ι : Type*} [Fintype ι] (b : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (ω : ℕ → ι) (n : ℕ) :
    |alphabetSeries b q ω - alphabetPrefix b q n (fun j : Fin n => ω j)| ≤
      (alphabetBound b * (1 - q)⁻¹) * q ^ n := by
  have hs := summable_alphabetSeries b hq hq1 ω
  have heq : alphabetSeries b q ω = alphabetPrefix b q n (fun j : Fin n => ω j) +
      q ^ n * alphabetSeries b q (fun j => ω (j + n)) := by
    rw [alphabetPrefix, Fin.sum_univ_eq_sum_range (fun j => b (ω j) * q ^ j) n]
    unfold alphabetSeries
    rw [← hs.sum_add_tsum_nat_add n]
    congr 1
    rw [← tsum_mul_left]
    congr 1
    ext j
    rw [pow_add]
    ring
  have ht : alphabetSeries b q ω - alphabetPrefix b q n (fun j : Fin n => ω j) =
      q ^ n * alphabetSeries b q (fun j => ω (j + n)) := by linarith
  rw [ht, abs_mul, abs_of_nonneg (pow_nonneg hq n)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (abs_alphabetSeries_le b hq hq1 (fun j => ω (j + n))) (pow_nonneg hq n)

theorem measurable_alphabetSeries {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (b : ι → ℝ) (q : ℝ) :
    Measurable (alphabetSeries b q) := by
  unfold alphabetSeries
  refine Measurable.tsum (X := ℕ → ι) (E := ℝ) (ι := ℕ)
    (L := SummationFilter.unconditional ℕ) (f := fun j ω => b (ω j) * q ^ j) ?_
  intro j
  exact ((measurable_of_countable b).comp (measurable_pi_apply j)).mul_const _

/-- Actual finite-alphabet iid geometric series have a Borel full-mass set of entropy dimension.
All masses are the singleton probabilities of the supplied finite law; the cover is constructed. -/
theorem exists_full_mass_alphabetSeries_entropy_cover
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∀ i, ν.real {i} = p i)
    (b : ι → ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries b q) F = 1 ∧
      dimH F ≤ ENNReal.ofReal (finiteEntropy p / (-Real.log q)) := by
  apply exists_full_mass_entropy_cover_of_cylinder_approximation
    (K := alphabetBound b * (1 - q)⁻¹) ν p hp hmass
    (alphabetSeries b q) (measurable_alphabetSeries b q) (alphabetPrefix b q)
    (mul_nonneg (alphabetBound_nonneg b) (inv_nonneg.2 (by linarith))) hq hq1
  exact abs_alphabetSeries_sub_prefix_le b hq.le hq1

/-- A finite pushforward atom has exactly the sum of the probabilities of its merged preimages. -/
theorem finite_map_singleton_probability {α ι : Type*} [Fintype α] [DecidableEq ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure α) [IsFiniteMeasure ν] (f : α → ι) (i : ι) :
    (ν.map f).real {i} = ∑ a, if f a = i then ν.real {a} else 0 := by
  classical
  rw [map_measureReal_apply (measurable_of_countable f) (measurableSet_singleton i)]
  have hset : (↑(Finset.univ.filter (fun a : α => f a = i)) : Set α) = f ⁻¹' {i} := by
    ext a
    simp
  rw [← hset, ← sum_measureReal_singleton, Finset.sum_filter]

/-- A surjective merging of strictly positive finite atoms retains strict positivity. -/
theorem finite_map_singleton_probability_pos {α ι : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure α) [IsFiniteMeasure ν] (hν : ∀ a, 0 < ν.real {a})
    (f : α → ι) (hf : Function.Surjective f) (i : ι) :
    0 < (ν.map f).real {i} := by
  rcases hf i with ⟨a, ha⟩
  rw [map_measureReal_apply (measurable_of_countable f) (measurableSet_singleton i)]
  apply (hν a).trans_le
  apply measureReal_mono (h₂ := by finiteness)
  intro x hx
  simpa only [Set.mem_singleton_iff.1 hx, Set.mem_preimage, Set.mem_singleton_iff] using ha

/-- Coordinatewise merging commutes with the iid law of the actual geometric series. -/
theorem map_alphabetSeries_merge {α ι : Type*} [Fintype α] [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ι) (b : ι → ℝ) (q : ℝ) :
    (Measure.infinitePi (fun _ : ℕ => ν.map f)).map (alphabetSeries b q) =
      (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries (fun a => b (f a)) q) := by
  have hm : Measurable (fun ω : ℕ → α => fun j : ℕ => f (ω j)) :=
    Measurable.of_eval (fun j => (measurable_of_countable f).comp (measurable_pi_apply j))
  rw [← Measure.infinitePi_map_pi (fun _ : ℕ => ν) (f := fun _ : ℕ => f)
    (fun _ => measurable_of_countable f),
    Measure.map_map (measurable_alphabetSeries b q) hm]
  rfl

/-- Actual iid series admit the entropy bound of their merged finite digit law.
The entropy masses are explicitly the fiber sums, so coincident values are merged before counting. -/
theorem exists_full_mass_mergedAlphabetSeries_entropy_cover
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (hν : ∀ a, 0 < ν.real {a})
    (f : α → ι) (hf : Function.Surjective f) (b : ι → ℝ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries (fun a => b (f a)) q) F = 1 ∧
      dimH F ≤ ENNReal.ofReal
        (finiteEntropy (fun i => ∑ a, if f a = i then ν.real {a} else 0) / (-Real.log q)) := by
  have hp := finite_map_singleton_probability_pos ν hν f hf
  have hs := exists_full_mass_alphabetSeries_entropy_cover (ν.map f)
    (fun i => (ν.map f).real {i}) hp (fun _ => rfl) b hq hq1
  simp_rw [finite_map_singleton_probability ν f] at hs
  rwa [map_alphabetSeries_merge ν f b q] at hs

/-- Consecutive finite words, used to regroup a geometric series into independent blocks. -/
def consecutiveBlocks {α : Type*} (N : ℕ) (ω : ℕ → α) (j : ℕ) (k : Fin N) : α :=
  ω (j * N + k)

/-- Regrouping the actual convergent digit series into blocks changes no value. -/
theorem alphabetSeries_consecutiveBlocks {α : Type*} [Fintype α]
    (b : α → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (N : ℕ) [NeZero N] (ω : ℕ → α) :
    alphabetSeries b q ω =
      alphabetSeries (alphabetPrefix b q N) (q ^ N) (consecutiveBlocks N ω) := by
  let e := (Nat.divModEquiv N).symm
  have hs : Summable (fun z : ℕ × Fin N =>
      b (ω (z.1 * N + z.2)) * q ^ (z.1 * N + z.2)) := by
    exact (summable_alphabetSeries b hq hq1 ω).comp_injective e.injective
  unfold alphabetSeries
  calc
    _ = ∑' z : ℕ × Fin N, b (ω (z.1 * N + z.2)) * q ^ (z.1 * N + z.2) :=
      (e.tsum_eq (fun j : ℕ => b (ω j) * q ^ j)).symm
    _ = ∑' j : ℕ, ∑' k : Fin N, b (ω (j * N + k)) * q ^ (j * N + k) := hs.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype, alphabetPrefix, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [consecutiveBlocks]
      rw [pow_add, mul_comm j N, pow_mul]
      ring

/-- The finite set of distinct real digit values, so equal digits give one atom. -/
noncomputable def alphabetValues {α : Type*} [Fintype α] (b : α → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image b

/-- The canonical map from letters to their merged real-value alphabet. -/
noncomputable def mergeLetter {α : Type*} [Fintype α] (b : α → ℝ) (a : α) :
    alphabetValues b :=
  ⟨b a, by classical simp [alphabetValues]⟩

theorem mergeLetter_surjective {α : Type*} [Fintype α] (b : α → ℝ) :
    Function.Surjective (mergeLetter b) := by
  classical
  intro i
  have hi := i.property
  change i.val ∈ Finset.univ.image b at hi
  rcases Finset.mem_image.1 hi with ⟨a, _, ha⟩
  exact ⟨a, Subtype.ext ha⟩

/-- Actual Shannon entropy after merging every coincident real digit value. -/
noncomputable def mergedAlphabetEntropy {α : Type*} [Fintype α] [MeasurableSpace α]
    (ν : Measure α) (b : α → ℝ) : ℝ := by
  classical
  exact finiteEntropy (fun i : alphabetValues b =>
    ∑ a, if b a = i.val then ν.real {a} else 0)

/-- Canonical merging requires no user-supplied atom set or probability vector. -/
theorem exists_full_mass_canonicallyMergedSeries_entropy_cover
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (hν : ∀ a, 0 < ν.real {a})
    (b : α → ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries b q) F = 1 ∧
      dimH F ≤ ENNReal.ofReal (mergedAlphabetEntropy ν b / (-Real.log q)) := by
  classical
  have hs := exists_full_mass_mergedAlphabetSeries_entropy_cover ν hν
    (mergeLetter b) (mergeLetter_surjective b) (fun i => i.val) hq hq1
  simpa only [mergeLetter, Subtype.ext_iff, mergedAlphabetEntropy] using hs

/-- A finite word's singleton mass is its product probability, before merging block values. -/
theorem pi_singleton_real_eq_wordProbability
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (N : ℕ) (w : Fin N → α) :
    (Measure.pi (fun _ : Fin N => ν)).real {w} =
      wordProbability (fun a => ν.real {a}) N w := by
  rw [measureReal_def, Measure.pi_singleton]
  simp only [wordProbability, ENNReal.toReal_prod, measureReal_def]

theorem measurable_consecutiveBlocks {α : Type*} [MeasurableSpace α] (N : ℕ) :
    Measurable (consecutiveBlocks (α := α) N) :=
  Measurable.of_eval (fun j => Measurable.of_eval (fun k => measurable_pi_apply (j * N + k)))

/-- Disjoint consecutive blocks of an iid process have the actual finite product block law. -/
theorem map_consecutiveBlocks {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (N : ℕ) (hN : 0 < N) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (consecutiveBlocks N) =
      Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin N => ν)) := by
  have hinj : Function.Injective (fun p : ℕ × Fin N => p.1 * N + p.2) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ hab
    have hm := congrArg (fun m => m % N) hab
    simp only [Nat.mul_add_mod_of_lt i.isLt, Nat.mul_add_mod_of_lt j.isLt] at hm
    have hi : i = j := Fin.ext hm
    subst j
    have hd := congrArg (fun m => m / N) hab
    simp only [Nat.mul_comm a N, Nat.mul_comm b N, Nat.mul_add_div hN,
      Nat.div_eq_of_lt i.isLt, Nat.add_zero] at hd
    cases hd
    rfl
  have hflat := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) hinj
  have hcur := Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin N) => ν)
  have h := congrArg (Measure.map (MeasurableEquiv.curry ℕ (Fin N) α)) hflat
  rw [Measure.map_map (by fun_prop) (by fun_prop), hcur] at h
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  congr 1

/-- The actual series law is unchanged when its independent digits are grouped into blocks. -/
theorem map_alphabetSeries_consecutiveBlocks {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (b : α → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) (hN : 0 < N) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries b q) =
      (Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin N => ν))).map
        (alphabetSeries (alphabetPrefix b q N) (q ^ N)) := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [← map_consecutiveBlocks ν N hN,
    Measure.map_map (measurable_alphabetSeries (alphabetPrefix b q N) (q ^ N))
      (measurable_consecutiveBlocks N)]
  congr 1
  funext ω
  exact alphabetSeries_consecutiveBlocks b hq hq1 N ω

/-- The merged probability of a finite block value, as the explicit sum of word probabilities. -/
noncomputable def finiteBlockAtomProbability {α : Type*} [Fintype α] [MeasurableSpace α]
    (ν : Measure α) (b : α → ℝ) (q : ℝ) (N : ℕ)
    (i : alphabetValues (alphabetPrefix b q N)) : ℝ := by
  classical
  exact ∑ w : Fin N → α, if alphabetPrefix b q N w = i.val then
    wordProbability (fun a => ν.real {a}) N w else 0

/-- Shannon entropy of the merged block atoms, with all probabilities computed explicitly. -/
noncomputable def finiteBlockEntropy {α : Type*} [Fintype α] [MeasurableSpace α]
    (ν : Measure α) (b : α → ℝ) (q : ℝ) (N : ℕ) : ℝ :=
  finiteEntropy (finiteBlockAtomProbability ν b q N)

theorem finiteBlockEntropy_eq_mergedAlphabetEntropy
    {α : Type*} [Fintype α] [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → ℝ) (q : ℝ) (N : ℕ) :
    finiteBlockEntropy ν b q N =
      mergedAlphabetEntropy (Measure.pi (fun _ : Fin N => ν)) (alphabetPrefix b q N) := by
  classical
  unfold finiteBlockEntropy mergedAlphabetEntropy
  congr 1
  funext i
  simp only [finiteBlockAtomProbability, pi_singleton_real_eq_wordProbability]

/-- The full block-entropy bound for an actual finite-alphabet iid geometric series.
No cover, typicality, or dimension premise is assumed; the block law and merged atoms are explicit. -/
theorem exists_full_mass_blockEntropy_cover
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (hν : ∀ a, 0 < ν.real {a})
    (b : α → ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (N : ℕ) (hN : 0 < N) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries b q) F = 1 ∧
      dimH F ≤ ENNReal.ofReal (finiteBlockEntropy ν b q N / ((N : ℝ) * (-Real.log q))) := by
  have hpos (w : Fin N → α) : 0 < (Measure.pi (fun _ : Fin N => ν)).real {w} := by
    rw [pi_singleton_real_eq_wordProbability]
    exact wordProbability_pos hν N w
  have hs := exists_full_mass_canonicallyMergedSeries_entropy_cover
    (Measure.pi (fun _ : Fin N => ν)) hpos (alphabetPrefix b q N)
    (pow_pos hq N) (pow_lt_one₀ hq.le hq1 hN.ne')
  rw [← map_alphabetSeries_consecutiveBlocks ν b hq.le hq1 N hN,
    ← finiteBlockEntropy_eq_mergedAlphabetEntropy ν b q N] at hs
  simpa only [Real.log_pow, neg_mul_eq_mul_neg] using hs

/-- Push the finite digit law to real digits before or after forming the actual series. -/
theorem map_alphabetSeries_realDigits {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → ℝ) (q : ℝ) :
    (Measure.infinitePi (fun _ : ℕ => ν.map b)).map
      (fun ω : ℕ → ℝ => ∑' j : ℕ, ω j * q ^ j) =
      (Measure.infinitePi (fun _ : ℕ => ν)).map (alphabetSeries b q) := by
  have hS : Measurable (fun ω : ℕ → ℝ => ∑' j : ℕ, ω j * q ^ j) := by
    apply Measurable.tsum
    intro j
    fun_prop
  have hm : Measurable (fun ω : ℕ → α => fun j : ℕ => b (ω j)) :=
    Measurable.of_eval (fun j => (measurable_of_countable b).comp (measurable_pi_apply j))
  rw [← Measure.infinitePi_map_pi (fun _ : ℕ => ν) (f := fun _ : ℕ => b)
    (fun _ => measurable_of_countable b), Measure.map_map hS hm]
  rfl

/-- The finite fair sign alphabet, before applying its real digit map. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure fairBoolMeasure := by
  constructor
  rw [fairBoolMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _)]
  simpa [smul_eq_mul, one_div] using ENNReal.inv_two_add_inv_two

theorem fairBoolMeasure_real_singleton (a : Bool) : fairBoolMeasure.real {a} = 1 / 2 := by
  cases a <;> norm_num [fairBoolMeasure, measureReal_def, Measure.smul_apply,
    Measure.add_apply, smul_eq_mul]

def fairSignDigit (a : Bool) : ℝ := if a then 1 else -1

/-- The Boolean fair law pushes forward to exactly the symmetric real sign law. -/
theorem map_fairBoolMeasure_fairSignDigit :
    fairBoolMeasure.map fairSignDigit =
      (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
        (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) := by
  rw [fairBoolMeasure, Measure.map_add _ _ (measurable_of_countable fairSignDigit)]
  rw [Measure.map_smul _ (measurable_of_countable fairSignDigit).aemeasurable,
    Measure.map_smul _ (measurable_of_countable fairSignDigit).aemeasurable]
  simp [Measure.map_dirac, fairSignDigit]

/-- The paper's actual Shannon block entropy, with coincident finite sign sums merged. -/
noncomputable def signBlockEntropy (β : ℝ) (N : ℕ) : ℝ :=
  finiteBlockEntropy fairBoolMeasure fairSignDigit β⁻¹ N

/-- The paper's block lemma for the explicit real-sign series law, independent of endpoint wrappers. -/
theorem exists_full_mass_signBlockEntropy_cover (β : ℝ) (hβ : 1 < β)
    (N : ℕ) (hN : 0 < N) :
    ∃ F : Set ℝ, MeasurableSet F ∧
      (Measure.infinitePi (fun _ : ℕ =>
        (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
          (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ))).map
        (fun ω : ℕ → ℝ => ∑' j : ℕ, ω j * β⁻¹ ^ j) F = 1 ∧
      dimH F ≤ ENNReal.ofReal (signBlockEntropy β N / (N : ℝ) / Real.log β) := by
  have hpos (a : Bool) : 0 < fairBoolMeasure.real {a} := by
    rw [fairBoolMeasure_real_singleton]
    norm_num
  have hs := exists_full_mass_blockEntropy_cover fairBoolMeasure hpos fairSignDigit
    (inv_pos.2 (by linarith : 0 < β)) (inv_lt_one_of_one_lt₀ hβ) N hN
  have hlaw := map_alphabetSeries_realDigits fairBoolMeasure fairSignDigit β⁻¹
  rw [map_fairBoolMeasure_fairSignDigit] at hlaw
  rw [← hlaw] at hs
  simpa only [signBlockEntropy, Real.log_inv, neg_neg, div_div] using hs

/-- The explicit merged block probability is exactly its singleton mass under the block law. -/
theorem finiteBlockAtomProbability_eq_singleton
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → ℝ) (q : ℝ) (N : ℕ)
    (i : alphabetValues (alphabetPrefix b q N)) :
    finiteBlockAtomProbability ν b q N i =
      ((Measure.pi (fun _ : Fin N => ν)).map (mergeLetter (alphabetPrefix b q N))).real {i} := by
  classical
  rw [finite_map_singleton_probability]
  simp only [finiteBlockAtomProbability, mergeLetter, Subtype.ext_iff,
    pi_singleton_real_eq_wordProbability]

theorem sum_finiteBlockAtomProbability
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → ℝ) (q : ℝ) (N : ℕ) :
    ∑ i, finiteBlockAtomProbability ν b q N i = 1 := by
  simp_rw [finiteBlockAtomProbability_eq_singleton]
  simpa only [Finset.coe_univ, probReal_univ] using
    (sum_measureReal_singleton
      (μ := (Measure.pi (fun _ : Fin N => ν)).map (mergeLetter (alphabetPrefix b q N)))
      (Finset.univ : Finset (alphabetValues (alphabetPrefix b q N))))

theorem finiteBlockAtomProbability_nonneg
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → ℝ) (q : ℝ) (N : ℕ)
    (i : alphabetValues (alphabetPrefix b q N)) :
    0 ≤ finiteBlockAtomProbability ν b q N i := by
  rw [finiteBlockAtomProbability_eq_singleton]
  exact ENNReal.toReal_nonneg

theorem finiteBlockAtomProbability_pos
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (hν : ∀ a, 0 < ν.real {a})
    (b : α → ℝ) (q : ℝ) (N : ℕ)
    (i : alphabetValues (alphabetPrefix b q N)) :
    0 < finiteBlockAtomProbability ν b q N i := by
  rw [finiteBlockAtomProbability_eq_singleton]
  apply finite_map_singleton_probability_pos
    (Measure.pi (fun _ : Fin N => ν)) _ _ (mergeLetter_surjective _) i
  intro w
  rw [pi_singleton_real_eq_wordProbability]
  exact wordProbability_pos hν N w

theorem finiteBlockEntropy_nonneg
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → ℝ) (q : ℝ) (N : ℕ) :
    0 ≤ finiteBlockEntropy ν b q N :=
  finiteEntropy_nonneg_of_probability (finiteBlockAtomProbability_nonneg ν b q N)
    (sum_finiteBlockAtomProbability ν b q N)

end Salem
