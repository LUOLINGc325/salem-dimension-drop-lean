module

public import Salem.FiniteEntropy
public import Salem.FourierBias
public import Salem.LacunaryProduct

@[expose] public section

open scoped BigOperators
open MeasureTheory Set

namespace Salem

/-- The half-open spatial cell indexed by `k`, at grid scale `δ`. -/
def gridCell (δ : ℝ) (k : ℤ) : Set ℝ := Ico ((k : ℝ) * δ) (((k : ℝ) + 1) * δ)

/-- All grid indices which can occur on the support interval `[-R,R]`. -/
noncomputable def gridIndexSet (R δ : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋

/-- The actual probability of one grid cell under the given measure. -/
noncomputable def gridMass (μ : Measure ℝ) (δ : ℝ) (k : ℤ) : ℝ := μ.real (gridCell δ k)

/-- Grid cells are exactly the fibers of the floor map, including their
left endpoints and excluding their right endpoints. -/
theorem gridCell_eq_floor_fiber {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    gridCell δ k = {x : ℝ | ⌊x / δ⌋ = k} := by
  ext x
  simp only [gridCell, mem_Ico, mem_ofPred_eq, Int.floor_eq_iff,
    le_div_iff₀ hδ, div_lt_iff₀ hδ]

/-- The grid mass is the singleton probability of the actual pushforward
by `x ↦ floor(x/δ)`, rather than an independently supplied finite vector. -/
theorem gridMass_eq_map_floor (μ : Measure ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    gridMass μ δ k = (Measure.map (fun x : ℝ => ⌊x / δ⌋) μ).real {k} := by
  have hf : Measurable (fun x : ℝ => ⌊x / δ⌋) := Int.measurable_floor.comp (measurable_id.div_const δ)
  unfold gridMass Measure.real
  rw [Measure.map_apply hf (measurableSet_singleton k), gridCell_eq_floor_fiber hδ]
  rfl

/-- A point in the stated support interval has an index in the explicit
finite grid index set. -/
theorem floor_mem_gridIndexSet {R δ x : ℝ} (hδ : 0 < δ) (hx : x ∈ Icc (-R) R) :
    ⌊x / δ⌋ ∈ gridIndexSet R δ := by
  simp only [gridIndexSet, Finset.mem_Icc]
  constructor
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hδ).mpr hx.1)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hδ).mpr hx.2)

/-- The finitely indexed cell masses form a genuine probability law whenever
`μ` is supported almost everywhere on `[-R,R]`. Zero-probability cells remain
in the index type and contribute zero to Shannon entropy. -/
theorem gridMass_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R δ : ℝ} (hδ : 0 < δ) (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    (∀ k : gridIndexSet R δ, 0 ≤ gridMass μ δ k) ∧
      (∑ k : gridIndexSet R δ, gridMass μ δ k) = 1 := by
  constructor
  · intro k
    exact measureReal_nonneg
  · rw [Finset.sum_coe_sort]
    have hf : Measurable (fun x : ℝ => ⌊x / δ⌋) := Int.measurable_floor.comp (measurable_id.div_const δ)
    have hpre : MeasurableSet ((fun x : ℝ => ⌊x / δ⌋) ⁻¹' (gridIndexSet R δ : Set ℤ)) :=
      hf ((gridIndexSet R δ).finite_toSet.measurableSet)
    have hfull : μ ((fun x : ℝ => ⌊x / δ⌋) ⁻¹' (gridIndexSet R δ : Set ℤ)) = 1 := by
      apply (mem_ae_iff_prob_eq_one hpre).mp
      filter_upwards [hsupp] with x hx
      exact floor_mem_gridIndexSet hδ hx
    have hsum := sum_measureReal_preimage_singleton (μ := μ) (gridIndexSet R δ)
      (fun k _ => hf (measurableSet_singleton k))
    have hcell (k : ℤ) : gridCell δ k = (fun x : ℝ => ⌊x / δ⌋) ⁻¹' {k} := by
      rw [gridCell_eq_floor_fiber hδ]
      rfl
    simpa only [gridMass, hcell, Measure.real, hfull, ENNReal.toReal_one] using hsum

/-- Every function of the finite grid value has its actual expectation given
by the finite grid masses. Its integrability is automatic on the bounded support. -/
theorem gridMass_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R δ : ℝ} (hδ : 0 < δ) (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) (f : ℤ → ℝ) :
    Integrable (fun x => f ⌊x / δ⌋) μ ∧
      (∫ x, f ⌊x / δ⌋ ∂μ) = ∑ k : gridIndexSet R δ, gridMass μ δ k * f k := by
  classical
  let g : ℝ → ℝ := fun x => ∑ k ∈ gridIndexSet R δ, (gridCell δ k).indicator (fun _ => f k) x
  have hi (k : ℤ) : Integrable ((gridCell δ k).indicator (fun _ : ℝ => f k)) μ :=
    (integrable_const (f k)).indicator measurableSet_Ico
  have hg : Integrable g μ := integrable_finsetSum _ (fun k _ => hi k)
  have hae : g =ᵐ[μ] (fun x => f ⌊x / δ⌋) := by
    filter_upwards [hsupp] with x hx
    have hk := floor_mem_gridIndexSet hδ hx
    simp [g, gridCell_eq_floor_fiber hδ, Set.indicator_apply, eq_comm, hk]
  refine ⟨hg.congr hae, ?_⟩
  rw [← integral_congr_ae hae,
    Finset.sum_coe_sort (gridIndexSet R δ) (fun k : ℤ => gridMass μ δ k * f k)]
  change (∫ x, ∑ k ∈ gridIndexSet R δ, (gridCell δ k).indicator (fun _ => f k) x ∂μ) = _
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_indicator_const (f k) (show MeasurableSet (gridCell δ k) from measurableSet_Ico)]
  rfl

/-- Distinct grid cells are disjoint, with no boundary mass ambiguity. -/
theorem gridCell_disjoint {δ : ℝ} (hδ : 0 < δ) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (gridCell δ i) (gridCell δ j) := by
  rw [gridCell_eq_floor_fiber hδ, gridCell_eq_floor_fiber hδ]
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (hi.symm.trans hj)

/-- At scale at most one, every selected grid cell is contained in the
paper's common interval `[-R-1,R+1]`, including cells of zero probability. -/
theorem gridCell_subset_containing {R δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {k : ℤ} (hk : k ∈ gridIndexSet R δ) : gridCell δ k ⊆ Icc (-R - 1) (R + 1) := by
  have hk' := Finset.mem_Icc.mp hk
  have hklo : (⌊-R / δ⌋ : ℝ) ≤ k := by exact_mod_cast hk'.1
  have hkhi : (k : ℝ) ≤ (⌊R / δ⌋ : ℝ) := by exact_mod_cast hk'.2
  have hlo : -R < ((⌊-R / δ⌋ : ℝ) + 1) * δ :=
    (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (-R / δ))
  have hhi : (⌊R / δ⌋ : ℝ) * δ ≤ R := (le_div_iff₀ hδ).mp (Int.floor_le (R / δ))
  have hmullo := mul_le_mul_of_nonneg_right hklo hδ.le
  have hmulhi := mul_le_mul_of_nonneg_right hkhi hδ.le
  intro x hx
  constructor <;> dsimp [gridCell] at hx <;> nlinarith [hx.1, hx.2, hmullo, hmulhi]

/-- Two points of the same half-open cell are at distance at most its scale. -/
theorem gridCell_abs_sub_le {δ x y : ℝ} {k : ℤ}
    (hx : x ∈ gridCell δ k) (hy : y ∈ gridCell δ k) : |x - y| ≤ δ := by
  dsimp [gridCell] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

/-- Lebesgue volume of one nonnegative-scale grid cell. -/
theorem gridCell_volume {δ : ℝ} (hδ : 0 ≤ δ) (k : ℤ) : volume.real (gridCell δ k) = δ := by
  unfold gridCell
  rw [Real.volume_real_Ico]
  have heq : ((k : ℝ) + 1) * δ - (k : ℝ) * δ = δ := by ring
  rw [heq, max_eq_left hδ]

/-- The unnormalized reference weight is the cell integral divided by its
width, exactly the weight whose normalization is used in the grid entropy proof. -/
noncomputable def gridReferenceWeight (P : ℝ → ℝ) (δ : ℝ) (k : ℤ) : ℝ :=
  δ⁻¹ * ∫ x in gridCell δ k, P x

/-- Log-Lipschitz control yields the actual lower bound on each cell integral.
No pointwise sample is substituted for the integral reference weight. -/
theorem gridReferenceWeight_lower {P : ℝ → ℝ} {δ K B : ℝ}
    (hδ : 0 < δ) (hPcont : Continuous P) (hPpos : ∀ x, 0 < P x)
    (hK : 0 ≤ K) (hKB : K * δ ≤ B)
    (hlip : ∀ x y, |Real.log (P x) - Real.log (P y)| ≤ K * |x - y|)
    (k : ℤ) {y : ℝ} (hy : y ∈ gridCell δ k) :
    Real.exp (Real.log (P y) - B) ≤ gridReferenceWeight P δ k := by
  have hpoint (x : ℝ) (hx : x ∈ gridCell δ k) : Real.exp (Real.log (P y) - B) ≤ P x := by
    have hh := (hlip x y).trans (mul_le_mul_of_nonneg_left (gridCell_abs_sub_le hx hy) hK)
    have hlow := (abs_le.mp hh).1
    have he := Real.exp_le_exp.mpr (show Real.log (P y) - B ≤ Real.log (P x) by linarith)
    simpa only [Real.exp_log (hPpos x)] using he
  have hiP : IntegrableOn P (gridCell δ k) :=
    hPcont.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hic : IntegrableOn (fun _ : ℝ => Real.exp (Real.log (P y) - B)) (gridCell δ k) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hI := setIntegral_mono_on hic hiP (show MeasurableSet (gridCell δ k) from measurableSet_Ico) hpoint
  rw [setIntegral_const, gridCell_volume hδ.le, smul_eq_mul] at hI
  change Real.exp (Real.log (P y) - B) ≤ δ⁻¹ * _
  calc
    _ = δ⁻¹ * (δ * Real.exp (Real.log (P y) - B)) := by field_simp [hδ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hδ.le)

/-- The reference weights are strictly positive, including in zero-probability
cells, and their logarithms dominate every log-product value in the same cell. -/
theorem gridReferenceWeight_log_lower {P : ℝ → ℝ} {δ K B : ℝ}
    (hδ : 0 < δ) (hPcont : Continuous P) (hPpos : ∀ x, 0 < P x)
    (hK : 0 ≤ K) (hKB : K * δ ≤ B)
    (hlip : ∀ x y, |Real.log (P x) - Real.log (P y)| ≤ K * |x - y|)
    (k : ℤ) : 0 < gridReferenceWeight P δ k ∧
      ∀ y ∈ gridCell δ k, Real.log (P y) - B ≤ Real.log (gridReferenceWeight P δ k) := by
  have hy : (k : ℝ) * δ ∈ gridCell δ k := by
    constructor
    · exact le_rfl
    · nlinarith
  have hw := gridReferenceWeight_lower hδ hPcont hPpos hK hKB hlip k hy
  refine ⟨(Real.exp_pos _).trans_le hw, ?_⟩
  intro y hy
  have hh := Real.log_le_log (Real.exp_pos _) (gridReferenceWeight_lower hδ hPcont hPpos hK hKB hlip k hy)
  simpa only [Real.log_exp] using hh

/-- The actual sum of cell-integral reference weights is bounded by the
containing-interval integral divided by `δ`. -/
theorem gridReferenceWeight_sum_le_integral {P : ℝ → ℝ} {R δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hPcont : Continuous P) (hPnonneg : ∀ x, 0 ≤ P x) :
    (∑ k : gridIndexSet R δ, gridReferenceWeight P δ k) ≤
      δ⁻¹ * ∫ x in Icc (-R - 1) (R + 1), P x := by
  let S := gridIndexSet R δ
  have hd : Set.Pairwise (S : Set ℤ) (fun i j => Disjoint (gridCell δ i) (gridCell δ j)) := by
    intro i _ j _ hij
    exact gridCell_disjoint hδ hij
  have hi (k : ℤ) : IntegrableOn P (gridCell δ k) :=
    hPcont.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have heq := integral_biUnion_finset S (s := gridCell δ)
    (fun _ _ => measurableSet_Ico) hd (fun k _ => hi k)
  have hsub : (⋃ k ∈ S, gridCell δ k) ⊆ Icc (-R - 1) (R + 1) := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨k, hx⟩
    rcases mem_iUnion.mp hx with ⟨hk, hx⟩
    exact gridCell_subset_containing hδ hδ1 hk hx
  have hPI : IntegrableOn P (Icc (-R - 1) (R + 1)) volume := hPcont.continuousOn.integrableOn_Icc
  have hm := setIntegral_mono_set hPI
    (Filter.Eventually.of_forall hPnonneg) (Filter.Eventually.of_forall fun x hx => hsub hx)
  rw [heq] at hm
  rw [Finset.sum_coe_sort]
  change (∑ k ∈ S, δ⁻¹ * ∫ x in gridCell δ k, P x) ≤ _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hδ.le)

/-- The grid entropy inequality from actual measure probabilities and actual
cell-integral weights. Neither an entropy bound nor a normalized reference law
is assumed; the finite Gibbs inequality constructs the comparison internally. -/
theorem gridEntropy_le_log_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {P : ℝ → ℝ} {R δ K B : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-R) R)
    (hPcont : Continuous P) (hPpos : ∀ x, 0 < P x) (hK : 0 ≤ K) (hKB : K * δ ≤ B)
    (hlip : ∀ x y, |Real.log (P x) - Real.log (P y)| ≤ K * |x - y|) :
    finiteEntropy (fun k : gridIndexSet R δ => gridMass μ δ k) ≤
      -Real.log δ - (∫ x, Real.log (P x) ∂μ) + B +
        Real.log (∫ x in Icc (-R - 1) (R + 1), P x) := by
  let w : ℤ → ℝ := gridReferenceWeight P δ
  have hw (k : ℤ) := gridReferenceWeight_log_lower hδ hPcont hPpos hK hKB hlip k
  have hp := gridMass_probability μ hδ hsupp
  have hzero : (0 : ℤ) ∈ gridIndexSet R δ := by
    simpa using (floor_mem_gridIndexSet hδ (show (0 : ℝ) ∈ Icc (-R) R by constructor <;> linarith))
  let : Nonempty (gridIndexSet R δ) := ⟨⟨0, hzero⟩⟩
  have hws : 0 < ∑ k : gridIndexSet R δ, w k :=
    Finset.sum_pos (fun k _ => (hw k).1) Finset.univ_nonempty
  have hnorm := gridReferenceWeight_sum_le_integral (R := R) hδ hδ1 hPcont (fun x => (hPpos x).le)
  have hZ : 0 < ∫ x in Icc (-R - 1) (R + 1), P x := by
    have hh : 0 < δ⁻¹ * ∫ x in Icc (-R - 1) (R + 1), P x := hws.trans_le hnorm
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hδ)).mp hh
  have hGibbs := finiteEntropy_add_expectation_le_log_sum_exp hp.1 hp.2
    (fun k : gridIndexSet R δ => Real.log (w k))
  have hexp : (∑ k : gridIndexSet R δ, Real.exp (Real.log (w k))) = ∑ k : gridIndexSet R δ, w k := by
    apply Finset.sum_congr rfl
    intro k _
    exact Real.exp_log (hw k).1
  rw [hexp] at hGibbs
  have ht := gridMass_expectation μ hδ hsupp (fun k => Real.log (w k))
  have hlogcont : Continuous (fun x => Real.log (P x)) := hPcont.log (fun x => (hPpos x).ne')
  have hlogint : Integrable (fun x => Real.log (P x)) μ := by
    have hh : IntegrableOn (fun x => Real.log (P x)) (Icc (-R) R) μ := hlogcont.continuousOn.integrableOn_Icc
    unfold IntegrableOn at hh
    rwa [Measure.restrict_eq_self_of_ae_mem hsupp] at hh
  have hcompare : (∫ x, Real.log (P x) ∂μ) ≤
      (∑ k : gridIndexSet R δ, gridMass μ δ k * Real.log (w k)) + B := by
    have hh := integral_mono hlogint (ht.1.add (integrable_const B)) (fun x => by
      have hx : x ∈ gridCell δ ⌊x / δ⌋ := by rw [gridCell_eq_floor_fiber hδ]; rfl
      have hlow := (hw ⌊x / δ⌋).2 x hx
      change Real.log (P x) - B ≤ Real.log (w ⌊x / δ⌋) at hlow
      change Real.log (P x) ≤ Real.log (w ⌊x / δ⌋) + B
      linarith [hlow])
    change (∫ x, Real.log (P x) ∂μ) ≤ (∫ x, Real.log (w ⌊x / δ⌋) + B ∂μ) at hh
    simpa only [integral_add ht.1 (integrable_const B), integral_const, probReal_univ,
      one_smul, ht.2] using hh
  have hlognorm := Real.log_le_log hws hnorm
  rw [Real.log_mul (inv_ne_zero hδ.ne') hZ.ne', Real.log_inv] at hlognorm
  linarith [hGibbs, hcompare, hlognorm]

/-- The actual finite grid Fourier-Shannon criterion, with the paper's exact
constants. The sign product, its mean gain, its integral bound, and its
log-Lipschitz bound are all supplied by the proved analytic construction. -/
theorem lacunary_gridEntropy_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R δ a Q : ℝ} {ξ : ℕ → ℝ} (n : ℕ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-R) R)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) (hscale : δ * ξ n ≤ 1)
    (hfourier : ∀ i ≤ n, a ≤ |∫ x, Real.cos (ξ i * x) ∂μ|) :
    finiteEntropy (fun k : gridIndexSet R δ => gridMass μ δ k) ≤
      -Real.log δ - (n + 1 : ℕ) * fourierBiasGain a +
        a * Q / ((1 - a) * (Q - 1)) +
        Real.log (2 * R + 2 + 2 * a /
          (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))) := by
  classical
  have ha1 : a < 1 := by linarith
  obtain ⟨s, hsign, _, _, hgain, _⟩ := integral_fourier_log_product_lower_bound μ
    (fun j : Fin (n + 1) => ξ j) ha ha1 (fun j => hfourier j (by omega))
  let σ : ℕ → ℝ := fun i => if hi : i < n + 1 then s ⟨i, hi⟩ else 1
  have hσ : ∀ i ≤ n, |σ i| = 1 := by
    intro i hi
    dsimp [σ]
    rw [dite_eq_left (by omega : i < n + 1)]
    rcases hsign ⟨i, by omega⟩ with h | h <;> rw [h] <;> norm_num
  let P : ℝ → ℝ := trigProduct a σ ξ (n + 1)
  have hprod (x : ℝ) : P x = ∏ j : Fin (n + 1), (1 + a * (s j * Real.cos (ξ j * x))) := by
    dsimp [P, trigProduct]
    rw [← Fin.prod_univ_eq_prod_range (fun i => 1 + a * σ i * Real.cos (ξ i * x)) (n + 1)]
    apply Finset.prod_congr rfl
    intro j _
    dsimp [σ]
    rw [ite_eq_left j.isLt]
    ring
  have hmean : (n + 1 : ℕ) * fourierBiasGain a ≤ ∫ x, Real.log (P x) ∂μ := by
    simpa only [← hprod, Fintype.card_fin] using hgain
  have hPcont : Continuous P := by unfold P trigProduct; fun_prop
  have hPpos : ∀ x, 0 < P x := fun x =>
    trigProduct_pos (n + 1) ha ha1 (fun i hi => hσ i (by omega)) x
  have hQ0 : 0 < Q := by linarith
  have hξ (i : ℕ) (hi : i ≤ n) : 0 < ξ i :=
    (mul_pos (pow_pos hQ0 i) (Real.pi_pos.trans_le hξ₀)).trans_le
      (lacunary_frequency_power_lower hQ0.le i (fun j hj => hgap j (by omega)))
  let B : ℝ := a * Q / ((1 - a) * (Q - 1))
  let D : ℝ := 2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg ha hQ0.le) (mul_pos (by linarith : 0 < 1 - a) (by linarith : 0 < Q - 1)).le
  have hK : 0 ≤ B * ξ n := mul_nonneg hB (hξ n le_rfl).le
  have hKB : (B * ξ n) * δ ≤ B := by
    have hh := mul_le_mul_of_nonneg_left hscale hB
    nlinarith [hh]
  have hlip (x y : ℝ) : |Real.log (P x) - Real.log (P y)| ≤ (B * ξ n) * |x - y| :=
    lacunary_log_trigProduct_lipschitz n ha ha1 (by linarith) hσ
      (fun i hi => (hξ i hi).le) hgap y x
  have hgrid := gridEntropy_le_log_integral μ hR hδ hδ1 hsupp hPcont hPpos hK hKB hlip
  have heq : (∫ x in Icc (-R - 1) (R + 1), P x) = ∫ x in (-R - 1)..(R + 1), P x := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith : -R - 1 ≤ R + 1)]
  have hZ : 0 < ∫ x in Icc (-R - 1) (R + 1), P x := by
    rw [heq]
    exact intervalIntegral.intervalIntegral_pos_of_pos (hPcont.intervalIntegrable _ _) hPpos (by linarith)
  have hInt := lacunary_trigProduct_integral_upper_bound (n + 1) ha ha2 hQ hξ₀
    (fun i hi => hσ i (by omega)) (fun i hi => hgap i (by omega)) (-R - 1) (R + 1)
  have hZbound : (∫ x in Icc (-R - 1) (R + 1), P x) ≤ 2 * R + 2 + D := by
    rw [heq]
    simpa only [P, D, show (R + 1) - (-R - 1) = 2 * R + 2 by ring] using hInt
  have hlog := Real.log_le_log hZ hZbound
  change finiteEntropy (fun k : gridIndexSet R δ => gridMass μ δ k) ≤
    -Real.log δ - (n + 1 : ℕ) * fourierBiasGain a + B + Real.log (2 * R + 2 + D)
  linarith [hgrid, hmean, hlog]

/-- At the paper's scale `δ = β⁻ᴺ`, the grid entropy has the exact
`N log β - M Ψ(a) + B + log(2R+2+D)` upper bound. -/
theorem lacunary_gridEntropy_bound_at_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R β a Q : ℝ} {ξ : ℕ → ℝ} (n N : ℕ)
    (hR : 0 ≤ R) (hβ : 1 < β) (hsupp : ∀ᵐ x ∂μ, x ∈ Icc (-R) R)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) (hscale : β⁻¹ ^ N * ξ n ≤ 1)
    (hfourier : ∀ i ≤ n, a ≤ |∫ x, Real.cos (ξ i * x) ∂μ|) :
    finiteEntropy (fun k : gridIndexSet R (β⁻¹ ^ N) => gridMass μ (β⁻¹ ^ N) k) ≤
      (N : ℝ) * Real.log β - (n + 1 : ℕ) * fourierBiasGain a +
        a * Q / ((1 - a) * (Q - 1)) +
        Real.log (2 * R + 2 + 2 * a /
          (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))) := by
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  have hδpos : 0 < β⁻¹ ^ N := pow_pos (inv_pos.mpr hβpos) N
  have hinv : β⁻¹ ≤ 1 := (inv_le_one₀ hβpos).mpr hβ.le
  have hδle : β⁻¹ ^ N ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hβpos.le) hinv
  have hlog : -Real.log (β⁻¹ ^ N) = (N : ℝ) * Real.log β := by
    rw [Real.log_pow, Real.log_inv]
    ring
  simpa only [hlog] using lacunary_gridEntropy_bound μ n hR hδpos hδle hsupp
    ha ha2 hQ hξ₀ hgap hscale hfourier

/-- Deterministically merging equal values cannot increase finite Shannon
entropy. The input masses need only be nonnegative. -/
theorem finiteEntropy_atomMass_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (f : ι → κ) :
    finiteEntropy (atomMass p f) ≤ finiteEntropy p := by
  have hself (i : ι) : p i ≤ atomMass p f (f i) := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => if f j = f i then p j else 0)
      (fun j _ => by split_ifs <;> simp_all) (Finset.mem_univ i)
    simpa only [ite_true, atomMass] using hh
  have heq : finiteEntropy (atomMass p f) = ∑ i, -p i * Real.log (atomMass p f (f i)) := by
    have hh := atomMass_expectation p f (fun y => -Real.log (atomMass p f y))
    simpa only [finiteEntropy, Real.negMulLog, mul_neg, neg_mul] using hh
  rw [heq]
  apply Finset.sum_le_sum
  intro i _
  rcases (hp i).eq_or_lt with hzero | hpos
  · simp [← hzero, Real.negMulLog]
  · have hlog := Real.log_le_log hpos (hself i)
    have hm := mul_le_mul_of_nonneg_left hlog (hp i)
    dsimp [Real.negMulLog]
    linarith [hm]

/-- If every fiber of a finite map contains at most `L` positive-probability
atoms, forgetting the atom within its fiber loses at most `log L` entropy.
Only distinct positive atoms are counted; zero masses cause no logarithmic exception. -/
theorem finiteEntropy_le_atomMass_add_log {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (f : ι → κ) {L : ℝ}
    (hcard : ∀ y, ((Finset.univ.filter (fun i => 0 < p i ∧ f i = y)).card : ℝ) ≤ L) :
    finiteEntropy p ≤ finiteEntropy (atomMass p f) + Real.log L := by
  classical
  let S : Finset ι := Finset.univ.filter (fun i => 0 < p i)
  let m : κ → ℝ := atomMass p f
  have hself (i : ι) : p i ≤ m (f i) := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => if f j = f i then p j else 0)
      (fun j _ => by split_ifs <;> simp_all) (Finset.mem_univ i)
    simpa only [ite_true, m, atomMass] using hh
  have hm := atomMass_probability hp hp_sum f
  have hSsum (F : ι → ℝ) (hz : ∀ i, p i = 0 → F i = 0) : (∑ i : S, F i) = ∑ i, F i := by
    rw [Finset.sum_coe_sort]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    have hn : ¬0 < p i := by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact hz i (le_antisymm (le_of_not_gt hn) (hp i))
  have hpS : (∑ i : S, p i) = 1 := by rw [hSsum p (fun _ hz => hz)]; exact hp_sum
  have hmpos (i : S) : 0 < m (f i) :=
    (Finset.mem_filter.mp i.property).2.trans_le (hself i)
  have hWge : (1 : ℝ) ≤ ∑ i : S, m (f i) := by
    rw [← hpS]
    exact Finset.sum_le_sum (fun i _ => hself i)
  have hWpos : 0 < ∑ i : S, m (f i) := lt_of_lt_of_le zero_lt_one hWge
  have hGibbs := finiteEntropy_add_expectation_le_log_sum_exp (fun i : S => hp i) hpS
    (fun i : S => Real.log (m (f i)))
  have hexp : (∑ i : S, Real.exp (Real.log (m (f i)))) = ∑ i : S, m (f i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.exp_log (hmpos i)
  rw [hexp] at hGibbs
  have hH : finiteEntropy (fun i : S => p i) = finiteEntropy p :=
    hSsum (fun i => Real.negMulLog (p i)) (fun i hz => by simp [hz])
  have hE : (∑ i : S, p i * Real.log (m (f i))) = -finiteEntropy m := by
    rw [hSsum (fun i => p i * Real.log (m (f i))) (fun i hz => by simp [hz])]
    have heq := atomMass_expectation p f (fun y => Real.log (m y))
    change (∑ i, p i * Real.log (m (f i))) = -finiteEntropy m
    rw [← heq]
    simp only [m, finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hsplit : (∑ i : S, m (f i)) =
      ∑ y, ((S.filter (fun i => f i = y)).card : ℝ) * m y := by
    rw [Finset.sum_coe_sort S (fun i => m (f i))]
    calc
      _ = ∑ i ∈ S, ∑ y, if f i = y then m y else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ y, ∑ i ∈ S, if f i = y then m y else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        rw [← Finset.sum_filter]
        simp
  have hW : (∑ i : S, m (f i)) ≤ L := by
    rw [hsplit]
    calc
      _ ≤ ∑ y, L * m y := by
        apply Finset.sum_le_sum
        intro y _
        have hc : ((S.filter (fun i => f i = y)).card : ℝ) ≤ L := by
          simpa only [S, Finset.filter_filter] using hcard y
        exact mul_le_mul_of_nonneg_right hc (hm.1 y)
      _ = L := by rw [← Finset.mul_sum, hm.2, mul_one]
  have hlog := Real.log_le_log hWpos hW
  rw [hH, hE] at hGibbs
  linarith [hGibbs, hlog]

/-- The finite joint-law occupancy inequality needed to pass from the actual
grid entropy to the entropy of merged block atoms. Each positive atom in a
fixed grid fiber is counted once. -/
theorem finite_joint_entropy_le_marginal_add_log {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {r : ι × κ → ℝ} (hr : ∀ z, 0 ≤ r z) (hr_sum : ∑ z, r z = 1) {L : ℝ}
    (hcard : ∀ y, ((Finset.univ.filter (fun z : ι × κ => 0 < r z ∧ z.2 = y)).card : ℝ) ≤ L) :
    finiteEntropy (fun x => ∑ y, r (x, y)) ≤
      finiteEntropy (fun y => ∑ x, r (x, y)) + Real.log L := by
  have hmerge := finiteEntropy_atomMass_le hr (Prod.fst : ι × κ → ι)
  have hocc := finiteEntropy_le_atomMass_add_log hr hr_sum (Prod.snd : ι × κ → κ) hcard
  have hfst : atomMass r (Prod.fst : ι × κ → ι) = (fun x => ∑ y, r (x, y)) := by
    funext x
    simp only [atomMass, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hbx
      simp [hbx]
    · simp
  have hsnd : atomMass r (Prod.snd : ι × κ → κ) = (fun y => ∑ x, r (x, y)) := by
    funext y
    simp [atomMass, Fintype.sum_prod_type]
  rw [hfst] at hmerge
  rw [hsnd] at hocc
  exact hmerge.trans hocc

/-- Actual singleton masses of a finite probability measure form a finite
probability vector. This is used for the pushforward law of an actual joint variable. -/
theorem finite_measure_singleton_probability {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) [IsProbabilityMeasure ν] :
    (∀ i, 0 ≤ ν.real {i}) ∧ (∑ i, ν.real {i}) = 1 := by
  refine ⟨fun _ => measureReal_nonneg, ?_⟩
  simp

/-- The first marginal of an actual finite joint measure is its row sum. -/
theorem finite_measure_fst_marginal {ι κ : Type*} [Fintype κ]
    [MeasurableSpace ι] [MeasurableSpace κ] [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    (ν : Measure (ι × κ)) [IsFiniteMeasure ν] (x : ι) :
    (Measure.map Prod.fst ν).real {x} = ∑ y, ν.real {(x, y)} := by
  have hmap : (Measure.map Prod.fst ν).real {x} = ν.real (Prod.fst ⁻¹' {x}) := by
    unfold Measure.real
    rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
  rw [hmap]
  have hset : (Prod.fst : ι × κ → ι) ⁻¹' {x} = ⋃ y : κ, {(x, y)} := by
    ext z
    rcases z with ⟨u, v⟩
    simp [eq_comm]
  rw [hset]
  apply measureReal_iUnion_fintype
  · intro y z hyz
    apply Set.disjoint_singleton.mpr
    intro h
    exact hyz (congrArg Prod.snd h)
  · intro y
    exact measurableSet_singleton _
  · intro y
    finiteness

/-- The second marginal of an actual finite joint measure is its column sum. -/
theorem finite_measure_snd_marginal {ι κ : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace κ] [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    (ν : Measure (ι × κ)) [IsFiniteMeasure ν] (y : κ) :
    (Measure.map Prod.snd ν).real {y} = ∑ x, ν.real {(x, y)} := by
  have hmap : (Measure.map Prod.snd ν).real {y} = ν.real (Prod.snd ⁻¹' {y}) := by
    unfold Measure.real
    rw [Measure.map_apply measurable_snd (measurableSet_singleton y)]
  rw [hmap]
  have hset : (Prod.snd : ι × κ → κ) ⁻¹' {y} = ⋃ x : ι, {(x, y)} := by
    ext z
    rcases z with ⟨u, v⟩
    simp [eq_comm]
  rw [hset]
  apply measureReal_iUnion_fintype
  · intro x z hxz
    apply Set.disjoint_singleton.mpr
    intro h
    exact hxz (congrArg Prod.fst h)
  · intro x
    exact measurableSet_singleton _
  · intro x
    finiteness

/-- The occupancy entropy bound for the actual singleton law of a finite
joint probability measure, expressed directly through its pushforward marginals. -/
theorem finite_measure_joint_entropy_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    (ν : Measure (ι × κ)) [IsProbabilityMeasure ν] {L : ℝ}
    (hcard : ∀ y, ((Finset.univ.filter (fun z : ι × κ => 0 < ν.real {z} ∧ z.2 = y)).card : ℝ) ≤ L) :
    finiteEntropy (fun x => (Measure.map Prod.fst ν).real {x}) ≤
      finiteEntropy (fun y => (Measure.map Prod.snd ν).real {y}) + Real.log L := by
  have hp := finite_measure_singleton_probability ν
  have hh := finite_joint_entropy_le_marginal_add_log hp.1 hp.2 hcard
  have hfst : (fun x => ∑ y, ν.real {(x, y)}) = (fun x => (Measure.map Prod.fst ν).real {x}) :=
    funext (fun x => (finite_measure_fst_marginal ν x).symm)
  have hsnd : (fun y => ∑ x, ν.real {(x, y)}) = (fun y => (Measure.map Prod.snd ν).real {y}) :=
    funext (fun y => (finite_measure_snd_marginal ν y).symm)
  rw [hfst, hsnd] at hh
  exact hh

end Salem
