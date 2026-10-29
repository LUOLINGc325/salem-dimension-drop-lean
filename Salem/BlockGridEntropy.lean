module

public import Salem.EntropyCover
public import Salem.AtomSeparation
public import Salem.GridEntropy
public import Salem.ElementaryGeneric

@[expose] public section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set Polynomial

namespace Salem

/-- The actual iid fair Boolean process used for the coupled prefix and infinite series. -/
noncomputable def fairSignProcess : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => fairBoolMeasure)

instance : IsProbabilityMeasure fairSignProcess := by
  unfold fairSignProcess
  infer_instance

noncomputable def signAlphabetSeries (β : ℝ) : (ℕ → Bool) → ℝ :=
  alphabetSeries fairSignDigit β⁻¹

noncomputable def signSeriesLaw (β : ℝ) : Measure ℝ :=
  fairSignProcess.map (signAlphabetSeries β)

instance (β : ℝ) : IsProbabilityMeasure (signSeriesLaw β) := by
  unfold signSeriesLaw
  infer_instance

noncomputable def signSupportRadius (β : ℝ) : ℝ := (1 - β⁻¹)⁻¹

theorem signSupportRadius_pos {β : ℝ} (hβ : 1 < β) : 0 < signSupportRadius β := by
  exact inv_pos.2 (sub_pos.2 (inv_lt_one_of_one_lt₀ hβ))

theorem measurable_signAlphabetSeries (β : ℝ) : Measurable (signAlphabetSeries β) :=
  measurable_alphabetSeries fairSignDigit β⁻¹

theorem abs_signAlphabetSeries_le {β : ℝ} (hβ : 1 < β) (ω : ℕ → Bool) :
    |signAlphabetSeries β ω| ≤ signSupportRadius β := by
  have hω : ∀ j, |fairSignDigit (ω j)| = 1 := by
    intro j
    cases ω j <;> norm_num [fairSignDigit]
  exact ElementaryCore.abs_bernoulliSeries_le β hβ (fun j => fairSignDigit (ω j)) hω

theorem ae_signSeriesLaw_support {β : ℝ} (hβ : 1 < β) :
    ∀ᵐ x ∂signSeriesLaw β, x ∈ Icc (-signSupportRadius β) (signSupportRadius β) := by
  unfold signSeriesLaw
  apply (ae_map_iff (measurable_signAlphabetSeries β).aemeasurable
    (show MeasurableSet {x : ℝ | x ∈ Icc (-signSupportRadius β) (signSupportRadius β)} from
      measurableSet_Icc)).2
  exact Filter.Eventually.of_forall (fun ω => abs_le.1 (abs_signAlphabetSeries_le hβ ω))

/-- The finite initial word in the same infinite process. -/
def prefixWord (N : ℕ) (ω : ℕ → Bool) (j : Fin N) : Bool := ω j

theorem measurable_prefixWord (N : ℕ) : Measurable (prefixWord N) :=
  Measurable.of_eval (fun j => measurable_pi_apply (j : ℕ))

/-- The canonical merged prefix atom, without retaining a word multiplicity. -/
noncomputable def mergedSignPrefix (β : ℝ) (N : ℕ) (ω : ℕ → Bool) :
    alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) :=
  mergeLetter (alphabetPrefix fairSignDigit β⁻¹ N) (prefixWord N ω)

theorem measurable_mergedSignPrefix (β : ℝ) (N : ℕ) : Measurable (mergedSignPrefix β N) :=
  (measurable_of_countable (mergeLetter (alphabetPrefix fairSignDigit β⁻¹ N))).comp
    (measurable_prefixWord N)

/-- The exact finite initial word has the finite product law. -/
theorem map_prefixWord (N : ℕ) :
    fairSignProcess.map (prefixWord N) = Measure.pi (fun _ : Fin N => fairBoolMeasure) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => fairBoolMeasure) (f := fun j : Fin N => (j : ℕ)) Fin.val_injective
  change (Measure.infinitePi (fun _ : ℕ => fairBoolMeasure)).map
    (fun ω : ℕ → Bool => fun j : Fin N => ω j) = _
  simpa only [Measure.infinitePi_eq_pi] using h

theorem map_mergedSignPrefix (β : ℝ) (N : ℕ) :
    fairSignProcess.map (mergedSignPrefix β N) =
      (Measure.pi (fun _ : Fin N => fairBoolMeasure)).map
        (mergeLetter (alphabetPrefix fairSignDigit β⁻¹ N)) := by
  rw [← map_prefixWord N,
    Measure.map_map (measurable_of_countable (mergeLetter (alphabetPrefix fairSignDigit β⁻¹ N)))
      (measurable_prefixWord N)]
  rfl

/-- The actual prefix marginal is precisely the explicitly computed merged block mass. -/
theorem mergedSignPrefix_singleton_probability (β : ℝ) (N : ℕ)
    (x : alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N)) :
    (fairSignProcess.map (mergedSignPrefix β N)).real {x} =
      finiteBlockAtomProbability fairBoolMeasure fairSignDigit β⁻¹ N x := by
  rw [map_mergedSignPrefix, finiteBlockAtomProbability_eq_singleton]

/-- The sharp sign tail bound keeps the source separation constant unchanged. -/
theorem abs_signAlphabetSeries_sub_mergedPrefix_le {β : ℝ} (hβ : 1 < β)
    (N : ℕ) (ω : ℕ → Bool) :
    |signAlphabetSeries β ω - (mergedSignPrefix β N ω : ℝ)| ≤
      signSupportRadius β * β⁻¹ ^ N := by
  have hω : ∀ j, |fairSignDigit (ω j)| = 1 := by
    intro j
    cases ω j <;> norm_num [fairSignDigit]
  have h := ElementaryCore.abs_bernoulliSeries_sub_partialSum_le β hβ
    (fun j => fairSignDigit (ω j)) hω N
  change |signAlphabetSeries β ω - ∑ j : Fin N, fairSignDigit (ω j) * β⁻¹ ^ (j : ℕ)| ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun j => fairSignDigit (ω j) * β⁻¹ ^ j) N]
  exact h

/-- The actual floor-grid index, in the explicit finite index set supplied by the support bound. -/
noncomputable def signGridIndex (β : ℝ) (hβ : 1 < β) (N : ℕ) (ω : ℕ → Bool) :
    gridIndexSet (signSupportRadius β) (β⁻¹ ^ N) :=
  ⟨⌊signAlphabetSeries β ω / (β⁻¹ ^ N)⌋,
    floor_mem_gridIndexSet (pow_pos (inv_pos.2 (by linarith : 0 < β)) N)
      (abs_le.1 (abs_signAlphabetSeries_le hβ ω))⟩

theorem measurable_signGridIndex (β : ℝ) (hβ : 1 < β) (N : ℕ) :
    Measurable (signGridIndex β hβ N) := by
  apply Measurable.subtype_mk
  exact Int.measurable_floor.comp ((measurable_signAlphabetSeries β).div_const _)

theorem signAlphabetSeries_mem_gridCell {β : ℝ} (hβ : 1 < β) (N : ℕ) (ω : ℕ → Bool) :
    signAlphabetSeries β ω ∈ gridCell (β⁻¹ ^ N) (signGridIndex β hβ N ω) := by
  rw [gridCell_eq_floor_fiber (pow_pos (inv_pos.2 (by linarith : 0 < β)) N)]
  rfl

/-- The grid marginal is the actual cell mass of the infinite series law. -/
theorem signGridIndex_singleton_probability {β : ℝ} (hβ : 1 < β) (N : ℕ)
    (k : gridIndexSet (signSupportRadius β) (β⁻¹ ^ N)) :
    (fairSignProcess.map (signGridIndex β hβ N)).real {k} = gridMass (signSeriesLaw β) (β⁻¹ ^ N) k := by
  rw [map_measureReal_apply (measurable_signGridIndex β hβ N) (measurableSet_singleton k),
    gridMass, signSeriesLaw,
    map_measureReal_apply (measurable_signAlphabetSeries β)
      (show MeasurableSet (gridCell (β⁻¹ ^ N) k) from measurableSet_Ico),
    gridCell_eq_floor_fiber (pow_pos (inv_pos.2 (by linarith : 0 < β)) N)]
  congr 1
  ext ω
  simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff, signGridIndex, mem_ofPred_eq]

/-- The Boolean realization is exactly the paper's actual real-sign series law. -/
theorem signSeriesLaw_eq_bernoulliLaw (β : ℝ) :
    signSeriesLaw β = ElementaryCore.bernoulliLaw β := by
  have h := map_alphabetSeries_realDigits fairBoolMeasure fairSignDigit β⁻¹
  rw [map_fairBoolMeasure_fairSignDigit] at h
  unfold signSeriesLaw fairSignProcess signAlphabetSeries ElementaryCore.bernoulliLaw
    ElementaryCore.signProcess ElementaryCore.signMeasure ElementaryCore.bernoulliSeries
  exact h.symm

/-- The concrete coupled prefix/grid variable on the actual iid sign sequence. -/
noncomputable def signBlockGridPair (β : ℝ) (hβ : 1 < β) (N : ℕ) (ω : ℕ → Bool) :
    alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) ×
      gridIndexSet (signSupportRadius β) (β⁻¹ ^ N) :=
  (mergedSignPrefix β N ω, signGridIndex β hβ N ω)

theorem measurable_signBlockGridPair (β : ℝ) (hβ : 1 < β) (N : ℕ) :
    Measurable (signBlockGridPair β hβ N) :=
  (measurable_mergedSignPrefix β N).prodMk (measurable_signGridIndex β hβ N)

/-- The actual joint probability measure of the canonical finite prefix and infinite-series grid. -/
noncomputable def signBlockGridJoint (β : ℝ) (hβ : 1 < β) (N : ℕ) :
    Measure (alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) ×
      gridIndexSet (signSupportRadius β) (β⁻¹ ^ N)) :=
  fairSignProcess.map (signBlockGridPair β hβ N)

instance (β : ℝ) (hβ : 1 < β) (N : ℕ) : IsProbabilityMeasure (signBlockGridJoint β hβ N) := by
  unfold signBlockGridJoint
  infer_instance

theorem map_fst_signBlockGridJoint (β : ℝ) (hβ : 1 < β) (N : ℕ) :
    (signBlockGridJoint β hβ N).map Prod.fst = fairSignProcess.map (mergedSignPrefix β N) := by
  rw [signBlockGridJoint, Measure.map_map measurable_fst (measurable_signBlockGridPair β hβ N)]
  rfl

theorem map_snd_signBlockGridJoint (β : ℝ) (hβ : 1 < β) (N : ℕ) :
    (signBlockGridJoint β hβ N).map Prod.snd = fairSignProcess.map (signGridIndex β hβ N) := by
  rw [signBlockGridJoint, Measure.map_map measurable_snd (measurable_signBlockGridPair β hβ N)]
  rfl

/-- A positive joint atom is realized by a sequence, so its finite prefix lies in the sharp window. -/
theorem positive_signBlockGridJoint_mem_window {β : ℝ} (hβ : 1 < β) (N : ℕ)
    (z : alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) ×
      gridIndexSet (signSupportRadius β) (β⁻¹ ^ N))
    (hz : 0 < (signBlockGridJoint β hβ N).real {z}) :
    (z.1 : ℝ) ∈ finiteSignAtomsInInterval β N
      (β⁻¹ ^ N * ((z.2 : ℤ) - signSupportRadius β))
      (β⁻¹ ^ N * ((z.2 : ℤ) + 1 + signSupportRadius β)) := by
  classical
  have hpre : fairSignProcess ((signBlockGridPair β hβ N) ⁻¹' {z}) ≠ 0 := by
    intro hzero
    have hzero' : (signBlockGridJoint β hβ N).real {z} = 0 := by
      rw [signBlockGridJoint,
        map_measureReal_apply (measurable_signBlockGridPair β hβ N) (measurableSet_singleton z),
        Measure.real, hzero, ENNReal.toReal_zero]
    exact (ne_of_gt hz) hzero'
  rcases nonempty_of_measure_ne_zero hpre with ⟨ω, hω⟩
  change signBlockGridPair β hβ N ω = z at hω
  have hx := congrArg Prod.fst hω
  have hk := congrArg Prod.snd hω
  change mergedSignPrefix β N ω = z.1 at hx
  change signGridIndex β hβ N ω = z.2 at hk
  have hwin := prefix_mem_window_of_cell_and_tail (signAlphabetSeries_mem_gridCell hβ N ω)
    (abs_signAlphabetSeries_sub_mergedPrefix_le hβ N ω)
  rw [hx, hk] at hwin
  apply Finset.mem_filter.2
  exact ⟨z.1.property, hwin⟩

theorem atomSeparationConstant_pos {β R : ℝ} (hβ : 1 < β) (hR : 0 ≤ R) :
    0 < atomSeparationConstant β R := by
  unfold atomSeparationConstant
  have hden : 0 < 2 * (β - 1) := by nlinarith
  positivity

section QuarticBlockGrid

variable (P : ℤ[X]) (hPmonic : P.Monic) (hdegree : P.natDegree = 4)
  (hPirr : Irreducible (P.map (Int.castRingHom ℚ)))
  {β : ℝ} (hβ : 1 < β) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζim : ζ.im ≠ 0)
  (hβroot : (P.map (Int.castRingHom ℂ)).IsRoot (β : ℂ))
  (hβinvroot : (P.map (Int.castRingHom ℂ)).IsRoot ((β⁻¹ : ℝ) : ℂ))
  (hζroot : (P.map (Int.castRingHom ℂ)).IsRoot ζ)
  (hstarroot : (P.map (Int.castRingHom ℂ)).IsRoot (star ζ))

include hPmonic hdegree hPirr hβ hζ hζim hβroot hβinvroot hζroot hstarroot

/-- The positive atoms in each fiber of the actual joint law satisfy the source occupancy bound. -/
theorem signBlockGridJoint_fiber_card_le {N : ℕ} (hN : 0 < N)
    (y : gridIndexSet (signSupportRadius β) (β⁻¹ ^ N)) :
    ((Finset.univ.filter (fun z : alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) ×
      gridIndexSet (signSupportRadius β) (β⁻¹ ^ N) =>
      0 < (signBlockGridJoint β hβ N).real {z} ∧ z.2 = y)).card : ℝ) ≤
      atomSeparationConstant β (signSupportRadius β) * (N : ℝ) ^ 2 := by
  classical
  let T := Finset.univ.filter (fun z : alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) ×
      gridIndexSet (signSupportRadius β) (β⁻¹ ^ N) =>
    0 < (signBlockGridJoint β hβ N).real {z} ∧ z.2 = y)
  let W := finiteSignAtomsInInterval β N
    (β⁻¹ ^ N * ((y : ℤ) - signSupportRadius β))
    (β⁻¹ ^ N * ((y : ℤ) + 1 + signSupportRadius β))
  let f : (alphabetValues (alphabetPrefix fairSignDigit β⁻¹ N) ×
      gridIndexSet (signSupportRadius β) (β⁻¹ ^ N)) → ℝ := fun z => z.1
  have hmap : Set.MapsTo f (T : Set _) (W : Set ℝ) := by
    intro z hz
    have hh := (Finset.mem_filter.1 hz).2
    have hw := positive_signBlockGridJoint_mem_window hβ N z hh.1
    simpa only [f, W, hh.2, Finset.mem_coe] using hw
  have hinj : Set.InjOn f (T : Set _) := by
    intro z hz z' hz' hval
    apply Prod.ext (Subtype.ext hval)
    exact (Finset.mem_filter.1 hz).2.2.trans ((Finset.mem_filter.1 hz').2.2.symm)
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  have hbound := card_finiteSignAtoms_gridWindow_le P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot hN (signSupportRadius_pos hβ).le ((y : ℤ) : ℝ)
  exact (Nat.cast_le.2 hcard).trans hbound

/-- The actual merged block entropy is bounded by the actual infinite-series grid entropy. -/
theorem signBlockEntropy_le_gridEntropy_add_log {N : ℕ} (hN : 0 < N) :
    signBlockEntropy β N ≤
      finiteEntropy (fun k : gridIndexSet (signSupportRadius β) (β⁻¹ ^ N) =>
        gridMass (signSeriesLaw β) (β⁻¹ ^ N) k) +
      Real.log (atomSeparationConstant β (signSupportRadius β) * (N : ℝ) ^ 2) := by
  classical
  have h := finite_measure_joint_entropy_bound (signBlockGridJoint β hβ N)
    (signBlockGridJoint_fiber_card_le P hPmonic hdegree hPirr hβ ζ hζ hζim
      hβroot hβinvroot hζroot hstarroot hN)
  rw [map_fst_signBlockGridJoint, map_snd_signBlockGridJoint] at h
  simp_rw [mergedSignPrefix_singleton_probability, signGridIndex_singleton_probability] at h
  exact h

/-- The paper's exact `2 log N + log C_sep` penalty, derived from the actual joint law. -/
theorem signBlockEntropy_le_gridEntropy {N : ℕ} (hN : 0 < N) :
    signBlockEntropy β N ≤
      finiteEntropy (fun k : gridIndexSet (signSupportRadius β) (β⁻¹ ^ N) =>
        gridMass (signSeriesLaw β) (β⁻¹ ^ N) k) + 2 * Real.log N +
      Real.log (atomSeparationConstant β (signSupportRadius β)) := by
  have h := signBlockEntropy_le_gridEntropy_add_log P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hC := atomSeparationConstant_pos hβ (signSupportRadius_pos hβ).le
  rw [Real.log_mul hC.ne' (pow_pos hNpos 2).ne', Real.log_pow] at h
  linarith

/-- The paper's Fourier-to-block-entropy estimate for the actual Bernoulli sign law.
The finite entropy, joint law, cell probabilities, and algebraic occupancy are all constructed. -/
theorem signBlockEntropy_fourier_bound {a Q : ℝ} {ξ : ℕ → ℝ} (n N : ℕ) (hN : 0 < N)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) (hscale : β⁻¹ ^ N * ξ n ≤ 1)
    (hfourier : ∀ i ≤ n, a ≤ |∫ x, Real.cos (ξ i * x) ∂ElementaryCore.bernoulliLaw β|) :
    signBlockEntropy β N ≤
      (N : ℝ) * Real.log β - (n + 1 : ℕ) * fourierBiasGain a + 2 * Real.log N +
      Real.log ((2 * signSupportRadius β + 2 + 2 * a /
        (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))) *
          atomSeparationConstant β (signSupportRadius β)) +
      a * Q / ((1 - a) * (Q - 1)) := by
  have hprefix := signBlockEntropy_le_gridEntropy P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot hN
  have hgrid := lacunary_gridEntropy_bound_at_scale (signSeriesLaw β) n N
    (signSupportRadius_pos hβ).le hβ (ae_signSeriesLaw_support hβ)
    ha ha2 hQ hξ₀ hgap hscale (by simpa only [signSeriesLaw_eq_bernoulliLaw] using hfourier)
  have hC := atomSeparationConstant_pos hβ (signSupportRadius_pos hβ).le
  have hQpos : 0 < Q := by linarith
  have hCQ : 0 < (Q - 2) / (Q - 1) := div_pos (by linarith) (by linarith)
  have hlast : 0 < 1 - (1 + a) / Q := by
    have hratio : (1 + a) / Q < 1 := (div_lt_iff₀ hQpos).2 (by linarith)
    linarith
  have hD : 0 ≤ 2 * a /
      (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) :=
    div_nonneg (mul_nonneg (by norm_num) ha)
      (mul_nonneg (mul_nonneg Real.pi_pos.le hCQ.le) hlast.le)
  have hZ : 0 < 2 * signSupportRadius β + 2 + 2 * a /
      (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) := by
    linarith [signSupportRadius_pos hβ]
  rw [Real.log_mul hZ.ne' hC.ne']
  linarith

/-- The explicit quadratic Fourier version of the actual source entropy criterion. -/
theorem signBlockEntropy_fourier_bound_quadratic {a Q : ℝ} {ξ : ℕ → ℝ}
    (n N : ℕ) (hN : 0 < N)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) (hscale : β⁻¹ ^ N * ξ n ≤ 1)
    (hfourier : ∀ i ≤ n, a ≤ |∫ x, Real.cos (ξ i * x) ∂ElementaryCore.bernoulliLaw β|) :
    signBlockEntropy β N ≤
      (N : ℝ) * Real.log β - (1 / 2 : ℝ) * (n + 1 : ℕ) * a ^ 2 + 2 * Real.log N +
      Real.log ((2 * signSupportRadius β + 2 + 2 * a /
        (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))) *
          atomSeparationConstant β (signSupportRadius β)) +
      a * Q / ((1 - a) * (Q - 1)) := by
  have h := signBlockEntropy_fourier_bound P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot n N hN ha ha2 hQ hξ₀ hgap hscale hfourier
  have hgain := half_sq_le_fourierBiasGain ha (by linarith : a < 1)
  have hmul := mul_le_mul_of_nonneg_left hgain (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
  nlinarith

end QuarticBlockGrid

end Salem
