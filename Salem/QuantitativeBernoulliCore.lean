module

public import Salem.QuantitativeEntropy
public import Salem.QuantitativeRootCore

@[expose] public section

open MeasureTheory

namespace Salem.QuarticCore

/-- The first literal source parameter has the stated quantitative full-mass
cover once its actual uniform finite Fourier input is supplied. The quartic
root-pattern premise is definitionally the frozen nonvacuity guard. -/
theorem exists_quantitative_beta1_cover_of_uniform_bias
    (hquartic : IsQuarticSalemNumber beta1) {c : ℝ}
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1)
    (hfourier : ∀ k ≤ (2 * 10 ^ 25 : ℕ), (3 / (4 * 10 ^ 11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi * |c| * beta1 ^ k) * x) ∂ElementaryCore.bernoulliLaw beta1|) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw beta1 F = 1 ∧
      dimH F < ENNReal.ofReal (1 - (14 : ℝ) / 10 ^ 24) := by
  rcases hquartic with ⟨P, ζ, hmonic, hdegree, hirr, _, hβroot, hβinvroot,
    hζroot, hstarroot, hnorm, him, _⟩
  simp only [algebraMap_int_eq] at hirr hβroot hβinvroot hζroot hstarroot
  exact Salem.exists_quantitative_cover_1_of_uniform_bias P hmonic hdegree hirr
    beta1_gt_five_thirds ζ hnorm him hβroot (by simpa only [Complex.ofReal_inv, algebraMap_int_eq] using hβinvroot) hζroot hstarroot hc hc1
    log_beta1_lt_eleven_twentieths.le hfourier

/-- The second literal source parameter has the stated quantitative full-mass
cover once its actual uniform finite Fourier input is supplied. The quartic
root-pattern premise is definitionally the frozen nonvacuity guard. -/
theorem exists_quantitative_beta2_cover_of_uniform_bias
    (hquartic : IsQuarticSalemNumber beta2) {c : ℝ}
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1)
    (hfourier : ∀ k ≤ (10 ^ 26 : ℕ), (9 / (2 * 10 ^ 11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi * |c| * beta2 ^ k) * x) ∂ElementaryCore.bernoulliLaw beta2|) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw beta2 F = 1 ∧
      dimH F < ENNReal.ofReal (1 - (78 : ℝ) / 10 ^ 23) := by
  rcases hquartic with ⟨P, ζ, hmonic, hdegree, hirr, _, hβroot, hβinvroot,
    hζroot, hstarroot, hnorm, him, _⟩
  simp only [algebraMap_int_eq] at hirr hβroot hβinvroot hζroot hstarroot
  exact Salem.exists_quantitative_cover_2_of_uniform_bias P hmonic hdegree hirr
    beta2_gt_five_thirds ζ hnorm him hβroot (by simpa only [Complex.ofReal_inv, algebraMap_int_eq] using hβinvroot) hζroot hstarroot hc hc1
    log_beta2_lt_sixteen_twentyfifths.le hfourier

end Salem.QuarticCore
