module

public import Salem.QuarticClassificationCore
public import Salem.ElementaryGeneric

@[expose] public section

open scoped ENNReal
open MeasureTheory Set

namespace Salem

/-- The actual geometric sign attractor gives strict dimension drop above two. -/
theorem elementary_fullMass_dim_drop {β : ℝ} (hβ : 2 < β) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw β F = 1 ∧ dimH F < 1 := by
  have hb : 1 < β := by linarith
  have hlog : Real.log 2 < Real.log β := Real.log_lt_log (by norm_num) hβ
  have hlogpos : 0 < Real.log β := Real.log_pos hb
  have hratio : Real.log 2 / Real.log β < 1 := (div_lt_iff₀ hlogpos).2 (by simpa using hlog)
  refine ⟨ElementaryCore.signAttractor β, ElementaryCore.measurableSet_signAttractor β,
    ElementaryCore.bernoulliLaw_signAttractor β hb,
    (ElementaryCore.dimH_signAttractor_le β hb).trans_lt ?_⟩
  have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hratio
  simpa only [ENNReal.ofReal_one] using h

/-- Classification, exclusion of two, and the actual elementary attractor reduce every
quartic Salem parameter to two explicit full-mass covers. Both cover obligations stay explicit. -/
theorem quartic_fullMass_dim_drop_of_two_covers
    (h1 : ∃ F : Set ℝ, MeasurableSet F ∧
      ElementaryCore.bernoulliLaw QuarticCore.beta1 F = 1 ∧ dimH F < 1)
    (h2 : ∃ F : Set ℝ, MeasurableSet F ∧
      ElementaryCore.bernoulliLaw QuarticCore.beta2 F = 1 ∧ dimH F < 1)
    {β : ℝ} (hquartic : QuarticCore.IsQuarticSalemNumber β) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw β F = 1 ∧ dimH F < 1 := by
  by_cases hlt : β < 2
  · rcases QuarticCore.quartic_classification_in_one_two hquartic hlt with h | h
    · rw [h]
      exact h1
    · rw [h]
      exact h2
  · have hne := QuarticCore.quartic_ne_two hquartic
    have hgt : 2 < β := by rcases lt_trichotomy β 2 with h | h | h <;> tauto
    exact elementary_fullMass_dim_drop hgt

end Salem
