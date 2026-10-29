module

public import Salem.P2GreenIntervals
public import Salem.P1Returns

@[expose] public section

namespace Salem

/-- A certified box for the source's exact odd direct-difference return. -/
def p2ReturnBox : ComplexRationalBox :=
  p2GreenZetaBox.powRounded p2GreenGrid 1846082221

/-- These rational comparisons execute the complete rounded power inside the
Lean kernel; they are not assumptions imported from the verification archive. -/
lemma p2ReturnBox_bounds :
    (1 - 1 / 10 ^ 18 : ℚ) ≤ p2ReturnBox.re.lo ∧
    p2ReturnBox.re.hi ≤ (1 + 1 / 10 ^ 18 : ℚ) ∧
    (-23649999999 / 10 ^ 20 : ℚ) ≤ p2ReturnBox.im.lo ∧
    p2ReturnBox.im.hi ≤ (23649999999 / 10 ^ 20 : ℚ) ∧
    p2ReturnBox.re.hi < 1 := by
  decide +kernel

/-- The actual P₂ unit-root return required by the odd direct difference. -/
lemma p2_return_bound_1846082221 :
    0 < ‖1 - p2CoefficientZeta ^ 1846082221‖ ∧
      ‖1 - p2CoefficientZeta ^ 1846082221‖ < (2365 / 10 ^ 13 : ℝ) := by
  have hbox := ComplexRationalBox.powRounded_contains p2GreenGrid_pos
    p2GreenZetaBox_contains 1846082221
  change p2ReturnBox.Contains (p2CoefficientZeta ^ 1846082221) at hbox
  constructor
  · apply norm_pos_iff.mpr
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    have hhi : (p2ReturnBox.re.hi : ℝ) < 1 := by exact_mod_cast p2ReturnBox_bounds.2.2.2.2
    linarith [hbox.1.2]
  · apply complexBox_norm_one_sub_lt hbox (a := (1 / 10 ^ 18 : ℝ))
      (b := (23649999999 / 10 ^ 20 : ℝ))
    · norm_num
    · norm_num
    · norm_num
    · have h : ((1 - 1 / 10 ^ 18 : ℚ) : ℝ) ≤ ((p2ReturnBox.re.lo : ℚ) : ℝ) := Rat.cast_le.mpr p2ReturnBox_bounds.1
      norm_num at h ⊢
      exact h
    · have h : ((p2ReturnBox.re.hi : ℚ) : ℝ) ≤ ((1 + 1 / 10 ^ 18 : ℚ) : ℝ) := Rat.cast_le.mpr p2ReturnBox_bounds.2.1
      norm_num at h ⊢
      exact h
    · have h : ((-23649999999 / 10 ^ 20 : ℚ) : ℝ) ≤ ((p2ReturnBox.im.lo : ℚ) : ℝ) := Rat.cast_le.mpr p2ReturnBox_bounds.2.2.1
      norm_num at h ⊢
      exact h
    · have h : ((p2ReturnBox.im.hi : ℚ) : ℝ) ≤ ((23649999999 / 10 ^ 20 : ℚ) : ℝ) := Rat.cast_le.mpr p2ReturnBox_bounds.2.2.2.1
      norm_num at h ⊢
      exact h
    · norm_num

end Salem
