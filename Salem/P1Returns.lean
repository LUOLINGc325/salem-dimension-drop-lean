module

public import Salem.RationalIntervals

@[expose] public section

namespace Salem
/-- The upper-half-plane unit conjugate for P1, given by the appendix's
exact radical coordinates. -/
noncomputable def p1NeutralRoot : ℂ :=
  let re : ℝ := (1 - Real.sqrt 13) / 4
  ⟨re, Real.sqrt (1 - re ^ 2)⟩
theorem p1NeutralRoot_re_bounds :
    (-651387818865997323279805316867623986562824143461311553177614 / 10 ^ 60 : ℝ) ≤
      p1NeutralRoot.re ∧
    p1NeutralRoot.re ≤
      (-651387818865997323279805316867623986562824143461311553177613 / 10 ^ 60 : ℝ) := by
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have hs0 : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
  have hsl : (3605551275463989293119221267470495946251296573845246212710453 / 10 ^ 60 : ℝ) ≤
      Real.sqrt 13 := by nlinarith
  have hsu : (Real.sqrt 13 : ℝ) ≤
      (3605551275463989293119221267470495946251296573845246212710454 / 10 ^ 60 : ℝ) := by nlinarith
  dsimp [p1NeutralRoot]
  constructor <;> linarith
theorem p1NeutralRoot_re_sq_bounds :
    (651387818865997323279805316867623986562824143461311553177613 / 10 ^ 60 : ℝ) ^ 2 ≤
      p1NeutralRoot.re ^ 2 ∧
    p1NeutralRoot.re ^ 2 ≤
      (651387818865997323279805316867623986562824143461311553177614 / 10 ^ 60 : ℝ) ^ 2 := by
  have h := p1NeutralRoot_re_bounds
  constructor
  · have h' := pow_le_pow_left₀
      (by norm_num : (0 : ℝ) ≤ 651387818865997323279805316867623986562824143461311553177613 / 10 ^ 60)
      (show (651387818865997323279805316867623986562824143461311553177613 / 10 ^ 60 : ℝ) ≤
        -p1NeutralRoot.re by linarith [h.2]) 2
    simpa only [neg_sq] using h'
  · have h' := pow_le_pow_left₀ (show (0 : ℝ) ≤ -p1NeutralRoot.re by linarith [h.2])
      (show -p1NeutralRoot.re ≤
        (651387818865997323279805316867623986562824143461311553177614 / 10 ^ 60 : ℝ) by linarith [h.1]) 2
    simpa only [neg_sq] using h'
theorem p1NeutralRoot_im_sq : p1NeutralRoot.im ^ 2 = 1 - p1NeutralRoot.re ^ 2 := by
  have hp : 0 ≤ 1 - p1NeutralRoot.re ^ 2 := by
    nlinarith [(p1NeutralRoot_re_sq_bounds).2]
  exact Real.sq_sqrt hp
theorem p1NeutralRoot_im_bounds :
    (758744956775989820904814328865157013369150563327647208852797 / 10 ^ 60 : ℝ) ≤
      p1NeutralRoot.im ∧
    p1NeutralRoot.im ≤
      (758744956775989820904814328865157013369150563327647208852802 / 10 ^ 60 : ℝ) := by
  have hi := p1NeutralRoot_im_sq
  have hi0 : 0 ≤ p1NeutralRoot.im := Real.sqrt_nonneg _
  have hrl := p1NeutralRoot_re_sq_bounds.1
  have hru := p1NeutralRoot_re_sq_bounds.2
  constructor <;> nlinarith
theorem p1NeutralRoot_norm : ‖p1NeutralRoot‖ = 1 := by
  have hs : ‖p1NeutralRoot‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [p1NeutralRoot_im_sq]
  nlinarith [norm_nonneg p1NeutralRoot]
theorem p1NeutralRoot_quartic :
    p1NeutralRoot ^ 4 - p1NeutralRoot ^ 3 - p1NeutralRoot ^ 2 - p1NeutralRoot + 1 = 0 := by
  let v : ℂ := ((2 * p1NeutralRoot.re : ℝ) : ℂ)
  have hvR : (2 * p1NeutralRoot.re) ^ 2 - (2 * p1NeutralRoot.re) - 3 = 0 := by
    dsimp [p1NeutralRoot]
    have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
    nlinarith
  have hv : v ^ 2 - v - 3 = 0 := by
    dsimp [v]
    exact_mod_cast hvR
  have hq : p1NeutralRoot ^ 2 - v * p1NeutralRoot + 1 = 0 := by
    apply Complex.ext
    · simp [v, pow_two]
      nlinarith [p1NeutralRoot_im_sq]
    · simp [v, pow_two]
      ring
  calc
    _ = (p1NeutralRoot ^ 2 - v * p1NeutralRoot + 1) *
          (p1NeutralRoot ^ 2 + (v - 1) * p1NeutralRoot + 1) +
          (v ^ 2 - v - 3) * p1NeutralRoot ^ 2 := by ring
    _ = 0 := by rw [hq, hv]; ring

/-- Rational input box for the exact P1 neutral root. -/
def p1NeutralRootBox : ComplexRationalBox :=
  ⟨⟨-651387818865997323279805316867623986562824143461311553177614 / 10 ^ 60,
      -651387818865997323279805316867623986562824143461311553177613 / 10 ^ 60⟩,
    ⟨758744956775989820904814328865157013369150563327647208852797 / 10 ^ 60,
      758744956775989820904814328865157013369150563327647208852802 / 10 ^ 60⟩⟩

/-- The input intervals contain the actual radical root. -/
theorem p1NeutralRootBox_contains : p1NeutralRootBox.Contains p1NeutralRoot := by
  have hr := p1NeutralRoot_re_bounds
  have hi := p1NeutralRoot_im_bounds
  norm_num [p1NeutralRootBox, ComplexRationalBox.Contains, RationalInterval.Contains] at *
  exact ⟨hr, hi⟩

/-- A compact constructor for explicit outward-rounded return boxes. -/
def p1ReturnGridBox (a b c d : ℤ) : ComplexRationalBox :=
  ⟨⟨(a : ℚ) / 10 ^ 40, (b : ℚ) / 10 ^ 40⟩, ⟨(c : ℚ) / 10 ^ 40, (d : ℚ) / 10 ^ 40⟩⟩
/-- The entire rounded binary-power computation is checked by the Lean
kernel.  No program output is accepted as a proof oracle. -/
theorem p1Return124_eval : p1NeutralRootBox.powRounded (10 ^ 40) 124 =
    p1ReturnGridBox 9999968591563405966257249679344777742424 9999968591563405966257249679344777743766 25063274833724055334364491992518395596 25063274833724055334364491992518396935 := by
  decide +kernel
/-- Kernel-checked exact binary-power output for the long P1 delay. -/
theorem p1Return489637838_eval : p1NeutralRootBox.powRounded (10 ^ 40) 489637838 =
    p1ReturnGridBox 9999999999999999930253135316921403575302 9999999999999999930253135421339635797587 37348859321502594072412352026004 37348859321502594176830584248288 := by
  decide +kernel
theorem complexBox_norm_one_sub_pos {I : ComplexRationalBox} {z : ℂ}
    (hz : I.Contains z) (him : 0 < (I.im.lo : ℝ)) : 0 < ‖1 - z‖ := by
  apply norm_pos_iff.mpr
  intro heq
  have hi := congrArg Complex.im heq
  simp only [Complex.sub_im, Complex.one_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
  have hpos := him.trans_le hz.2.1
  linarith
theorem complexBox_norm_one_sub_lt {I : ComplexRationalBox} {z : ℂ} {a b ε : ℝ}
    (hz : I.Contains z) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε)
    (hrelo : 1 - a ≤ (I.re.lo : ℝ)) (hrehi : (I.re.hi : ℝ) ≤ 1 + a)
    (himlo : -b ≤ (I.im.lo : ℝ)) (himhi : (I.im.hi : ℝ) ≤ b)
    (hs : a ^ 2 + b ^ 2 < ε ^ 2) : ‖1 - z‖ < ε := by
  have hx : |(1 - z).re| ≤ a := by
    apply abs_le.mpr
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hz.1.1, hz.1.2]
  have hy : |(1 - z).im| ≤ b := by
    apply abs_le.mpr
    simp only [Complex.sub_im, Complex.one_im]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hx2 := (sq_le_sq₀ (abs_nonneg (1 - z).re) ha).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg (1 - z).im) hb).mpr hy
  simp only [sq_abs] at hx2 hy2
  have hnorm : ‖1 - z‖ ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg (1 - z)]
/-- The first actual P1 unit-circle return, including its nonvanishing. -/
theorem p1_return_bound_124 : 0 < ‖1 - p1NeutralRoot ^ 124‖ ∧
    ‖1 - p1NeutralRoot ^ 124‖ < (2507 / 10 ^ 6 : ℝ) := by
  have hbox := ComplexRationalBox.powRounded_contains
    (by norm_num : 0 < (10 ^ 40 : ℕ)) p1NeutralRootBox_contains 124
  rw [p1Return124_eval] at hbox
  constructor
  · apply complexBox_norm_one_sub_pos hbox
    norm_num [p1ReturnGridBox]
  · apply complexBox_norm_one_sub_lt hbox (a := (4 / 10 ^ 6 : ℝ))
      (b := (25064 / 10 ^ 7 : ℝ)) <;> norm_num [p1ReturnGridBox]
/-- The second actual P1 unit-circle return.  Its enormous exponent is
handled by a proved binary interval computation inside Lean. -/
theorem p1_return_bound_489637838 : 0 < ‖1 - p1NeutralRoot ^ 489637838‖ ∧
    ‖1 - p1NeutralRoot ^ 489637838‖ < (3736 / 10 ^ 12 : ℝ) := by
  have hbox := ComplexRationalBox.powRounded_contains
    (by norm_num : 0 < (10 ^ 40 : ℕ)) p1NeutralRootBox_contains 489637838
  rw [p1Return489637838_eval] at hbox
  constructor
  · apply complexBox_norm_one_sub_pos hbox
    norm_num [p1ReturnGridBox]
  · apply complexBox_norm_one_sub_lt hbox (a := (1 / 10 ^ 15 : ℝ))
      (b := (3735 / 10 ^ 12 : ℝ)) <;> norm_num [p1ReturnGridBox]

theorem p1NeutralRoot_quadratic :
    p1NeutralRoot ^ 2 - ((2 * p1NeutralRoot.re : ℝ) : ℂ) * p1NeutralRoot + 1 = 0 := by
  apply Complex.ext
  · simp [pow_two]
    nlinarith [p1NeutralRoot_im_sq]
  · simp [pow_two]
    ring
theorem p1NeutralRoot_trace :
    p1NeutralRoot + p1NeutralRoot⁻¹ = ((2 * p1NeutralRoot.re : ℝ) : ℂ) := by
  have hz : p1NeutralRoot ≠ 0 := by
    intro hz
    have h := p1NeutralRoot_norm
    rw [hz] at h
    norm_num at h
  have ht := congrArg (fun w : ℂ => w * p1NeutralRoot⁻¹) p1NeutralRoot_quadratic
  simp only [sub_mul, add_mul, zero_mul, one_mul, pow_two, mul_assoc,
    mul_inv_cancel₀ hz, mul_one] at ht
  linear_combination ht
theorem p1NeutralRoot_derivative_factorization :
    4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1 =
      (((4 * p1NeutralRoot.re - 1 : ℝ) : ℂ) * p1NeutralRoot) *
        (2 * p1NeutralRoot - ((2 * p1NeutralRoot.re : ℝ) : ℂ)) := by
  let v : ℂ := ((2 * p1NeutralRoot.re : ℝ) : ℂ)
  have hvR : (2 * p1NeutralRoot.re) ^ 2 - (2 * p1NeutralRoot.re) - 3 = 0 := by
    dsimp [p1NeutralRoot]
    have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
    nlinarith
  have hv : v ^ 2 - v - 3 = 0 := by dsimp [v]; exact_mod_cast hvR
  have hq : p1NeutralRoot ^ 2 - v * p1NeutralRoot + 1 = 0 := p1NeutralRoot_quadratic
  have heq : (((4 * p1NeutralRoot.re - 1 : ℝ) : ℂ) * p1NeutralRoot) *
      (2 * p1NeutralRoot - ((2 * p1NeutralRoot.re : ℝ) : ℂ)) =
      (2 * v - 1) * p1NeutralRoot * (2 * p1NeutralRoot - v) := by
    dsimp [v]
    push_cast
    ring
  rw [heq]
  linear_combination (4 * p1NeutralRoot - 1) * hq + 2 * p1NeutralRoot * hv
theorem p1NeutralRoot_derivative_norm :
    ‖4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1‖ =
      (1 - 4 * p1NeutralRoot.re) * (2 * p1NeutralRoot.im) := by
  rw [p1NeutralRoot_derivative_factorization, norm_mul, norm_mul, p1NeutralRoot_norm, mul_one]
  have hr : 4 * p1NeutralRoot.re - 1 ≤ 0 := by linarith [p1NeutralRoot_re_bounds.2]
  have hi : 0 ≤ p1NeutralRoot.im := Real.sqrt_nonneg _
  have heq : 2 * p1NeutralRoot - ((2 * p1NeutralRoot.re : ℝ) : ℂ) =
      ((2 * p1NeutralRoot.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [heq, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hr, abs_of_nonneg (by positivity), mul_one]
  ring
/-- The actual unit-circle mode coefficient `κ_ζ U₁(ζ)^3` of the power seed. -/
noncomputable def p1SeedNeutralCoefficient : ℂ :=
  (4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1)⁻¹ *
    (p1NeutralRoot + 1 + p1NeutralRoot⁻¹) ^ 3
/-- The actual outgoing seed amplitude, defined as twice the coefficient norm. -/
noncomputable def p1SeedNeutralAmplitude : ℝ := 2 * ‖p1SeedNeutralCoefficient‖
theorem p1SeedNeutralAmplitude_formula :
    p1SeedNeutralAmplitude =
      2 * (-(1 + 2 * p1NeutralRoot.re)) ^ 3 /
        ‖4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1‖ := by
  have hk : p1NeutralRoot + 1 + p1NeutralRoot⁻¹ =
      ((1 + 2 * p1NeutralRoot.re : ℝ) : ℂ) := by
    calc
      _ = (p1NeutralRoot + p1NeutralRoot⁻¹) + 1 := by ring
      _ = _ := by rw [p1NeutralRoot_trace]; push_cast; ring
  have hr : 1 + 2 * p1NeutralRoot.re ≤ 0 := by linarith [p1NeutralRoot_re_bounds.2]
  dsimp [p1SeedNeutralAmplitude, p1SeedNeutralCoefficient]
  rw [norm_mul, norm_inv, norm_pow, hk, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hr]
  ring
theorem p1NeutralRoot_derivative_norm_lower :
    (5471387 / 10 ^ 6 : ℝ) ≤
      ‖4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1‖ := by
  have h1 : (3605551275 / 10 ^ 9 : ℝ) ≤ 1 - 4 * p1NeutralRoot.re := by
    linarith [p1NeutralRoot_re_bounds.2]
  have h2 : (1517489913 / 10 ^ 9 : ℝ) ≤ 2 * p1NeutralRoot.im := by
    linarith [p1NeutralRoot_im_bounds.1]
  have hp := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1517489913 / 10 ^ 9)
    (by linarith [h1] : 0 ≤ 1 - 4 * p1NeutralRoot.re)
  rw [p1NeutralRoot_derivative_norm]
  nlinarith [hp]
/-- A rigorous seed amplitude bound, retaining the precision needed for
the final two-mirror budget. -/
theorem p1SeedNeutralAmplitude_bounds : 0 < p1SeedNeutralAmplitude ∧ p1SeedNeutralAmplitude < (1014602 / 10 ^ 8 : ℝ) := by
  have hD := p1NeutralRoot_derivative_norm_lower
  have hDpos : 0 < ‖4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1‖ := by
    linarith
  have hkpos : 0 < -(1 + 2 * p1NeutralRoot.re) := by linarith [p1NeutralRoot_re_bounds.2]
  have hkupper : -(1 + 2 * p1NeutralRoot.re) ≤ (302775638 / 10 ^ 9 : ℝ) := by
    linarith [p1NeutralRoot_re_bounds.1]
  rw [p1SeedNeutralAmplitude_formula]
  constructor
  · positivity
  · calc
      2 * (-(1 + 2 * p1NeutralRoot.re)) ^ 3 /
          ‖4 * p1NeutralRoot ^ 3 - 3 * p1NeutralRoot ^ 2 - 2 * p1NeutralRoot - 1‖ ≤
          2 * (302775638 / 10 ^ 9 : ℝ) ^ 3 / (5471387 / 10 ^ 6) := by
            gcongr
      _ < (1014602 / 10 ^ 8 : ℝ) := by norm_num
theorem p1_return_bound_124_refined : ‖1 - p1NeutralRoot ^ 124‖ < (250632946 / 10 ^ 11 : ℝ) := by
  have hbox := ComplexRationalBox.powRounded_contains
    (by norm_num : 0 < (10 ^ 40 : ℕ)) p1NeutralRootBox_contains 124
  rw [p1Return124_eval] at hbox
  apply complexBox_norm_one_sub_lt hbox (a := (3140844 / 10 ^ 12 : ℝ))
    (b := (250632749 / 10 ^ 11 : ℝ)) <;> norm_num [p1ReturnGridBox]
theorem p1_return_bound_489637838_refined : ‖1 - p1NeutralRoot ^ 489637838‖ < (373488594 / 10 ^ 17 : ℝ) := by
  have hbox := ComplexRationalBox.powRounded_contains
    (by norm_num : 0 < (10 ^ 40 : ℕ)) p1NeutralRootBox_contains 489637838
  rw [p1Return489637838_eval] at hbox
  apply complexBox_norm_one_sub_lt hbox (a := (1 / 10 ^ 16 : ℝ))
    (b := (3734885933 / 10 ^ 18 : ℝ)) <;> norm_num [p1ReturnGridBox]

theorem p1NeutralRoot_norm_inverse_return (L : ℕ) :
    ‖1 - (p1NeutralRoot ^ L)⁻¹‖ = ‖1 - p1NeutralRoot ^ L‖ := by
  have hw : ‖p1NeutralRoot ^ L‖ = 1 := by simp [norm_pow, p1NeutralRoot_norm]
  rw [Complex.inv_eq_conj hw]
  simpa using Complex.norm_conj (1 - p1NeutralRoot ^ L)
/-- The neutral coefficient for the Laurent seed after the two prescribed
differences.  The global mirror sequence and its action are separate obligations. -/
noncomputable def p1FinalNeutralCoefficient : ℂ :=
  (1 - (p1NeutralRoot ^ 124)⁻¹) * (1 - (p1NeutralRoot ^ 489637838)⁻¹) *
    p1SeedNeutralCoefficient
noncomputable def p1FinalNeutralAmplitude : ℝ := 2 * ‖p1FinalNeutralCoefficient‖
theorem p1FinalNeutralAmplitude_formula :
    p1FinalNeutralAmplitude = p1SeedNeutralAmplitude *
      ‖1 - p1NeutralRoot ^ 124‖ * ‖1 - p1NeutralRoot ^ 489637838‖ := by
  dsimp [p1FinalNeutralAmplitude, p1FinalNeutralCoefficient, p1SeedNeutralAmplitude]
  rw [norm_mul, norm_mul, p1NeutralRoot_norm_inverse_return,
    p1NeutralRoot_norm_inverse_return]
  ring
/-- The exact Laurent coefficient after the two differences has nonzero
amplitude below the final appendix bound, using the stronger internal returns. -/
theorem p1FinalNeutralAmplitude_bounds : 0 < p1FinalNeutralAmplitude ∧ p1FinalNeutralAmplitude < (9498 / 10 ^ 17 : ℝ) := by
  have hΔ := p1SeedNeutralAmplitude_bounds
  have hret1 := p1_return_bound_124
  have hret2 := p1_return_bound_489637838
  have hr1u := p1_return_bound_124_refined
  have hr2u := p1_return_bound_489637838_refined
  have hΔu := hΔ.2
  have hΔ0 : 0 ≤ p1SeedNeutralAmplitude := hΔ.1.le
  rw [p1FinalNeutralAmplitude_formula]
  constructor
  · exact mul_pos (mul_pos hΔ.1 hret1.1) hret2.1
  · calc
      p1SeedNeutralAmplitude * ‖1 - p1NeutralRoot ^ 124‖ * ‖1 - p1NeutralRoot ^ 489637838‖ <
          (1014602 / 10 ^ 8 : ℝ) * (250632946 / 10 ^ 11) * (373488594 / 10 ^ 17) := by
            gcongr
      _ < (9498 / 10 ^ 17 : ℝ) := by norm_num

end Salem
