module

public import Mathlib

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The derivative of the second Salem polynomial, evaluated on the real line. -/
noncomputable def p2CoefficientDerivative (x : ℝ) : ℝ :=
  4 * x ^ 3 - 6 * x ^ 2 + 2 * x - 2

/-- The expanding Green coefficient has modulus at most one throughout this range. -/
lemma p2_expanding_reciprocal_derivative_bound {x : ℝ} (hx : (3 / 2 : ℝ) ≤ x) :
    |(p2CoefficientDerivative x)⁻¹| ≤ 1 := by
  have hd : 1 ≤ p2CoefficientDerivative x := by
    have hp : 0 ≤ (x - 3 / 2) * (4 * x ^ 2 + 2) :=
      mul_nonneg (by linarith) (by positivity)
    dsimp [p2CoefficientDerivative]
    nlinarith
  rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < p2CoefficientDerivative x))]
  simpa only [one_div, inv_one] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd

/-- The contracting Green coefficient has modulus at most one on the unit interval. -/
lemma p2_contracting_reciprocal_derivative_bound {r : ℝ} (hr1 : r ≤ 1) :
    |(p2CoefficientDerivative r)⁻¹| ≤ 1 := by
  have hd : p2CoefficientDerivative r ≤ -1 := by
    have hp : 0 ≤ r ^ 2 * (1 - r) := mul_nonneg (sq_nonneg r) (by linarith)
    have hs := sq_nonneg (r - 1 / 2)
    dsimp [p2CoefficientDerivative]
    nlinarith
  have habs : 1 ≤ |p2CoefficientDerivative r| := by
    rw [abs_of_nonpos (by linarith : p2CoefficientDerivative r ≤ 0)]
    linarith
  rw [abs_inv]
  simpa only [one_div, inv_one] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) habs

/-- The ten-term integer polynomial `K_b` specified in Appendix P₂. -/
noncomputable def p2CoefficientBase : Polynomial ℤ :=
  Polynomial.X ^ 0 - Polynomial.X ^ 1 + Polynomial.X ^ 2 - Polynomial.X ^ 3 +
    Polynomial.X ^ 4 - Polynomial.X ^ 7 + Polynomial.X ^ 8 - Polynomial.X ^ 9 +
    Polynomial.X ^ 10 - Polynomial.X ^ 11

/-- The actual preprocessing seed `K_b(1-X^2673)`. -/
noncomputable def p2CoefficientSeed : Polynomial ℤ :=
  p2CoefficientBase * (1 - Polynomial.X ^ 2673)

lemma p2CoefficientBase_degree : p2CoefficientBase.natDegree ≤ 11 := by
  unfold p2CoefficientBase
  compute_degree

lemma p2CoefficientSeed_degree : p2CoefficientSeed.natDegree ≤ 2684 := by
  unfold p2CoefficientSeed
  apply le_trans Polynomial.natDegree_mul_le
  have hf : (1 - Polynomial.X ^ 2673 : Polynomial ℤ).natDegree ≤ 2673 := by
    compute_degree
  have hb := p2CoefficientBase_degree
  omega

/-- The base polynomial is anti-reciprocal, with its fixed degree eleven. -/
lemma p2CoefficientBase_reflect : p2CoefficientBase.reflect 11 = -p2CoefficientBase := by
  simp only [p2CoefficientBase, Polynomial.reflect_add, Polynomial.reflect_sub,
    Polynomial.reflect_monomial]
  norm_num [Polynomial.revAt_le]
  ring

/-- Both factors are anti-reciprocal, so the full preprocessing seed is reciprocal. -/
lemma p2CoefficientSeed_reflect : p2CoefficientSeed.reflect 2684 = p2CoefficientSeed := by
  have hf : (1 - Polynomial.X ^ 2673 : Polynomial ℤ).natDegree ≤ 2673 := by
    compute_degree
  have hreflect : (1 - Polynomial.X ^ 2673 : Polynomial ℤ).reflect 2673 =
      -(1 - Polynomial.X ^ 2673) := by
    rw [Polynomial.reflect_sub, Polynomial.reflect_one, Polynomial.reflect_monomial]
    norm_num [Polynomial.revAt_le]
  change (p2CoefficientBase * (1 - Polynomial.X ^ 2673)).reflect (11 + 2673) = _
  rw [Polynomial.reflect_mul _ _ p2CoefficientBase_degree hf,
    p2CoefficientBase_reflect, hreflect]
  simp only [p2CoefficientSeed]
  ring

/-- A crude analytic bound on the actual base polynomial suffices for the tails. -/
lemma p2CoefficientBase_eval_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |p2CoefficientBase.eval₂ (Int.castRingHom ℝ) r| ≤ 10 := by
  have hp (n : ℕ) : |r ^ n| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hr0 n)]
    exact pow_le_one₀ hr0 hr1
  have htri := Multiset.abs_sum_le_sum_abs
    (s := ({1, -r, r ^ 2, -r ^ 3, r ^ 4, -r ^ 7, r ^ 8, -r ^ 9,
      r ^ 10, -r ^ 11} : Multiset ℝ))
  have hraw : |p2CoefficientBase.eval₂ (Int.castRingHom ℝ) r| ≤
      1 + |r| + |r ^ 2| + |r ^ 3| + |r ^ 4| + |r ^ 7| + |r ^ 8| +
        |r ^ 9| + |r ^ 10| + |r ^ 11| := by
    simpa [p2CoefficientBase, sub_eq_add_neg, add_assoc] using htri
  have hp1 : |r| ≤ 1 := by simpa using hp 1
  linarith [hp1, hp 2, hp 3, hp 4, hp 7, hp 8, hp 9, hp 10, hp 11]

lemma p2CoefficientSeed_eval_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) r| ≤ 10 := by
  have hpow : 0 ≤ r ^ 2673 := pow_nonneg hr0 _
  have hpow1 : r ^ 2673 ≤ 1 := pow_le_one₀ hr0 hr1
  have hf : |1 - r ^ 2673| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  simp only [p2CoefficientSeed, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_pow, Polynomial.eval₂_X, abs_mul]
  have hbase := p2CoefficientBase_eval_bound hr0 hr1
  nlinarith [abs_nonneg (p2CoefficientBase.eval₂ (Int.castRingHom ℝ) r)]

/-- Evaluate an explicitly reflected integer polynomial as the reversed coefficient sum. -/
lemma integer_polynomial_reflect_eval {p : Polynomial ℤ} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (r : ℝ) :
    (p.reflect N).eval₂ (Int.castRingHom ℝ) r =
      ∑ j ∈ Finset.range (N + 1), (p.coeff j : ℝ) * r ^ (N - j) := by
  have hrefdeg : (p.reflect N).natDegree < N + 1 := by
    have h := Polynomial.natDegree_reflect_le (p := p) (N := N)
    omega
  let f : ℕ → ℝ := fun j => ((p.reflect N).coeff j : ℝ) * r ^ j
  calc
    (p.reflect N).eval₂ (Int.castRingHom ℝ) r = ∑ j ∈ Finset.range (N + 1), f j :=
      Polynomial.eval₂_eq_sum_range' _ hrefdeg _
    _ = ∑ j ∈ Finset.range (N + 1), f (N + 1 - 1 - j) :=
      (Finset.sum_range_reflect f (N + 1)).symm
    _ = ∑ j ∈ Finset.range (N + 1), (p.coeff j : ℝ) * r ^ (N - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j ≤ N := by simpa using (Finset.mem_range.mp hj)
      dsimp [f]
      rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.sub_le N j),
        Nat.sub_sub_self hjN]

/-- The actual 2885-core right-tail coefficient sum has its first stable power at100.
The identity uses the reciprocal preprocessing polynomial, not a numerical bound. -/
lemma p2CoefficientSeed_right_sum (r : ℝ) :
    (∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) * r ^ (2885 - 101 - j)) =
      r ^ 100 * p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) r := by
  calc
    (∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) * r ^ (2885 - 101 - j)) =
        r ^ 100 * ∑ j ∈ Finset.range 2685,
          (p2CoefficientSeed.coeff j : ℝ) * r ^ (2684 - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hidx : 2885 - 101 - j = 100 + (2684 - j) := by
        have := Finset.mem_range.mp hj
        omega
      rw [hidx, pow_add]
      ring
    _ = r ^ 100 * (p2CoefficientSeed.reflect 2684).eval₂ (Int.castRingHom ℝ) r := by
      rw [integer_polynomial_reflect_eval p2CoefficientSeed_degree]
    _ = r ^ 100 * p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) r := by
      rw [p2CoefficientSeed_reflect]

/-- The actual second quartic polynomial, kept Mathlib-only for algebraic reuse. -/
noncomputable def p2CoefficientPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X + 1

lemma p2CoefficientDerivative_eval (x : ℝ) :
    p2CoefficientPolynomial.derivative.eval₂ (Int.castRingHom ℝ) x =
      p2CoefficientDerivative x := by
  simp [p2CoefficientPolynomial, p2CoefficientDerivative]
  ring

/-- The exact radical for the second Salem root.  It agrees definitionally with
`beta2`; the present module deliberately has no endpoint imports. -/
noncomputable def p2CoefficientBeta : ℝ :=
  let u : ℝ := 1 + Real.sqrt 2
  (u + Real.sqrt (u ^ 2 - 4)) / 2

noncomputable def p2CoefficientR : ℝ := p2CoefficientBeta⁻¹

/-- The actual reciprocal derivative appearing in the bilateral Green sequence. -/
noncomputable def p2CoefficientKappa (x : ℝ) : ℝ :=
  (p2CoefficientPolynomial.derivative.eval₂ (Int.castRingHom ℝ) x)⁻¹

lemma p2CoefficientBeta_lower : (37 / 20 : ℝ) < p2CoefficientBeta := by
  let u : ℝ := 1 + Real.sqrt 2
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hslo : (7 / 5 : ℝ) < Real.sqrt 2 := by nlinarith
  have hu : (12 / 5 : ℝ) < u := by dsimp [u]; linarith
  have hrad : 0 ≤ u ^ 2 - 4 := by nlinarith
  have hv : 0 ≤ Real.sqrt (u ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlo : (13 / 10 : ℝ) < Real.sqrt (u ^ 2 - 4) := by nlinarith
  change (37 / 20 : ℝ) < (u + Real.sqrt (u ^ 2 - 4)) / 2
  linarith

lemma p2CoefficientR_bounds : 0 < p2CoefficientR ∧ p2CoefficientR ≤ (11 / 20 : ℝ) := by
  have hβ : 0 < p2CoefficientBeta := by linarith [p2CoefficientBeta_lower]
  refine ⟨inv_pos.mpr hβ, ?_⟩
  have hβlo : (20 / 11 : ℝ) < p2CoefficientBeta := by linarith [p2CoefficientBeta_lower]
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 20 / 11) hβlo
  have h' : p2CoefficientR < (11 / 20 : ℝ) := by
    simpa only [p2CoefficientR, one_div, inv_div] using h
  exact h'.le

/-- The Green factors at the two actual real roots have the required uniform bound. -/
lemma p2CoefficientKappa_bounds :
    |p2CoefficientKappa p2CoefficientBeta| ≤ 1 ∧
      |p2CoefficientKappa p2CoefficientR| ≤ 1 := by
  constructor
  · simpa only [p2CoefficientKappa, p2CoefficientDerivative_eval] using
      p2_expanding_reciprocal_derivative_bound
        (by linarith [p2CoefficientBeta_lower] : (3 / 2 : ℝ) ≤ p2CoefficientBeta)
  · simpa only [p2CoefficientKappa, p2CoefficientDerivative_eval] using
      p2_contracting_reciprocal_derivative_bound
        (by linarith [p2CoefficientR_bounds.2] : p2CoefficientR ≤ 1)

/-- The finite rational comparison supplying the exponential tail smallness. -/
lemma p2Coefficient_power_small : (10 : ℝ) * (11 / 20 : ℝ) ^ 100 < 1 / 10 ^ 24 := by
  norm_num

/-- A product bound for the actual seed evaluation at any admissible stable ratio. -/
lemma p2CoefficientSeed_product_bound {r κ : ℝ} (hr0 : 0 ≤ r)
    (hrbound : r ≤ (11 / 20 : ℝ)) (hκ : |κ| ≤ 1) {n : ℕ} (hn : 100 ≤ n) :
    |κ * r ^ n * p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) r| < (1 / 10 ^ 24 : ℝ) := by
  have hr1 : r ≤ 1 := by linarith
  have hp : r ^ n ≤ (11 / 20 : ℝ) ^ 100 := by
    calc
      r ^ n ≤ (11 / 20 : ℝ) ^ n := pow_le_pow_left₀ hr0 hrbound n
      _ ≤ (11 / 20 : ℝ) ^ 100 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have heval := p2CoefficientSeed_eval_bound hr0 hr1
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0 n)]
  calc
    |κ| * r ^ n * |p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) r| ≤
        (1 * (11 / 20 : ℝ) ^ 100) * 10 :=
      mul_le_mul (mul_le_mul hκ hp (pow_nonneg hr0 n) (by norm_num))
        heval (abs_nonneg _) (by positivity)
    _ < 1 / 10 ^ 24 := by nlinarith [p2Coefficient_power_small]

/-- The exact left stable coefficient of the 2885-core Green configuration. -/
noncomputable def p2GreenSeedLeftCoefficient : ℝ :=
  -p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ 101 *
    p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR

/-- The exact right stable coefficient with the appendix's original core indexing. -/
noncomputable def p2GreenSeedRightCoefficient : ℝ :=
  p2CoefficientKappa p2CoefficientR *
    ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) *
      p2CoefficientR ^ (2885 - 101 - j)

/-- The actual specified P₂ Green seed has both stable coefficients below `10⁻²⁴`.
This uses exact algebraic evaluations, not an assumed action certificate. -/
lemma p2GreenSeed_stable_coefficients_small :
    |p2GreenSeedLeftCoefficient| < (1 / 10 ^ 24 : ℝ) ∧
      |p2GreenSeedRightCoefficient| < (1 / 10 ^ 24 : ℝ) := by
  constructor
  · dsimp [p2GreenSeedLeftCoefficient]
    apply p2CoefficientSeed_product_bound p2CoefficientR_bounds.1.le p2CoefficientR_bounds.2
    · simpa only [abs_neg] using p2CoefficientKappa_bounds.1
    · norm_num
  · dsimp [p2GreenSeedRightCoefficient]
    rw [p2CoefficientSeed_right_sum, ← mul_assoc]
    exact p2CoefficientSeed_product_bound p2CoefficientR_bounds.1.le
      p2CoefficientR_bounds.2 p2CoefficientKappa_bounds.2 (by norm_num : 100 ≤ 100)

/-- The final direct difference multiplies the actual left stable coefficient
by `1-r^L`, with the appendix's exact odd delay. -/
noncomputable def p2GreenFinalLeftCoefficient : ℝ :=
  (1 - p2CoefficientR ^ 1846082221) * p2GreenSeedLeftCoefficient

/-- The corresponding exact multiplier of the final right stable coefficient. -/
noncomputable def p2GreenFinalRightCoefficient : ℝ :=
  (p2CoefficientR ^ 1846082221 - 1) * p2GreenSeedRightCoefficient

lemma p2GreenFinal_stable_coefficients_small :
    |p2GreenFinalLeftCoefficient| < (1 / 10 ^ 24 : ℝ) ∧
      |p2GreenFinalRightCoefficient| < (1 / 10 ^ 24 : ℝ) := by
  have hr0 := p2CoefficientR_bounds.1.le
  have hr1 : p2CoefficientR ≤ 1 := by linarith [p2CoefficientR_bounds.2]
  have hp0 : 0 ≤ p2CoefficientR ^ 1846082221 := pow_nonneg hr0 _
  have hp1 : p2CoefficientR ^ 1846082221 ≤ 1 := pow_le_one₀ hr0 hr1
  have hm : |1 - p2CoefficientR ^ 1846082221| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hm' : |p2CoefficientR ^ 1846082221 - 1| ≤ 1 := by
    simpa only [abs_sub_comm] using hm
  constructor
  · rw [p2GreenFinalLeftCoefficient, abs_mul]
    exact lt_of_le_of_lt
      (by simpa using mul_le_mul_of_nonneg_right hm (abs_nonneg p2GreenSeedLeftCoefficient))
      p2GreenSeed_stable_coefficients_small.1
  · rw [p2GreenFinalRightCoefficient, abs_mul]
    exact lt_of_le_of_lt
      (by simpa using mul_le_mul_of_nonneg_right hm' (abs_nonneg p2GreenSeedRightCoefficient))
      p2GreenSeed_stable_coefficients_small.2

/-- A sharp stable-ratio enclosure suffices for the appendix's final tail budget. -/
lemma p2CoefficientR_sharp : p2CoefficientR ≤ (1000 / 1883 : ℝ) := by
  have hβ : (1883 / 1000 : ℝ) < p2CoefficientBeta := by
    let u : ℝ := 1 + Real.sqrt 2
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
    have hslo : (7071 / 5000 : ℝ) < Real.sqrt 2 := by nlinarith
    have hu : (12071 / 5000 : ℝ) < u := by dsimp [u]; linarith
    have hrad : 0 ≤ u ^ 2 - 4 := by nlinarith
    have hv : 0 ≤ Real.sqrt (u ^ 2 - 4) := Real.sqrt_nonneg _
    have hv_sq := Real.sq_sqrt hrad
    have hvlo : (169 / 125 : ℝ) < Real.sqrt (u ^ 2 - 4) := by nlinarith
    change (1883 / 1000 : ℝ) < (u + Real.sqrt (u ^ 2 - 4)) / 2
    linarith
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1883 / 1000) hβ
  have h' : p2CoefficientR < (1000 / 1883 : ℝ) := by
    simpa only [p2CoefficientR, one_div, inv_div] using h
  exact h'.le

lemma p2CoefficientBeta_upper : p2CoefficientBeta < 2 := by
  let u : ℝ := 1 + Real.sqrt 2
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hslt : (Real.sqrt 2 : ℝ) < 3 / 2 := by nlinarith
  have hu : u < 5 / 2 := by dsimp [u]; linarith
  have hupos : 0 ≤ u := by dsimp [u]; positivity
  have hrad : 0 ≤ u ^ 2 - 4 := by dsimp [u]; nlinarith
  have hv : 0 ≤ Real.sqrt (u ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlt : Real.sqrt (u ^ 2 - 4) < 3 / 2 := by nlinarith
  change (u + Real.sqrt (u ^ 2 - 4)) / 2 < 2
  linarith

lemma p2CoefficientR_lower : (1 / 2 : ℝ) < p2CoefficientR := by
  have hpos : 0 < p2CoefficientBeta := by linarith [p2CoefficientBeta_lower]
  simpa only [one_div, p2CoefficientR] using
    one_div_lt_one_div_of_lt hpos p2CoefficientBeta_upper

lemma p2CoefficientKappa_beta_lower : (1 / 62 : ℝ) < p2CoefficientKappa p2CoefficientBeta := by
  let b := p2CoefficientBeta
  have hb0 : 0 < b := by dsimp [b]; linarith [p2CoefficientBeta_lower]
  have hblo : (3 / 2 : ℝ) ≤ b := by dsimp [b]; linarith [p2CoefficientBeta_lower]
  have hbhi : b < 2 := p2CoefficientBeta_upper
  have hdlo : 1 ≤ p2CoefficientDerivative b := by
    have hp : 0 ≤ (b - 3 / 2) * (4 * b ^ 2 + 2) :=
      mul_nonneg (by linarith) (by positivity)
    dsimp [p2CoefficientDerivative]
    nlinarith
  have hb3 : b ^ 3 < 8 := by
    have hp : 0 ≤ b ^ 2 * (2 - b) := mul_nonneg (sq_nonneg b) (by linarith)
    nlinarith
  have hdhi : p2CoefficientDerivative b < 62 := by
    dsimp [p2CoefficientDerivative]
    nlinarith [sq_nonneg b]
  have h := one_div_lt_one_div_of_lt (by linarith : 0 < p2CoefficientDerivative b) hdhi
  simpa only [p2CoefficientKappa, p2CoefficientDerivative_eval, one_div] using h

lemma p2CoefficientBase_eval_lower : (2 / 5 : ℝ) <
    p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR := by
  let r := p2CoefficientR
  have hr0 : 0 ≤ r := p2CoefficientR_bounds.1.le
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [p2CoefficientR_bounds.2]
  have hp (m k : ℕ) : 0 ≤ r ^ m - r ^ (m + k) := by
    have h := mul_nonneg (pow_nonneg hr0 m)
      (sub_nonneg.mpr (pow_le_one₀ hr0 hr1 : r ^ k ≤ 1))
    rw [pow_add]
    nlinarith
  have heq : p2CoefficientBase.eval₂ (Int.castRingHom ℝ) r =
      (1 - r) + (r ^ 2 - r ^ 3) + (r ^ 4 - r ^ 7) +
        (r ^ 8 - r ^ 9) + (r ^ 10 - r ^ 11) := by
    simp [p2CoefficientBase]
    ring
  rw [heq]
  have hrbound : r ≤ (11 / 20 : ℝ) := p2CoefficientR_bounds.2
  have h2 := hp 2 1
  have h4 := hp 4 3
  have h8 := hp 8 1
  have h10 := hp 10 1
  norm_num at h2 h4 h8 h10
  linarith

lemma p2Coefficient_long_factor {L : ℕ} (hL : 2 ≤ L) :
    (1 / 2 : ℝ) < 1 - p2CoefficientR ^ L := by
  have hr0 := p2CoefficientR_bounds.1.le
  have hr1 : p2CoefficientR ≤ 1 := by linarith [p2CoefficientR_bounds.2]
  have hp : p2CoefficientR ^ L ≤ p2CoefficientR ^ 2 :=
    pow_le_pow_of_le_one hr0 hr1 hL
  have hb := pow_le_pow_left₀ hr0 p2CoefficientR_bounds.2 2
  norm_num at hb
  linarith

/-- The final expanding incoming coefficient is nonzero and satisfies the
source's common frequency-selection bound, with its actual boundary indexing. -/
lemma p2GreenFinal_incoming_coefficient_bounds :
    (2 : ℝ) ^ (-112 : ℤ) < |p2GreenFinalLeftCoefficient| ∧
      |p2GreenFinalLeftCoefficient| < 1 := by
  let r := p2CoefficientR
  let k := p2CoefficientKappa p2CoefficientBeta
  let B := p2CoefficientBase.eval₂ (Int.castRingHom ℝ) r
  have hk : (1 / 62 : ℝ) < k := p2CoefficientKappa_beta_lower
  have hk0 : 0 < k := by linarith
  have hr0 : 0 < r := p2CoefficientR_bounds.1
  have hb : (2 / 5 : ℝ) < B := p2CoefficientBase_eval_lower
  have hb0 : 0 < B := by linarith
  have hf1 : (1 / 2 : ℝ) < 1 - r ^ 2673 := p2Coefficient_long_factor (by norm_num)
  have hf2 : (1 / 2 : ℝ) < 1 - r ^ 1846082221 := p2Coefficient_long_factor (by norm_num)
  have hrpow : (1 / 2 : ℝ) ^ 101 ≤ r ^ 101 :=
    pow_le_pow_left₀ (by norm_num) p2CoefficientR_lower.le 101
  have hseed : p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) r = B * (1 - r ^ 2673) := by
    simp [p2CoefficientSeed, B]
  have heq : p2GreenFinalLeftCoefficient =
      -(k * r ^ 101 * B * (1 - r ^ 2673) * (1 - r ^ 1846082221)) := by
    dsimp [p2GreenFinalLeftCoefficient, p2GreenSeedLeftCoefficient]
    change (1 - r ^ 1846082221) * (-k * r ^ 101 * _) = _
    rw [hseed]
    ring
  constructor
  · rw [heq, abs_neg, abs_of_pos (by positivity)]
    have h1 := mul_lt_mul hk hrpow (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ 101) hk0.le
    have h2 := mul_lt_mul h1 hb.le (by norm_num : (0 : ℝ) < 2 / 5)
      (by positivity : 0 ≤ k * r ^ 101)
    have h3 := mul_lt_mul h2 hf1.le (by norm_num : (0 : ℝ) < 1 / 2)
      (by positivity : 0 ≤ k * r ^ 101 * B)
    have h4 := mul_lt_mul h3 hf2.le (by norm_num : (0 : ℝ) < 1 / 2)
      (by positivity : 0 ≤ k * r ^ 101 * B * (1 - r ^ 2673))
    exact lt_trans (by norm_num) h4
  · exact lt_trans p2GreenFinal_stable_coefficients_small.1 (by norm_num)

end Salem
