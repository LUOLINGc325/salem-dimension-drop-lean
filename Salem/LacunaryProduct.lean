module

public import Mathlib

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The total lower frequencies of a finite lacunary prefix are dominated by
its next frequency. This is the geometric estimate used in v2 (product-integral). -/
theorem lacunary_prefix_sum_bound {Q : ℝ} {ξ : ℕ → ℝ}
    (hQ : 1 < Q) (hξ₀ : 0 ≤ ξ 0) (n : ℕ)
    (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) :
    ∑ i ∈ Finset.range n, ξ i ≤ ξ n / (Q - 1) := by
  have htel : ∀ k : ℕ, (∀ i < k, Q * ξ i ≤ ξ (i + 1)) →
      (Q - 1) * (∑ i ∈ Finset.range k, ξ i) ≤ ξ k - ξ 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hg
      have hi := ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))
      have hk := hg k (Nat.lt_succ_self k)
      rw [Finset.sum_range_succ]
      nlinarith [hi, hk]
  apply (le_div_iff₀ (by linarith : 0 < Q - 1)).mpr
  nlinarith [htel n hgap]

/-- Every frequency in a finite lacunary sequence dominates the corresponding
power of the gap ratio times its first frequency. -/
theorem lacunary_frequency_power_lower {Q : ℝ} {ξ : ℕ → ℝ}
    (hQ : 0 ≤ Q) (n : ℕ) (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) :
    Q ^ n * ξ 0 ≤ ξ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hi => hgap i (Nat.lt_succ_of_lt hi))
    have hn := hgap n (Nat.lt_succ_self n)
    calc
      Q ^ (n + 1) * ξ 0 = Q * (Q ^ n * ξ 0) := by ring
      _ ≤ Q * ξ n := mul_le_mul_of_nonneg_left hi hQ
      _ ≤ ξ (n + 1) := hn

/-- A signed sum whose final coefficient has absolute value one cannot
cancel in a `Q > 2` lacunary sequence. The lower bound is the paper's
`c_Q ξ_j`, with `c_Q = (Q-2)/(Q-1)`. -/
theorem lacunary_signed_frequency_bound {Q : ℝ} {ξ ε : ℕ → ℝ} (j : ℕ)
    (hQ : 2 < Q) (hξ : ∀ i ≤ j, 0 ≤ ξ i)
    (hgap : ∀ i < j, Q * ξ i ≤ ξ (i + 1))
    (hε : ∀ i < j, |ε i| ≤ 1) (hεj : |ε j| = 1) :
    (Q - 2) / (Q - 1) * ξ j ≤ |∑ i ∈ Finset.range (j + 1), ε i * ξ i| := by
  have hprefix := lacunary_prefix_sum_bound (by linarith : 1 < Q) (hξ 0 (by omega)) j hgap
  have hlow : |∑ i ∈ Finset.range j, ε i * ξ i| ≤ ∑ i ∈ Finset.range j, ξ i := by
    calc
      _ ≤ ∑ i ∈ Finset.range j, |ε i * ξ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        rw [abs_mul, abs_of_nonneg (hξ i (by omega))]
        simpa using mul_le_mul_of_nonneg_right (hε i hij) (hξ i (by omega))
  have hrev : |ε j * ξ j| ≤ |∑ i ∈ Finset.range (j + 1), ε i * ξ i| +
      |∑ i ∈ Finset.range j, ε i * ξ i| := by
    calc
      _ = |(∑ i ∈ Finset.range (j + 1), ε i * ξ i) -
          (∑ i ∈ Finset.range j, ε i * ξ i)| := by rw [Finset.sum_range_succ]; ring_nf
      _ ≤ _ := abs_sub _ _
  rw [abs_mul, hεj, one_mul, abs_of_nonneg (hξ j le_rfl)] at hrev
  have hden : 0 < Q - 1 := by linarith
  have hid : (Q - 2) / (Q - 1) * ξ j = ξ j - ξ j / (Q - 1) := by field_simp; ring
  rw [hid]
  linarith [hprefix, hlow, hrev]

/-- A single logarithmic cosine factor has the derivative and uniform bound
used in v2 (log-lipschitz). -/
theorem log_cosine_factor_derivative {a σ ξ : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hσ : |σ| = 1) (hξ : 0 ≤ ξ) (x : ℝ) :
    HasDerivAt (fun y => Real.log (1 + a * σ * Real.cos (ξ * y)))
      (-a * σ * ξ * Real.sin (ξ * x) / (1 + a * σ * Real.cos (ξ * x))) x ∧
    |(-a * σ * ξ * Real.sin (ξ * x) / (1 + a * σ * Real.cos (ξ * x)))| ≤ a / (1 - a) * ξ := by
  have hc : |σ * Real.cos (ξ * x)| ≤ 1 := by
    rw [abs_mul, hσ, one_mul]
    exact Real.abs_cos_le_one _
  have hlower : 1 - a ≤ 1 + a * σ * Real.cos (ξ * x) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 ha
    nlinarith [hh]
  have hpos : 0 < 1 + a * σ * Real.cos (ξ * x) := by linarith
  constructor
  · have hd := ((((Real.hasDerivAt_cos (ξ * x)).comp x
        ((hasDerivAt_id x).const_mul ξ)).const_mul (a * σ)).const_add 1).log hpos.ne'
    change HasDerivAt (fun y => Real.log (1 + a * σ * Real.cos (ξ * y))) _ x at hd
    convert hd using 1; dsimp only [Function.comp_def]; ring
  · simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg ha, hσ,
      abs_of_nonneg hξ, abs_of_pos hpos, mul_one]
    apply (div_le_iff₀ hpos).mpr
    have hn := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (ξ * x)) (mul_nonneg ha hξ)
    have hm := mul_le_mul_of_nonneg_left hlower (show 0 ≤ a / (1 - a) * ξ by positivity)
    have heq : (a / (1 - a) * ξ) * (1 - a) = a * ξ := by field_simp
    rw [heq] at hm
    nlinarith [hn, hm]

/-- The positive trigonometric product used in the entropy proof, on a prefix
of the frequency sequence. -/
noncomputable def trigProduct (a : ℝ) (σ ξ : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 + a * σ i * Real.cos (ξ i * x))

/-- Differentiating the actual logarithm of the product gives the finite sum
of logarithmic derivatives, with the uniform bound from v2 (log-lipschitz). -/
theorem log_trigProduct_hasDerivAt {a : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hσ : ∀ i < n, |σ i| = 1)
    (hξ : ∀ i < n, 0 ≤ ξ i) (x : ℝ) :
    HasDerivAt (fun y => Real.log (trigProduct a σ ξ n y))
      (∑ i ∈ Finset.range n, -a * σ i * ξ i * Real.sin (ξ i * x) /
        (1 + a * σ i * Real.cos (ξ i * x))) x ∧
    |∑ i ∈ Finset.range n, -a * σ i * ξ i * Real.sin (ξ i * x) /
        (1 + a * σ i * Real.cos (ξ i * x))| ≤ a / (1 - a) * ∑ i ∈ Finset.range n, ξ i := by
  have hlog (y : ℝ) : Real.log (trigProduct a σ ξ n y) =
      ∑ i ∈ Finset.range n, Real.log (1 + a * σ i * Real.cos (ξ i * y)) := by
    apply Real.log_prod
    intro i hi
    have hc : |σ i * Real.cos (ξ i * y)| ≤ 1 := by
      rw [abs_mul, hσ i (Finset.mem_range.mp hi), one_mul]
      exact Real.abs_cos_le_one _
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 ha
    have hp : 0 < 1 + a * σ i * Real.cos (ξ i * y) := by nlinarith [hh]
    exact hp.ne'
  constructor
  · have hd := HasDerivAt.fun_sum (u := Finset.range n) (fun i hi =>
      (log_cosine_factor_derivative ha ha1 (hσ i (Finset.mem_range.mp hi))
        (hξ i (Finset.mem_range.mp hi)) x).1)
    have heq : (fun y => Real.log (trigProduct a σ ξ n y)) =
        (fun y => ∑ i ∈ Finset.range n, Real.log (1 + a * σ i * Real.cos (ξ i * y))) :=
      funext hlog
    rw [heq]
    exact hd
  · calc
      _ ≤ ∑ i ∈ Finset.range n, |(-a * σ i * ξ i * Real.sin (ξ i * x) /
          (1 + a * σ i * Real.cos (ξ i * x)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, a / (1 - a) * ξ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (log_cosine_factor_derivative ha ha1 (hσ i (Finset.mem_range.mp hi))
          (hξ i (Finset.mem_range.mp hi)) x).2
      _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual log-product is globally Lipschitz, with its sum-of-frequencies
constant. This is the variation estimate needed inside each spatial grid cell. -/
theorem log_trigProduct_lipschitz {a : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hσ : ∀ i < n, |σ i| = 1)
    (hξ : ∀ i < n, 0 ≤ ξ i) (x y : ℝ) :
    |Real.log (trigProduct a σ ξ n y) - Real.log (trigProduct a σ ξ n x)| ≤
      (a / (1 - a) * ∑ i ∈ Finset.range n, ξ i) * |y - x| := by
  have hd (z : ℝ) := log_trigProduct_hasDerivAt n ha ha1 hσ hξ z
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun z _ => (hd z).1.differentiableAt)
    (fun z _ => by rw [(hd z).1.deriv]; simpa only [Real.norm_eq_abs] using (hd z).2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using hh

/-- Lacunarity bounds the log-product's Lipschitz constant by the paper's
`B_{Q,a} ξ_M`, with every parameter explicit. -/
theorem lacunary_log_trigProduct_lipschitz {a Q : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hQ : 1 < Q)
    (hσ : ∀ i ≤ n, |σ i| = 1) (hξ : ∀ i ≤ n, 0 ≤ ξ i)
    (hgap : ∀ i < n, Q * ξ i ≤ ξ (i + 1)) (x y : ℝ) :
    |Real.log (trigProduct a σ ξ (n + 1) y) - Real.log (trigProduct a σ ξ (n + 1) x)| ≤
      (a * Q / ((1 - a) * (Q - 1)) * ξ n) * |y - x| := by
  have hp := lacunary_prefix_sum_bound hQ (hξ 0 (by omega)) n hgap
  have hsum : (∑ i ∈ Finset.range (n + 1), ξ i) ≤ Q / (Q - 1) * ξ n := by
    rw [Finset.sum_range_succ]
    have heq : Q / (Q - 1) * ξ n = ξ n / (Q - 1) + ξ n := by field_simp; ring
    rw [heq]
    linarith [hp]
  have hh := log_trigProduct_lipschitz (n + 1) ha ha1
    (fun i hi => hσ i (by omega)) (fun i hi => hξ i (by omega)) x y
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ a / (1 - a) by positivity)
  have heq : a / (1 - a) * (Q / (Q - 1) * ξ n) =
      a * Q / ((1 - a) * (Q - 1)) * ξ n := by
    have hQ1 : Q - 1 ≠ 0 := by linarith
    have ha0 : 1 - a ≠ 0 := by linarith
    field_simp
  rw [heq] at hmul
  exact hh.trans (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))

/-- The elementary nonconstant Fourier-mode integral bound on every bounded
interval. This is the analytic term estimate in v2 (product-integral). -/
theorem oscillatory_integral_bound {ω : ℝ} (hω : ω ≠ 0) (A B : ℝ) :
    ‖∫ x in A..B, Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |ω| := by
  have hωC : (ω : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hω) Complex.I_ne_zero
  have heq : (∫ x in A..B, Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I)) =
      (Complex.exp (((ω * B : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((ω * A : ℝ) : ℂ) * Complex.I)) / ((ω : ℂ) * Complex.I) := by
    have hh := integral_exp_mul_complex (a := A) (b := B) hωC
    have hfun (x : ℝ) : Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((ω : ℂ) * Complex.I) * x) := by
      congr 1
      push_cast
      ring
    simpa only [← hfun] using hh
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  apply div_le_div_of_nonneg_right _ (abs_nonneg ω)
  calc
    _ ≤ ‖Complex.exp (((ω * B : ℝ) : ℂ) * Complex.I)‖ +
        ‖Complex.exp (((ω * A : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ = 2 := by simp only [Complex.norm_exp_ofReal_mul_I]; norm_num

/-- A cosine product modulated by one Fourier frequency. The recursive
expansion below tracks the three choices in each cosine factor. -/
noncomputable def oscillatoryProduct (a : ℝ) (σ ξ : ℕ → ℝ) (n : ℕ) (ω x : ℝ) : ℂ :=
  Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I) * (trigProduct a σ ξ n x : ℂ)

/-- The actual finite Fourier expansion at the last factor, with frequencies
`ω`, `ω + ξ_n`, and `ω - ξ_n`. Iteration is the paper's ternary expansion. -/
theorem oscillatoryProduct_succ (a : ℝ) (σ ξ : ℕ → ℝ) (n : ℕ) (ω x : ℝ) :
    oscillatoryProduct a σ ξ (n + 1) ω x =
      oscillatoryProduct a σ ξ n ω x +
      ((a * σ n / 2 : ℝ) : ℂ) * oscillatoryProduct a σ ξ n (ω + ξ n) x +
      ((a * σ n / 2 : ℝ) : ℂ) * oscillatoryProduct a σ ξ n (ω - ξ n) x := by
  have hplus : Complex.exp ((((ω + ξ n) * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((ξ n * x : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hminus : Complex.exp ((((ω - ξ n) * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((ξ n * x : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcos : (Real.cos (ξ n * x) : ℂ) =
      (Complex.exp (((ξ n * x : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-((ξ n * x : ℝ) : ℂ) * Complex.I)) / 2 := by
    rw [Complex.ofReal_cos]
    linear_combination (1 / 2 : ℂ) * Complex.two_cos (((ξ n * x : ℝ) : ℂ))
  unfold oscillatoryProduct
  rw [hplus, hminus]
  simp only [trigProduct, Finset.prod_range_succ,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
  rw [hcos]
  push_cast
  ring

/-- Integrating the finite Fourier expansion when the carrier frequency is
separated from all lower frequencies. The factor `(1+a)^n` is the total
absolute coefficient mass of the expanded cosine product. -/
theorem norm_integral_oscillatoryProduct_le {a d : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (hd : 0 < d)
    (hσ : ∀ i < n, |σ i| = 1) (hξ : ∀ i < n, 0 ≤ ξ i) (ω : ℝ)
    (hsep : d + (∑ i ∈ Finset.range n, ξ i) ≤ |ω|) (A B : ℝ) :
    ‖∫ x in A..B, oscillatoryProduct a σ ξ n ω x‖ ≤ 2 * (1 + a) ^ n / d := by
  induction n generalizing ω with
  | zero =>
    have hω : ω ≠ 0 := by intro hh; simp [hh] at hsep; linarith
    have hh := oscillatory_integral_bound hω A B
    have hdiv : 2 / |ω| ≤ 2 / d :=
      div_le_div_of_nonneg_left (by norm_num) hd (by simpa using hsep)
    simpa [oscillatoryProduct, trigProduct] using hh.trans hdiv
  | succ n ih =>
    have hσ' : ∀ i < n, |σ i| = 1 := fun i hi => hσ i (by omega)
    have hξ' : ∀ i < n, 0 ≤ ξ i := fun i hi => hξ i (by omega)
    have hξn : 0 ≤ ξ n := hξ n (by omega)
    have hsep0 : d + (∑ i ∈ Finset.range n, ξ i) ≤ |ω| := by
      rw [Finset.sum_range_succ] at hsep
      linarith
    have habsp : |ω| ≤ |ω + ξ n| + ξ n := by
      calc
        _ = |(ω + ξ n) - ξ n| := by congr 1; ring
        _ ≤ |ω + ξ n| + |ξ n| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hξn]
    have habsm : |ω| ≤ |ω - ξ n| + ξ n := by
      calc
        _ = |(ω - ξ n) + ξ n| := by congr 1; ring
        _ ≤ |ω - ξ n| + |ξ n| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg hξn]
    have hsepp : d + (∑ i ∈ Finset.range n, ξ i) ≤ |ω + ξ n| := by
      rw [Finset.sum_range_succ] at hsep
      linarith
    have hsepm : d + (∑ i ∈ Finset.range n, ξ i) ≤ |ω - ξ n| := by
      rw [Finset.sum_range_succ] at hsep
      linarith
    have hi0 := ih hσ' hξ' ω hsep0
    have hip := ih hσ' hξ' (ω + ξ n) hsepp
    have him := ih hσ' hξ' (ω - ξ n) hsepm
    let c : ℂ := ((a * σ n / 2 : ℝ) : ℂ)
    have hint (v : ℝ) : IntervalIntegrable (oscillatoryProduct a σ ξ n v) MeasureTheory.volume A B := by
      apply Continuous.intervalIntegrable
      unfold oscillatoryProduct trigProduct
      fun_prop
    have hrec : (∫ x in A..B, oscillatoryProduct a σ ξ (n + 1) ω x) =
        (∫ x in A..B, oscillatoryProduct a σ ξ n ω x) +
        c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ω + ξ n) x) +
        c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ω - ξ n) x) := by
      simp_rw [oscillatoryProduct_succ]
      rw [intervalIntegral.integral_add ((hint ω).add ((hint (ω + ξ n)).const_mul c))
        ((hint (ω - ξ n)).const_mul c),
        intervalIntegral.integral_add (hint ω) ((hint (ω + ξ n)).const_mul c),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hc : ‖c‖ = a / 2 := by
      dsimp [c]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg ha,
        hσ n (by omega), mul_one]
      norm_num
    rw [hrec]
    calc
      _ ≤ ‖(∫ x in A..B, oscillatoryProduct a σ ξ n ω x) +
          c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ω + ξ n) x)‖ +
          ‖c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ω - ξ n) x)‖ := norm_add_le _ _
      _ ≤ ‖∫ x in A..B, oscillatoryProduct a σ ξ n ω x‖ +
          ‖c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ω + ξ n) x)‖ +
          ‖c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ω - ξ n) x)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖∫ x in A..B, oscillatoryProduct a σ ξ n ω x‖ +
          a / 2 * ‖∫ x in A..B, oscillatoryProduct a σ ξ n (ω + ξ n) x‖ +
          a / 2 * ‖∫ x in A..B, oscillatoryProduct a σ ξ n (ω - ξ n) x‖ := by
        rw [norm_mul, norm_mul, hc]
      _ ≤ 2 * (1 + a) ^ n / d + a / 2 * (2 * (1 + a) ^ n / d) +
          a / 2 * (2 * (1 + a) ^ n / d) := by
        gcongr
      _ = 2 * (1 + a) ^ (n + 1) / d := by rw [pow_succ]; ring

/-- Summing the nonconstant Fourier terms by their largest active index gives
the paper's explicit finite integral-error sum. This theorem integrates the
actual product; its only inputs are positivity, signs, and lacunary gaps. -/
theorem lacunary_integral_error_le_sum {a Q : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (hQ : 2 < Q) (hσ : ∀ i < n, |σ i| = 1)
    (hξ : ∀ i < n, 0 < ξ i) (hgap : ∀ i, i + 1 < n → Q * ξ i ≤ ξ (i + 1))
    (A B : ℝ) :
    ‖(∫ x in A..B, oscillatoryProduct a σ ξ n 0 x) - ((B - A : ℝ) : ℂ)‖ ≤
      ∑ i ∈ Finset.range n, 2 * a * (1 + a) ^ i / ((Q - 2) / (Q - 1) * ξ i) := by
  induction n with
  | zero => simp [oscillatoryProduct, trigProduct, intervalIntegral.integral_const]
  | succ n ih =>
    have hσ' : ∀ i < n, |σ i| = 1 := fun i hi => hσ i (by omega)
    have hξ' : ∀ i < n, 0 < ξ i := fun i hi => hξ i (by omega)
    have hgap' : ∀ i, i + 1 < n → Q * ξ i ≤ ξ (i + 1) := fun i hi => hgap i (by omega)
    have hprev := ih hσ' hξ' hgap'
    let cQ : ℝ := (Q - 2) / (Q - 1)
    have hcQ : 0 < cQ := div_pos (by linarith) (by linarith)
    have hξn : 0 < ξ n := hξ n (by omega)
    have hd : 0 < cQ * ξ n := mul_pos hcQ hξn
    have hp := lacunary_prefix_sum_bound (by linarith : 1 < Q) (hξ 0 (by omega)).le n
      (fun i hi => hgap i (by omega))
    have hid : cQ * ξ n + ξ n / (Q - 1) = ξ n := by
      have hQ1 : Q - 1 ≠ 0 := by linarith
      dsimp [cQ]
      field_simp [hQ1]
      ring
    have hsep : cQ * ξ n + (∑ i ∈ Finset.range n, ξ i) ≤ ξ n := by linarith [hp, hid]
    have hip := norm_integral_oscillatoryProduct_le n ha hd hσ' (fun i hi => (hξ' i hi).le)
      (ξ n) (by simpa only [abs_of_pos hξn] using hsep) A B
    have him := norm_integral_oscillatoryProduct_le n ha hd hσ' (fun i hi => (hξ' i hi).le)
      (-ξ n) (by simpa only [abs_neg, abs_of_pos hξn] using hsep) A B
    let c : ℂ := ((a * σ n / 2 : ℝ) : ℂ)
    have hint (v : ℝ) : IntervalIntegrable (oscillatoryProduct a σ ξ n v) MeasureTheory.volume A B := by
      apply Continuous.intervalIntegrable
      unfold oscillatoryProduct trigProduct
      fun_prop
    have hrec : (∫ x in A..B, oscillatoryProduct a σ ξ (n + 1) 0 x) =
        (∫ x in A..B, oscillatoryProduct a σ ξ n 0 x) +
        c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ξ n) x) +
        c * (∫ x in A..B, oscillatoryProduct a σ ξ n (-ξ n) x) := by
      simp_rw [oscillatoryProduct_succ]
      simp only [zero_add, zero_sub]
      rw [intervalIntegral.integral_add ((hint 0).add ((hint (ξ n)).const_mul c))
        ((hint (-ξ n)).const_mul c),
        intervalIntegral.integral_add (hint 0) ((hint (ξ n)).const_mul c),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hc : ‖c‖ = a / 2 := by
      dsimp [c]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg ha,
        hσ n (by omega), mul_one]
      norm_num
    rw [hrec]
    have heq (u v w z : ℂ) : u + v + w - z = (u - z) + v + w := by ring
    rw [heq]
    calc
      _ ≤ ‖((∫ x in A..B, oscillatoryProduct a σ ξ n 0 x) - ((B - A : ℝ) : ℂ)) +
          c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ξ n) x)‖ +
          ‖c * (∫ x in A..B, oscillatoryProduct a σ ξ n (-ξ n) x)‖ := norm_add_le _ _
      _ ≤ ‖(∫ x in A..B, oscillatoryProduct a σ ξ n 0 x) - ((B - A : ℝ) : ℂ)‖ +
          ‖c * (∫ x in A..B, oscillatoryProduct a σ ξ n (ξ n) x)‖ +
          ‖c * (∫ x in A..B, oscillatoryProduct a σ ξ n (-ξ n) x)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖(∫ x in A..B, oscillatoryProduct a σ ξ n 0 x) - ((B - A : ℝ) : ℂ)‖ +
          a / 2 * ‖∫ x in A..B, oscillatoryProduct a σ ξ n (ξ n) x‖ +
          a / 2 * ‖∫ x in A..B, oscillatoryProduct a σ ξ n (-ξ n) x‖ := by
        rw [norm_mul, norm_mul, hc]
      _ ≤ (∑ i ∈ Finset.range n, 2 * a * (1 + a) ^ i / (cQ * ξ i)) +
          a / 2 * (2 * (1 + a) ^ n / (cQ * ξ n)) +
          a / 2 * (2 * (1 + a) ^ n / (cQ * ξ n)) := by gcongr
      _ = _ := by rw [Finset.sum_range_succ]; dsimp [cQ]; ring

/-- The finite error sum is bounded by the explicit source constant `D_{Q,a}`.
The first frequency is at least `π`, the gap exceeds two, and `a ≤ 1/2`. -/
theorem lacunary_integral_error_sum_le_D {a Q : ℝ} {ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hgap : ∀ i, i + 1 < n → Q * ξ i ≤ ξ (i + 1)) :
    (∑ i ∈ Finset.range n, 2 * a * (1 + a) ^ i / ((Q - 2) / (Q - 1) * ξ i)) ≤
      2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) := by
  let cQ : ℝ := (Q - 2) / (Q - 1)
  let r : ℝ := (1 + a) / Q
  have hQ0 : 0 < Q := by linarith
  have hcQ : 0 < cQ := div_pos (by linarith) (by linarith)
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hQ0.le
  have hr1 : r < 1 := (div_lt_one hQ0).mpr (by linarith)
  have hgeom : (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1 - r) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1)
  have hterm (i : ℕ) (hi : i < n) :
      2 * a * (1 + a) ^ i / (cQ * ξ i) ≤ 2 * a / (Real.pi * cQ) * r ^ i := by
    have hpower := lacunary_frequency_power_lower hQ0.le i
      (fun j hj => hgap j (by omega))
    have hp : Q ^ i * Real.pi ≤ ξ i :=
      (mul_le_mul_of_nonneg_left hξ₀ (pow_nonneg hQ0.le i)).trans hpower
    have hden : 0 < cQ * (Q ^ i * Real.pi) := mul_pos hcQ (mul_pos (pow_pos hQ0 i) Real.pi_pos)
    calc
      _ ≤ 2 * a * (1 + a) ^ i / (cQ * (Q ^ i * Real.pi)) :=
        div_le_div_of_nonneg_left (by positivity) hden (mul_le_mul_of_nonneg_left hp hcQ.le)
      _ = _ := by
        dsimp [r]
        rw [div_pow]
        field_simp [hcQ.ne', hQ0.ne', Real.pi_ne_zero]
  calc
    _ ≤ ∑ i ∈ Finset.range n, 2 * a / (Real.pi * cQ) * r ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i (Finset.mem_range.mp hi)
    _ = (2 * a / (Real.pi * cQ)) * (∑ i ∈ Finset.range n, r ^ i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * a / (Real.pi * cQ)) * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by
      change (2 * a / (Real.pi * cQ)) * (1 / (1 - r)) = 2 * a / (Real.pi * cQ * (1 - r))
      field_simp

/-- The actual real trigonometric product satisfies v2 (product-integral),
with exactly the paper's explicit constant `D_{Q,a}` and no assumed integral bound. -/
theorem lacunary_trigProduct_integral_bound {a Q : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hσ : ∀ i < n, |σ i| = 1)
    (hgap : ∀ i, i + 1 < n → Q * ξ i ≤ ξ (i + 1)) (A B : ℝ) :
    |(∫ x in A..B, trigProduct a σ ξ n x) - (B - A)| ≤
      2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) := by
  have hQ0 : 0 < Q := by linarith
  have hξ (i : ℕ) (hi : i < n) : 0 < ξ i := by
    have hh := lacunary_frequency_power_lower hQ0.le i (fun j hj => hgap j (by omega))
    have hp : 0 < Q ^ i * ξ 0 := mul_pos (pow_pos hQ0 i) (Real.pi_pos.trans_le hξ₀)
    exact hp.trans_le hh
  have herr := lacunary_integral_error_le_sum n ha hQ hσ hξ hgap A B
  have hcast : (∫ x in A..B, oscillatoryProduct a σ ξ n 0 x) =
      ((∫ x in A..B, trigProduct a σ ξ n x) : ℂ) := by
    simp only [oscillatoryProduct, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      one_mul, intervalIntegral.integral_ofReal]
  rw [hcast, intervalIntegral.integral_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at herr
  exact herr.trans (lacunary_integral_error_sum_le_D n ha ha2 hQ hξ₀ hgap)

/-- The upper-integral form used for the containing interval of the spatial grid. -/
theorem lacunary_trigProduct_integral_upper_bound {a Q : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hQ : 2 < Q) (hξ₀ : Real.pi ≤ ξ 0)
    (hσ : ∀ i < n, |σ i| = 1)
    (hgap : ∀ i, i + 1 < n → Q * ξ i ≤ ξ (i + 1)) (A B : ℝ) :
    (∫ x in A..B, trigProduct a σ ξ n x) ≤ (B - A) +
      2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) := by
  have hh := (abs_le.mp (lacunary_trigProduct_integral_bound n ha ha2 hQ hξ₀ hσ hgap A B)).2
  linarith

/-- Strict positivity of every product value, needed when normalizing its
integrals to the reference grid law. -/
theorem trigProduct_pos {a : ℝ} {σ ξ : ℕ → ℝ} (n : ℕ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hσ : ∀ i < n, |σ i| = 1) (x : ℝ) :
    0 < trigProduct a σ ξ n x := by
  apply Finset.prod_pos
  intro i hi
  have hc : |σ i * Real.cos (ξ i * x)| ≤ 1 := by
    rw [abs_mul, hσ i (Finset.mem_range.mp hi), one_mul]
    exact Real.abs_cos_le_one _
  have hh := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 ha
  nlinarith [hh]

end Salem
