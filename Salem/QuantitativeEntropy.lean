module

public import Mathlib
public import Salem.BlockGridEntropy

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace Salem

/-- The common Appendix frequency count, using the fixed starting exponent 256. -/
def quantitativeFrequencyCount (J : ℕ) : ℕ := J / 2 - 127

/-- The explicit common schedule; its restriction to `Fin (J/2-127)` is used
in the quantitative entropy criterion. -/
noncomputable def quantitativeFrequency (β c : ℝ) (j : ℕ) : ℝ :=
  Real.pi * |c| * β ^ (256 + 2 * j)

/-- For even `J ≥ 258`, the last chosen exponent is exactly `J`, and every
chosen exponent lies in the uniform Fourier range. -/
theorem quantitativeFrequencyCount_bounds {J : ℕ} (hJ : Even J) (hJlo : 258 ≤ J) :
    0 < quantitativeFrequencyCount J ∧
      256 + 2 * (quantitativeFrequencyCount J - 1) = J ∧
      ∀ j < quantitativeFrequencyCount J, 256 + 2 * j ≤ J := by
  rcases hJ with ⟨k, hk⟩
  dsimp [quantitativeFrequencyCount]
  constructor
  · omega
  constructor
  · omega
  · intro j hj
    omega

/-- The fixed first exponent works uniformly for every source coefficient
`2⁻¹¹² < |c|`, without a minimal-exponent construction. -/
theorem quantitativeFrequency_first {β c : ℝ} (hβ : (5 / 3 : ℝ) < β)
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) : Real.pi ≤ quantitativeFrequency β c 0 := by
  have hβpos : 0 < β := by linarith
  have hβsq : (2 : ℝ) < β ^ 2 := by nlinarith
  have hpow : (2 : ℝ) ^ 128 < β ^ 256 := by
    calc
      _ < (β ^ 2) ^ 128 := by gcongr
      _ = _ := by rw [← pow_mul]
  have hpow112 : (2 : ℝ) ^ 112 < β ^ 256 := lt_trans (by norm_num) hpow
  have hprod : 1 < |c| * β ^ 256 := by
    calc
      _ < β ^ 256 / (2 : ℝ) ^ 112 := (one_lt_div (by positivity)).mpr hpow112
      _ = (1 / (2 : ℝ) ^ 112) * β ^ 256 := by ring
      _ < _ := mul_lt_mul_of_pos_right hc (pow_pos hβpos _)
  have hh := mul_le_mul_of_nonneg_left hprod.le Real.pi_pos.le
  simpa only [quantitativeFrequency, mul_zero, add_zero, mul_one, mul_assoc] using hh

/-- Consecutive scheduled frequencies have the exact ratio `β²`. -/
theorem quantitativeFrequency_succ (β c : ℝ) (j : ℕ) :
    quantitativeFrequency β c (j + 1) = β ^ 2 * quantitativeFrequency β c j := by
  unfold quantitativeFrequency
  rw [show 256 + 2 * (j + 1) = (256 + 2 * j) + 2 by omega, pow_add]
  ring

/-- Every scheduled frequency fits the common block scale `N=J+3`; this bound
holds uniformly over the whole schedule and uses no large finite enumeration. -/
theorem quantitativeFrequency_scale {β c : ℝ} {J j : ℕ}
    (hβ : (5 / 3 : ℝ) < β) (hc : |c| < 1) (hj : 256 + 2 * j ≤ J) :
    β⁻¹ ^ (J + 3) * quantitativeFrequency β c j < 1 := by
  have hβpos : 0 < β := by linarith
  have hβone : 1 ≤ β := by linarith
  have hpow : β ^ (256 + 2 * j) ≤ β ^ J := pow_le_pow_right₀ hβone hj
  have hcancel : β⁻¹ ^ (J + 3) * β ^ J = β⁻¹ ^ 3 := by
    rw [pow_add]
    calc
      β⁻¹ ^ J * β⁻¹ ^ 3 * β ^ J = (β⁻¹ ^ J * β ^ J) * β⁻¹ ^ 3 := by ring
      _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hβpos.ne', one_pow, one_mul]
  have hcub : (125 / 27 : ℝ) < β ^ 3 := by
    have hh : (5 / 3 : ℝ) ^ 3 < β ^ 3 := by gcongr
    norm_num at hh
    exact hh
  have hπ : Real.pi < β ^ 3 := lt_trans Real.pi_lt_four (by linarith)
  have hπc0 : Real.pi * |c| < Real.pi := by
    simpa using mul_lt_mul_of_pos_left hc Real.pi_pos
  have hπc : Real.pi * |c| < β ^ 3 := hπc0.trans hπ
  calc
    _ ≤ β⁻¹ ^ (J + 3) * (Real.pi * |c| * β ^ J) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr hβpos.le) _)
      exact mul_le_mul_of_nonneg_left hpow (mul_nonneg Real.pi_pos.le (abs_nonneg c))
    _ = Real.pi * |c| / β ^ 3 := by
      calc
        _ = (Real.pi * |c|) * (β⁻¹ ^ (J + 3) * β ^ J) := by ring
        _ = _ := by rw [hcancel, inv_pow]; ring
    _ < 1 := (div_lt_one (pow_pos hβpos _)).mpr hπc

/-- The support-radius and separation-factor bounds in the sharp entropy corollary. -/
theorem sharp_entropy_radius_bounds {β : ℝ} (hβ : (5 / 3 : ℝ) < β) :
    let R : ℝ := (1 - β⁻¹)⁻¹
    0 < R ∧ R < 5 / 2 ∧
      0 < 1 + (1 + 2 * R) / (2 * (β - 1)) ∧
      1 + (1 + 2 * R) / (2 * (β - 1)) < 11 / 2 := by
  let R : ℝ := (1 - β⁻¹)⁻¹
  change 0 < R ∧ R < 5 / 2 ∧ _
  have hβpos : 0 < β := by linarith
  have hβm : 0 < β - 1 := by linarith
  have hReq : R = β / (β - 1) := by
    dsimp [R]
    field_simp [hβpos.ne', hβm.ne']
  have hRpos : 0 < R := by rw [hReq]; exact div_pos hβpos hβm
  have hRlt : R < 5 / 2 := by
    rw [hReq]
    apply (div_lt_iff₀ hβm).mpr
    linarith
  have hCpos : 0 < 1 + (1 + 2 * R) / (2 * (β - 1)) := by positivity
  have hClt : 1 + (1 + 2 * R) / (2 * (β - 1)) < 11 / 2 := by
    have hh : (1 + 2 * R) / (2 * (β - 1)) < 9 / 2 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (β - 1))).mpr
      nlinarith [hRlt, hβ]
    linarith
  exact ⟨hRpos, hRlt, hCpos, hClt⟩

/-- The lacunary denominator factors in the sharp entropy range. -/
theorem sharp_entropy_gap_bounds {Q a : ℝ} (hQ : (25 / 9 : ℝ) ≤ Q) (ha : a ≤ 1 / 9) :
    7 / 16 ≤ (Q - 2) / (Q - 1) ∧ 3 / 5 ≤ 1 - (1 + a) / Q := by
  have hQpos : 0 < Q := by linarith
  have hQm : 0 < Q - 1 := by linarith
  constructor
  · apply (le_div_iff₀ hQm).mpr
    linarith
  · have hh : (1 + a) / Q ≤ 2 / 5 := by
      apply (div_le_iff₀ hQpos).mpr
      linarith
    linarith

/-- The exact source upper bound for `D_{Q,a}`. -/
theorem sharp_entropy_D_bound {Q a : ℝ} (hQ : (25 / 9 : ℝ) ≤ Q)
    (ha9 : a ≤ 1 / 9) :
    2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) ≤
      160 / (189 * Real.pi) := by
  have hb := sharp_entropy_gap_bounds hQ ha9
  have hc : 0 ≤ (Q - 2) / (Q - 1) := le_trans (by norm_num) hb.1
  have hr : 0 ≤ 1 - (1 + a) / Q := le_trans (by norm_num) hb.2
  have hh := mul_le_mul hb.1 hb.2 (by norm_num : (0 : ℝ) ≤ 3 / 5) hc
  have hden : (21 / 80 : ℝ) * Real.pi ≤
      Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q) := by
    have hp := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
    nlinarith [hp]
  have hdenpos : 0 < Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q) :=
    lt_of_lt_of_le (by positivity) hden
  calc
    _ ≤ (2 / 9 : ℝ) / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q)) :=
      div_le_div_of_nonneg_right (by linarith) hdenpos.le
    _ ≤ (2 / 9 : ℝ) / ((21 / 80 : ℝ) * Real.pi) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = _ := by field_simp; ring

/-- The exact source upper bound for `B_{Q,a}`. -/
theorem sharp_entropy_B_bound {Q a : ℝ} (hQ : (25 / 9 : ℝ) ≤ Q)
    (ha9 : a ≤ 1 / 9) :
    a * Q / ((1 - a) * (Q - 1)) ≤ 25 / 128 := by
  have hQpos : 0 < Q := by linarith
  have hQm : 0 < Q - 1 := by linarith
  have ham : 0 < 1 - a := by linarith
  have hleft : a / (1 - a) ≤ 1 / 8 := by
    apply (div_le_iff₀ ham).mpr
    linarith
  have hright : Q / (Q - 1) ≤ 25 / 16 := by
    apply (div_le_iff₀ hQm).mpr
    linarith
  have hh := mul_le_mul hleft hright (div_nonneg hQpos.le hQm.le) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have heq : a * Q / ((1 - a) * (Q - 1)) = (a / (1 - a)) * (Q / (Q - 1)) := by field_simp
  rw [heq]
  nlinarith [hh]

/-- The finite Taylor sum specified in the paper proves `41 < exp(15/4)`. -/
theorem forty_one_lt_exp_fifteen_quarters : (41 : ℝ) < Real.exp (15 / 4) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 4) 9
  have hsum : (∑ i ∈ Finset.range 9, (15 / 4 : ℝ) ^ i / (i.factorial : ℝ)) =
      2459867141 / 58720256 := by norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hh
  linarith [hh]

/-- The source entropy constant is strictly below four throughout the sharp
range. The logarithmic comparison uses the paper's explicit rational Taylor sum. -/
theorem sharp_entropy_constant_lt_four {β Q a : ℝ}
    (hβ : (5 / 3 : ℝ) < β) (hQ : (25 / 9 : ℝ) ≤ Q)
    (ha : 0 ≤ a) (ha9 : a ≤ 1 / 9) :
    let R : ℝ := (1 - β⁻¹)⁻¹
    let D : ℝ := 2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))
    let B : ℝ := a * Q / ((1 - a) * (Q - 1))
    Real.log ((2 * R + 2 + D) * (1 + (1 + 2 * R) / (2 * (β - 1)))) + B < 4 := by
  let R : ℝ := (1 - β⁻¹)⁻¹
  let D : ℝ := 2 * a / (Real.pi * ((Q - 2) / (Q - 1)) * (1 - (1 + a) / Q))
  let B : ℝ := a * Q / ((1 - a) * (Q - 1))
  change Real.log ((2 * R + 2 + D) * (1 + (1 + 2 * R) / (2 * (β - 1)))) + B < 4
  have hrad := sharp_entropy_radius_bounds hβ
  change 0 < R ∧ R < 5 / 2 ∧ 0 < 1 + (1 + 2 * R) / (2 * (β - 1)) ∧
    1 + (1 + 2 * R) / (2 * (β - 1)) < 11 / 2 at hrad
  have hD := sharp_entropy_D_bound hQ ha9
  change D ≤ 160 / (189 * Real.pi) at hD
  have hB := sharp_entropy_B_bound hQ ha9
  change B ≤ 25 / 128 at hB
  have hg := sharp_entropy_gap_bounds hQ ha9
  have hcpos : 0 < (Q - 2) / (Q - 1) := lt_of_lt_of_le (by norm_num) hg.1
  have hrpos : 0 < 1 - (1 + a) / Q := lt_of_lt_of_le (by norm_num) hg.2
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hDsmall : D < 160 / 567 := by
    have hh : 160 / (189 * Real.pi) < (160 / 567 : ℝ) := by
      apply (div_lt_iff₀ (by positivity : 0 < 189 * Real.pi)).mpr
      nlinarith [Real.pi_gt_three]
    exact hD.trans_lt hh
  have hargpos : 0 < (2 * R + 2 + D) * (1 + (1 + 2 * R) / (2 * (β - 1))) :=
    mul_pos (by linarith [hrad.1]) hrad.2.2.1
  have hsum : 2 * R + 2 + D < 7 + (160 / 567 : ℝ) := by linarith [hrad.2.1, hDsmall]
  have harglt : (2 * R + 2 + D) * (1 + (1 + 2 * R) / (2 * (β - 1))) <
      (7 + (160 / 567 : ℝ)) * (11 / 2) := by
    calc
      _ < (7 + (160 / 567 : ℝ)) * (1 + (1 + 2 * R) / (2 * (β - 1))) :=
        mul_lt_mul_of_pos_right hsum hrad.2.2.1
      _ < _ := mul_lt_mul_of_pos_left hrad.2.2.2 (by norm_num)
  have harg41 : (2 * R + 2 + D) * (1 + (1 + 2 * R) / (2 * (β - 1))) < 41 :=
    harglt.trans (by norm_num)
  have hlog : Real.log ((2 * R + 2 + D) * (1 + (1 + 2 * R) / (2 * (β - 1)))) < 15 / 4 :=
    (Real.log_lt_iff_lt_exp hargpos).mpr (harg41.trans forty_one_lt_exp_fifteen_quarters)
  linarith [hlog, hB]

/-- A finite positive Taylor sum certifies the source lower bound for `e`. -/
theorem exp_one_gt_163_sixtieths : (163 / 60 : ℝ) < Real.exp 1 := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith [hh]

/-- The paper's exact integer certificate implies `log N < 60`, without
approximating the logarithm or enumerating words at the block length. -/
theorem log_nat_lt_sixty_of_integer_bound {N : ℕ} (hN : 0 < N)
    (hcert : 163 ^ 60 > N * 60 ^ 60) : Real.log (N : ℝ) < 60 := by
  have hcertR : (N : ℝ) * (60 : ℝ) ^ 60 < (163 : ℝ) ^ 60 := by exact_mod_cast hcert
  have hNrat : (N : ℝ) < (163 / 60 : ℝ) ^ 60 := by
    rw [div_pow]
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 60 ^ 60)).mpr hcertR
  have hExp : (163 / 60 : ℝ) ^ 60 < Real.exp 60 := by
    calc
      _ < (Real.exp 1) ^ 60 := by gcongr; exact exp_one_gt_163_sixtieths
      _ = _ := by simp
  exact (Real.log_lt_iff_lt_exp (Nat.cast_pos.mpr hN)).mpr (hNrat.trans hExp)

/-- Exact arithmetic for the first source deficit with the fixed frequency count. -/
theorem quantitativeDeficit1_arithmetic :
    (1 / 2 : ℝ) * (quantitativeFrequencyCount (2 * 10 ^ 25) : ℝ) *
      (3 / (4 * 10 ^ 11) : ℝ) ^ 2 - 125 = (625 / 4 - 1143 / (32 * 10 ^ 22) : ℝ) := by
  have hcount : quantitativeFrequencyCount (2 * 10 ^ 25) = 9999999999999999999999873 := by
    change (2 * 10 ^ 25 : ℕ) / 2 - 127 = 9999999999999999999999873
    norm_num
  rw [hcount]
  norm_num

/-- Exact arithmetic for the second source deficit with the fixed frequency count. -/
theorem quantitativeDeficit2_arithmetic :
    (1 / 2 : ℝ) * (quantitativeFrequencyCount (10 ^ 26) : ℝ) *
      (9 / (2 * 10 ^ 11) : ℝ) ^ 2 - 125 = (50500 - 10287 / (8 * 10 ^ 22) : ℝ) := by
  have hcount : quantitativeFrequencyCount (10 ^ 26) = 49999999999999999999999873 := by
    change (10 ^ 26 : ℕ) / 2 - 127 = 49999999999999999999999873
    norm_num
  rw [hcount]
  norm_num

section QuantitativeQuartic

variable (P : Polynomial ℤ) (hPmonic : P.Monic) (hdegree : P.natDegree = 4)
  (hPirr : Irreducible (P.map (Int.castRingHom ℚ)))
  {β : ℝ} (hβlo : (5 / 3 : ℝ) < β) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζim : ζ.im ≠ 0)
  (hβroot : (P.map (Int.castRingHom ℂ)).IsRoot (β : ℂ))
  (hβinvroot : (P.map (Int.castRingHom ℂ)).IsRoot ((β⁻¹ : ℝ) : ℂ))
  (hζroot : (P.map (Int.castRingHom ℂ)).IsRoot ζ)
  (hstarroot : (P.map (Int.castRingHom ℂ)).IsRoot (star ζ))

include hPmonic hdegree hPirr hβlo hζ hζim hβroot hβinvroot hζroot hstarroot

/-- The actual merged block entropy deficit obtained from a uniform finite
cosine Fourier bound. The frequency schedule, entropy constant, and logarithmic
block-length penalty are derived internally; no entropy bound is assumed. -/
theorem signBlockEntropy_deficit_of_uniform_bias {c a : ℝ} {J : ℕ}
    (hJ : Even J) (hJlo : 258 ≤ J) (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1)
    (ha : 0 ≤ a) (ha9 : a ≤ 1 / 9) (hcert : 163 ^ 60 > (J + 3) * 60 ^ 60)
    (hfourier : ∀ k ≤ J, a ≤ |∫ x, Real.cos ((Real.pi * |c| * β ^ k) * x)
      ∂ElementaryCore.bernoulliLaw β|) :
    signBlockEntropy β (J + 3) < (J + 3 : ℕ) * Real.log β -
      ((1 / 2 : ℝ) * (quantitativeFrequencyCount J : ℝ) * a ^ 2 - 125) := by
  have hM := quantitativeFrequencyCount_bounds hJ hJlo
  let n : ℕ := quantitativeFrequencyCount J - 1
  have hcount : n + 1 = quantitativeFrequencyCount J := by dsimp [n]; omega
  have hβ : 1 < β := by linarith
  have hsq : (5 / 3 : ℝ) ^ 2 < β ^ 2 := by gcongr
  norm_num at hsq
  have hQ : 2 < β ^ 2 := by linarith only [hsq]
  have hQ25 : (25 / 9 : ℝ) ≤ β ^ 2 := hsq.le
  have hgap : ∀ i < n, β ^ 2 * quantitativeFrequency β c i ≤ quantitativeFrequency β c (i + 1) := by
    intro i _
    rw [quantitativeFrequency_succ]
  have hscale : β⁻¹ ^ (J + 3) * quantitativeFrequency β c n ≤ 1 :=
    (quantitativeFrequency_scale hβlo hc1 (by dsimp [n]; omega)).le
  have hfourier' : ∀ i ≤ n, a ≤ |∫ x, Real.cos (quantitativeFrequency β c i * x)
      ∂ElementaryCore.bernoulliLaw β| := by
    intro i hi
    have hiM : i < quantitativeFrequencyCount J := by omega
    have he := hM.2.2 i hiM
    simpa only [quantitativeFrequency] using hfourier (256 + 2 * i) he
  have hbound := signBlockEntropy_fourier_bound_quadratic P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot n (J + 3) (by omega) ha (by linarith) hQ
    (quantitativeFrequency_first hβlo hc) hgap hscale hfourier'
  rw [hcount] at hbound
  dsimp only [signSupportRadius, atomSeparationConstant] at hbound
  have hC := sharp_entropy_constant_lt_four hβlo hQ25 ha ha9
  dsimp only at hC
  have hlog := log_nat_lt_sixty_of_integer_bound (by omega : 0 < J + 3) hcert
  nlinarith only [hbound, hC, hlog]

/-- The first Appendix configuration gives the actual source deficit `D₁`
from its uniform Fourier modulus bound. All numerical side conditions are closed. -/
theorem signBlockEntropy_deficit_1_of_uniform_bias {c : ℝ}
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1)
    (hfourier : ∀ k ≤ (2 * 10 ^ 25 : ℕ), (3 / (4 * 10 ^ 11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi * |c| * β ^ k) * x) ∂ElementaryCore.bernoulliLaw β|) :
    signBlockEntropy β (2 * 10 ^ 25 + 3) < (2 * 10 ^ 25 + 3 : ℕ) * Real.log β -
      (625 / 4 - 1143 / (32 * 10 ^ 22) : ℝ) := by
  have h := signBlockEntropy_deficit_of_uniform_bias P hPmonic hdegree hPirr hβlo ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot (J := 2 * 10 ^ 25) (a := 3 / (4 * 10 ^ 11))
    (by norm_num) (by norm_num) hc hc1 (by norm_num) (by norm_num) (by norm_num) hfourier
  rw [quantitativeDeficit1_arithmetic] at h
  exact h

/-- The second Appendix configuration gives the actual source deficit `D₂`
from its uniform Fourier modulus bound. All numerical side conditions are closed. -/
theorem signBlockEntropy_deficit_2_of_uniform_bias {c : ℝ}
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1)
    (hfourier : ∀ k ≤ (10 ^ 26 : ℕ), (9 / (2 * 10 ^ 11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi * |c| * β ^ k) * x) ∂ElementaryCore.bernoulliLaw β|) :
    signBlockEntropy β (10 ^ 26 + 3) < (10 ^ 26 + 3 : ℕ) * Real.log β -
      (50500 - 10287 / (8 * 10 ^ 22) : ℝ) := by
  have h := signBlockEntropy_deficit_of_uniform_bias P hPmonic hdegree hPirr hβlo ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot (J := 10 ^ 26) (a := 9 / (2 * 10 ^ 11))
    (by norm_num) (by norm_num) hc hc1 (by norm_num) (by norm_num) (by norm_num) hfourier
  rw [quantitativeDeficit2_arithmetic] at h
  exact h

/-- A uniform finite Fourier input produces an actual Borel full-mass set
with the requested quantitative dimension bound. The entropy deficit and block
cover are proved internally from the input, rather than supplied as assumptions. -/
theorem exists_quantitative_cover_of_uniform_bias {c a L ε : ℝ} {J : ℕ}
    (hJ : Even J) (hJlo : 258 ≤ J) (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1)
    (ha : 0 ≤ a) (ha9 : a ≤ 1 / 9) (hcert : 163 ^ 60 > (J + 3) * 60 ^ 60)
    (hfourier : ∀ k ≤ J, a ≤ |∫ x, Real.cos ((Real.pi * |c| * β ^ k) * x)
      ∂ElementaryCore.bernoulliLaw β|)
    (hlogL : Real.log β ≤ L) (hε : ε < 1)
    (hD : 0 ≤ (1 / 2 : ℝ) * (quantitativeFrequencyCount J : ℝ) * a ^ 2 - 125)
    (hcomparison : ε < ((1 / 2 : ℝ) * (quantitativeFrequencyCount J : ℝ) * a ^ 2 - 125) /
      ((J + 3 : ℕ) * L)) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw β F = 1 ∧
      dimH F < ENNReal.ofReal (1 - ε) := by
  let N : ℕ := J + 3
  let H : ℝ := signBlockEntropy β N
  let D : ℝ := (1 / 2 : ℝ) * (quantitativeFrequencyCount J : ℝ) * a ^ 2 - 125
  have hβ : 1 < β := by linarith only [hβlo]
  have hN : 0 < N := by dsimp [N]; omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlogβ : 0 < Real.log β := Real.log_pos hβ
  have hNlog : 0 < (N : ℝ) * Real.log β := mul_pos hNr hlogβ
  have hH := signBlockEntropy_deficit_of_uniform_bias P hPmonic hdegree hPirr hβlo ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot hJ hJlo hc hc1 ha ha9 hcert hfourier
  change H < (N : ℝ) * Real.log β - D at hH
  change 0 ≤ D at hD
  change ε < D / ((N : ℝ) * L) at hcomparison
  have hDcompare : D / ((N : ℝ) * L) ≤ D / ((N : ℝ) * Real.log β) := by
    apply div_le_div_of_nonneg_left hD hNlog
    exact mul_le_mul_of_nonneg_left hlogL hNr.le
  have hεD : ε < D / ((N : ℝ) * Real.log β) := hcomparison.trans_le hDcompare
  have hnorm : H / ((N : ℝ) * Real.log β) < 1 - D / ((N : ℝ) * Real.log β) := by
    apply (div_lt_iff₀ hNlog).mpr
    have heq : (1 - D / ((N : ℝ) * Real.log β)) * ((N : ℝ) * Real.log β) =
        (N : ℝ) * Real.log β - D := by field_simp
    rw [heq]
    exact hH
  have hratio : H / (N : ℝ) / Real.log β < 1 - ε := by
    rw [div_div]
    linarith only [hnorm, hεD]
  obtain ⟨F, hFmeas, hFmass, hFdim⟩ := exists_full_mass_signBlockEntropy_cover β hβ N hN
  change ElementaryCore.bernoulliLaw β F = 1 at hFmass
  change dimH F ≤ ENNReal.ofReal (H / (N : ℝ) / Real.log β) at hFdim
  exact ⟨F, hFmeas, hFmass, hFdim.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by linarith only [hε] : 0 < 1 - ε)).mpr hratio)⟩

/-- The first source quantitative dimension drop, for the actual Bernoulli
law, follows from its uniform finite Fourier input and logarithmic root bound. -/
theorem exists_quantitative_cover_1_of_uniform_bias {c : ℝ}
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1) (hlogβ : Real.log β ≤ 11 / 20)
    (hfourier : ∀ k ≤ (2 * 10 ^ 25 : ℕ), (3 / (4 * 10 ^ 11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi * |c| * β ^ k) * x) ∂ElementaryCore.bernoulliLaw β|) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw β F = 1 ∧
      dimH F < ENNReal.ofReal (1 - (14 : ℝ) / 10 ^ 24) := by
  exact exists_quantitative_cover_of_uniform_bias P hPmonic hdegree hPirr hβlo ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot (J := 2 * 10 ^ 25) (a := 3 / (4 * 10 ^ 11))
    (L := 11 / 20) (ε := 14 / 10 ^ 24)
    (by norm_num) (by norm_num) hc hc1 (by norm_num) (by norm_num) (by norm_num) hfourier
    hlogβ (by norm_num)
    (by rw [quantitativeDeficit1_arithmetic]; norm_num)
    (by rw [quantitativeDeficit1_arithmetic]; norm_num)

/-- The second source quantitative dimension drop, for the actual Bernoulli
law, follows from its uniform finite Fourier input and logarithmic root bound. -/
theorem exists_quantitative_cover_2_of_uniform_bias {c : ℝ}
    (hc : 1 / (2 : ℝ) ^ 112 < |c|) (hc1 : |c| < 1) (hlogβ : Real.log β ≤ 16 / 25)
    (hfourier : ∀ k ≤ (10 ^ 26 : ℕ), (9 / (2 * 10 ^ 11) : ℝ) ≤
      |∫ x, Real.cos ((Real.pi * |c| * β ^ k) * x) ∂ElementaryCore.bernoulliLaw β|) :
    ∃ F : Set ℝ, MeasurableSet F ∧ ElementaryCore.bernoulliLaw β F = 1 ∧
      dimH F < ENNReal.ofReal (1 - (78 : ℝ) / 10 ^ 23) := by
  exact exists_quantitative_cover_of_uniform_bias P hPmonic hdegree hPirr hβlo ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot (J := 10 ^ 26) (a := 9 / (2 * 10 ^ 11))
    (L := 16 / 25) (ε := 78 / 10 ^ 23)
    (by norm_num) (by norm_num) hc hc1 (by norm_num) (by norm_num) (by norm_num) hfourier
    hlogβ (by norm_num)
    (by rw [quantitativeDeficit2_arithmetic]; norm_num)
    (by rw [quantitativeDeficit2_arithmetic]; norm_num)

end QuantitativeQuartic

end Salem
