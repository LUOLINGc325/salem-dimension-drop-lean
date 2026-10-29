module

public import Salem.P2RootFactorization
public import Salem.GreenKernel

@[expose] public section

open Polynomial
open scoped BigOperators

namespace Salem

/-- The actual complex reciprocal derivative is the residue coefficient in
the shared spectral Green kernel for the mapped integer polynomial. -/
lemma p2SpectralKappa_eq (z : ℂ) :
    (((p2CoefficientPolynomial.map (Int.castRingHom ℂ)).derivative.eval z)⁻¹) =
      p2CoefficientKappaComplex z := by
  simp [p2CoefficientKappaComplex, Polynomial.derivative_map, Polynomial.eval_map]

/-- On the real roots, the actual complex and real Green coefficients agree. -/
lemma p2CoefficientKappaComplex_ofReal (x : ℝ) :
    p2CoefficientKappaComplex (x : ℂ) = (p2CoefficientKappa x : ℂ) := by
  simp [p2CoefficientKappaComplex, p2CoefficientKappa, p2CoefficientPolynomial]

/-- Integer coefficients make the two unit-root Green coefficients conjugate. -/
lemma p2CoefficientKappaComplex_star (z : ℂ) :
    p2CoefficientKappaComplex (star z) = star (p2CoefficientKappaComplex z) := by
  simp [p2CoefficientKappaComplex, p2CoefficientPolynomial]

/-- The actual bilateral P₂ Green sequence is the real part of the shared
spectral construction, with the expanding root in slot zero. -/
lemma p2GreenCoordinate_eq_spectralReal (i : ℤ) :
    p2GreenCoordinate i =
      (quarticSpectralGreen (p2CoefficientPolynomial.map (Int.castRingHom ℂ)) p2GreenRoot 0 i).re := by
  let P : Polynomial ℂ := p2CoefficientPolynomial.map (Int.castRingHom ℂ)
  by_cases hi : i ≤ 0
  · have he : i - 1 = -(((1 - i).toNat : ℕ) : ℤ) := by omega
    have hpow : (p2CoefficientBeta : ℂ) ^ (i - 1) =
        ((p2CoefficientR ^ (1 - i).toNat : ℝ) : ℂ) := by
      rw [he, zpow_neg, zpow_natCast]
      simp [p2CoefficientR, inv_pow]
    rw [quarticSpectralGreen_left _ _ _ hi]
    simp only [p2GreenRoot, Matrix.cons_val_zero]
    rw [p2SpectralKappa_eq, p2CoefficientKappaComplex_ofReal, hpow]
    simp only [p2GreenCoordinate, p2GreenStableCoordinate, p2GreenNeutralCoordinate,
      ite_eq_left hi, add_zero, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  · have hipos : 0 < i := by omega
    have he : i - 1 = (((i - 1).toNat : ℕ) : ℤ) := by omega
    have huniv : ((Finset.univ : Finset (Fin 4)).erase 0) = {1, 2, 3} := by decide
    have hright : quarticSpectralGreen P p2GreenRoot 0 i =
        (p2CoefficientKappa p2CoefficientR : ℂ) * (p2CoefficientR : ℂ) ^ (i - 1) +
        p2CoefficientKappaComplex p2CoefficientZeta * p2CoefficientZeta ^ (i - 1) +
        star (p2CoefficientKappaComplex p2CoefficientZeta) * (star p2CoefficientZeta) ^ (i - 1) := by
      rw [quarticSpectralGreen_right _ _ _ hipos, huniv]
      dsimp only [P]
      simp_rw [p2SpectralKappa_eq]
      norm_num [p2GreenRoot, p2CoefficientKappaComplex_ofReal]
      simp only [starRingEnd_apply]
      rw [p2CoefficientKappaComplex_star]
      ring
    change p2GreenCoordinate i = (quarticSpectralGreen P p2GreenRoot 0 i).re
    rw [hright, he]
    simp only [zpow_natCast]
    have hstar : star (p2CoefficientKappaComplex p2CoefficientZeta) *
        (star p2CoefficientZeta) ^ (i - 1).toNat =
        star (p2CoefficientKappaComplex p2CoefficientZeta * p2CoefficientZeta ^ (i - 1).toNat) := by
      simp only [star_mul, star_pow]
      ring
    rw [hstar]
    have hpow : (p2CoefficientR : ℂ) ^ (i - 1).toNat =
        ((p2CoefficientR ^ (i - 1).toNat : ℝ) : ℂ) := by simp
    rw [hpow]
    simp only [p2GreenCoordinate, p2GreenStableCoordinate, p2GreenNeutralCoordinate,
      ite_eq_right hi, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.star_def, Complex.conj_re]
    ring

/-- Every actual P₂ root satisfies the scalar reciprocal recurrence equation. -/
lemma p2GreenRoot_scalar_equation (i : Fin 4) :
    p2GreenRoot i ^ 4 - 2 * p2GreenRoot i ^ 3 + p2GreenRoot i ^ 2 - 2 * p2GreenRoot i + 1 = 0 := by
  have hh := p2GreenRoot_isRoot i
  simpa [Polynomial.IsRoot.def, p2CoefficientPolynomial] using hh

/-- The actual bilateral Green sequence has exactly the source's unit impulse,
derived from the shared interpolation moment theorem and the actual root factorization. -/
lemma p2GreenCoordinate_forcing (t : ℤ) :
    reciprocalQuarticOperator (2 : ℝ) 1 p2GreenCoordinate t = if t = 0 then 1 else 0 := by
  have hf := quarticSpectralGreen_forcing (p2CoefficientPolynomial.map (Int.castRingHom ℂ))
    p2GreenRoot 0 p2GreenRoot_injective p2GreenRoot_factorization (A := (2 : ℂ)) (B := 1)
    p2GreenRoot_ne_zero (by simpa only [one_mul] using p2GreenRoot_scalar_equation) t
  have heq : reciprocalQuarticOperator (2 : ℝ) 1 p2GreenCoordinate t =
      (reciprocalQuarticOperator (2 : ℂ) 1
        (quarticSpectralGreen (p2CoefficientPolynomial.map (Int.castRingHom ℂ)) p2GreenRoot 0) t).re := by
    norm_num [reciprocalQuarticOperator, p2GreenCoordinate_eq_spectralReal, Complex.mul_re]
  rw [heq, hf]
  split_ifs <;> norm_num

/-- The literal twenty-impulse seed is also the stated finite Green convolution,
with the original source shifts `100+j`. -/
lemma p2GreenSeedCoordinate_eq_convolution : p2GreenSeedCoordinate =
    finiteGreenConvolution (Finset.range 2685) (fun j : ℕ => 100 + (j : ℤ))
      (fun j => (p2CoefficientSeed.coeff j : ℝ)) p2GreenCoordinate := by
  funext i
  unfold p2GreenSeedCoordinate finiteGreenConvolution
  apply Finset.sum_congr rfl
  intro j _
  rw [show i - 100 - (j : ℤ) = i - (100 + (j : ℤ)) by omega]

/-- The exact integer forcing of the literal finite P₂ seed. -/
noncomputable def p2GreenSeedForcing (t : ℤ) : ℤ :=
  ∑ j ∈ Finset.range 2685, if t = 100 + (j : ℤ) then p2CoefficientSeed.coeff j else 0

/-- The actual finite seed's recurrence equals its explicitly constructed integer forcing. -/
lemma p2GreenSeedCoordinate_forcing (t : ℤ) :
    reciprocalQuarticOperator (2 : ℝ) 1 p2GreenSeedCoordinate t = (p2GreenSeedForcing t : ℝ) := by
  rw [p2GreenSeedCoordinate_eq_convolution]
  rw [finiteGreenConvolution_forcing _ _ _ _ _ _ p2GreenCoordinate_forcing]
  unfold p2GreenSeedForcing
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

/-- The actual seed forcing vanishes outside the paper's interval `[100,2784]`. -/
lemma p2GreenSeedForcing_zero_outside {t : ℤ} (ht : t < 100 ∨ 2784 < t) :
    p2GreenSeedForcing t = 0 := by
  unfold p2GreenSeedForcing
  apply Finset.sum_eq_zero
  intro j hj
  have hjN : j < 2685 := Finset.mem_range.mp hj
  rw [ite_eq_right (by omega : ¬t = 100 + (j : ℤ))]

/-- The first literal forcing coefficient is one, so the actual integer forcing is nonzero. -/
lemma p2GreenSeedForcing_at_100 : p2GreenSeedForcing 100 = 1 := by
  unfold p2GreenSeedForcing
  rw [Finset.sum_eq_single 0]
  · norm_num [p2CoefficientSeed, p2CoefficientBase]
  · intro j _ hj
    rw [ite_eq_right (by omega : ¬(100 : ℤ) = 100 + (j : ℤ))]
  · simp

/-- The actual finite P₂ Green seed therefore has nonzero integer recurrence forcing. -/
lemma p2GreenSeedCoordinate_forcing_integer_nonzero :
    (∀ t : ℤ, ∃ m : ℤ, reciprocalQuarticOperator (2 : ℝ) 1 p2GreenSeedCoordinate t = (m : ℝ)) ∧
      reciprocalQuarticOperator (2 : ℝ) 1 p2GreenSeedCoordinate 100 = 1 := by
  constructor
  · intro t
    exact ⟨p2GreenSeedForcing t, p2GreenSeedCoordinate_forcing t⟩
  · rw [p2GreenSeedCoordinate_forcing, p2GreenSeedForcing_at_100]
    norm_num

/-- The actual neutral convolution has the outgoing mode with exactly the
literal coefficient used in `P2Neutral`, including its source shift101. -/
lemma p2GreenSeedNeutralCoordinate_right_tail (n : ℕ) :
    p2GreenSeedNeutralCoordinate (2885 + (n : ℤ)) =
      2 * ((p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
        p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta⁻¹) *
          p2CoefficientZeta ^ (2885 + n)).re := by
  have hz : p2CoefficientZeta ≠ 0 := by
    simpa [p2GreenRoot] using p2GreenRoot_ne_zero 2
  have hpow (j : ℕ) (hj : j < 2685) :
      p2CoefficientZeta ^ (2885 + (n : ℤ) - 100 - (j : ℤ) - 1).toNat =
        (p2CoefficientZeta⁻¹) ^ 101 * p2CoefficientZeta ^ (2885 + n) * (p2CoefficientZeta⁻¹) ^ j := by
    have he : (((2885 + (n : ℤ) - 100 - (j : ℤ) - 1).toNat : ℕ) : ℤ) =
        ((2885 + n : ℕ) : ℤ) - ((101 + j : ℕ) : ℤ) := by omega
    rw [← zpow_natCast, he, zpow_sub₀ hz]
    simp only [zpow_natCast]
    rw [div_eq_mul_inv, inv_pow, pow_add]
    ring
  have heval : (∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℂ) *
      (p2CoefficientZeta⁻¹) ^ j) = p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta⁻¹ :=
    (Polynomial.eval₂_eq_sum_range' (p := p2CoefficientSeed) (Int.castRingHom ℂ)
      (Nat.lt_succ_of_le p2CoefficientSeed_degree) p2CoefficientZeta⁻¹).symm
  calc
    _ = ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) *
        (2 * (p2CoefficientKappaComplex p2CoefficientZeta *
          p2CoefficientZeta ^ (2885 + (n : ℤ) - 100 - (j : ℤ) - 1).toNat).re) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j < 2685 := Finset.mem_range.mp hj
      have hi : ¬2885 + (n : ℤ) - 100 - (j : ℤ) ≤ 0 := by omega
      simp only [p2GreenNeutralCoordinate, ite_eq_right hi]
    _ = 2 * ((p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
        p2CoefficientZeta ^ (2885 + n)) *
        (∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℂ) * (p2CoefficientZeta⁻¹) ^ j)).re := by
      rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hpow j (Finset.mem_range.mp hj)]
      let w : ℂ := p2CoefficientKappaComplex p2CoefficientZeta *
        ((p2CoefficientZeta⁻¹) ^ 101 * p2CoefficientZeta ^ (2885 + n) * (p2CoefficientZeta⁻¹) ^ j)
      have hterm : (p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
          p2CoefficientZeta ^ (2885 + n)) * ((p2CoefficientSeed.coeff j : ℂ) * (p2CoefficientZeta⁻¹) ^ j) =
          (p2CoefficientSeed.coeff j : ℂ) * w := by dsimp [w]; ring
      rw [hterm]
      change (p2CoefficientSeed.coeff j : ℝ) * (2 * w.re) = 2 * ((p2CoefficientSeed.coeff j : ℂ) * w).re
      simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
      ring
    _ = _ := by
      rw [heval]
      have hterm : (p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
          p2CoefficientZeta ^ (2885 + n)) * p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta⁻¹ =
          (p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
            p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta⁻¹) *
              p2CoefficientZeta ^ (2885 + n) := by ring
      rw [hterm]

/-- The full actual seed right tail is the source stable mode plus the
outgoing unit-circle mode with its certified literal neutral coefficient. -/
lemma p2GreenSeedCoordinate_right_tail (n : ℕ) :
    p2GreenSeedCoordinate (2885 + (n : ℤ)) =
      p2GreenSeedRightCoefficient * p2CoefficientR ^ n +
      2 * ((p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
        p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta⁻¹) *
          p2CoefficientZeta ^ (2885 + n)).re := by
  rw [p2GreenSeedCoordinate_decomposition, p2GreenSeedStableCoordinate_right_tail,
    p2GreenSeedNeutralCoordinate_right_tail]

end Salem
