module

public import Salem.P2Coefficients
public import Salem.RationalIntervals

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The explicit upper-half-plane unit conjugate for P₂. -/
noncomputable def p2CoefficientZeta : ℂ :=
  let v : ℝ := 1 - Real.sqrt 2
  ⟨v / 2, Real.sqrt (4 - v ^ 2) / 2⟩

noncomputable def p2CoefficientKappaComplex (z : ℂ) : ℂ :=
  (p2CoefficientPolynomial.derivative.eval₂ (Int.castRingHom ℂ) z)⁻¹

/-- The stable part of the literal bilateral Green sequence in Appendix P₂. -/
noncomputable def p2GreenStableCoordinate (i : ℤ) : ℝ :=
  if i ≤ 0 then -p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ (1 - i).toNat
  else p2CoefficientKappa p2CoefficientR * p2CoefficientR ^ (i - 1).toNat

/-- Its neutral part, absent on the expanding side of the Green junction. -/
noncomputable def p2GreenNeutralCoordinate (i : ℤ) : ℝ :=
  if i ≤ 0 then 0 else
    2 * (p2CoefficientKappaComplex p2CoefficientZeta * p2CoefficientZeta ^ (i - 1).toNat).re

noncomputable def p2GreenCoordinate (i : ℤ) : ℝ :=
  p2GreenStableCoordinate i + p2GreenNeutralCoordinate i

/-- The actual finite 2885-core Green configuration, with its original shift100. -/
noncomputable def p2GreenSeedCoordinate (i : ℤ) : ℝ :=
  ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) *
    p2GreenCoordinate (i - 100 - (j : ℤ))

noncomputable def p2GreenSeedStableCoordinate (i : ℤ) : ℝ :=
  ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) *
    p2GreenStableCoordinate (i - 100 - (j : ℤ))

noncomputable def p2GreenSeedNeutralCoordinate (i : ℤ) : ℝ :=
  ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) *
    p2GreenNeutralCoordinate (i - 100 - (j : ℤ))

lemma p2GreenSeedCoordinate_decomposition (i : ℤ) :
    p2GreenSeedCoordinate i = p2GreenSeedStableCoordinate i + p2GreenSeedNeutralCoordinate i := by
  simp [p2GreenSeedCoordinate, p2GreenSeedStableCoordinate, p2GreenSeedNeutralCoordinate,
    p2GreenCoordinate, mul_add, Finset.sum_add_distrib]

set_option maxRecDepth 10000 in
/-- The proved coefficient is the actual left tail of the full finite Green convolution. -/
lemma p2GreenSeedCoordinate_left_tail (n : ℕ) :
    p2GreenSeedCoordinate (-((n + 1 : ℕ) : ℤ)) =
      p2GreenSeedLeftCoefficient * p2CoefficientR ^ (n + 1) := by
  have hgreen (j : ℕ) :
      p2GreenCoordinate (-((n + 1 : ℕ) : ℤ) - 100 - (j : ℤ)) =
        -p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ (101 + (n + 1) + j) := by
    have hi : -((n + 1 : ℕ) : ℤ) - 100 - (j : ℤ) ≤ 0 := by omega
    have he : (1 - (-((n + 1 : ℕ) : ℤ) - 100 - (j : ℤ))).toNat =
        101 + (n + 1) + j := by omega
    simp only [p2GreenCoordinate, p2GreenStableCoordinate, p2GreenNeutralCoordinate,
      ite_eq_left hi, add_zero, he]
  have heval : (∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) * p2CoefficientR ^ j) =
      p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR :=
    (Polynomial.eval₂_eq_sum_range' (p := p2CoefficientSeed) (Int.castRingHom ℝ)
      (Nat.lt_succ_of_le p2CoefficientSeed_degree) p2CoefficientR).symm
  calc
    p2GreenSeedCoordinate (-((n + 1 : ℕ) : ℤ)) =
        ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) *
          (-p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ (101 + (n + 1) + j)) := by
      simp only [p2GreenSeedCoordinate, hgreen]
    _ = (-p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ 101 *
          p2CoefficientR ^ (n + 1)) *
        ∑ j ∈ Finset.range 2685, (p2CoefficientSeed.coeff j : ℝ) * p2CoefficientR ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [pow_add, pow_add]
      ring
    _ = p2GreenSeedLeftCoefficient * p2CoefficientR ^ (n + 1) := by
      rw [heval]
      dsimp [p2GreenSeedLeftCoefficient]
      ring

/-- The stable projection's actual right tail starts at the core endpoint2885. -/
lemma p2GreenSeedStableCoordinate_right_tail (n : ℕ) :
    p2GreenSeedStableCoordinate (2885 + (n : ℤ)) =
      p2GreenSeedRightCoefficient * p2CoefficientR ^ n := by
  unfold p2GreenSeedStableCoordinate p2GreenSeedRightCoefficient
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < 2685 := Finset.mem_range.mp hj
  have hi : ¬(2885 + (n : ℤ) - 100 - (j : ℤ) ≤ 0) := by omega
  have he : (2885 + (n : ℤ) - 100 - (j : ℤ) - 1).toNat =
      2885 - 101 - j + n := by omega
  simp only [p2GreenStableCoordinate, ite_eq_right hi, he, pow_add]
  ring

/-- The chosen explicit P₂ conjugate is genuinely nonreal and lies on the unit circle. -/
lemma p2CoefficientZeta_unit : ‖p2CoefficientZeta‖ = 1 ∧ 0 < p2CoefficientZeta.im := by
  let v : ℝ := 1 - Real.sqrt 2
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hv : -2 < v ∧ v < 2 := by dsimp [v]; constructor <;> nlinarith
  have hrad : 0 < 4 - v ^ 2 := by nlinarith
  have hsq := Real.sq_sqrt hrad.le
  have hnorm : ‖p2CoefficientZeta‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change (v / 2) * (v / 2) +
      (Real.sqrt (4 - v ^ 2) / 2) * (Real.sqrt (4 - v ^ 2) / 2) = 1
    nlinarith
  constructor
  · nlinarith [norm_nonneg p2CoefficientZeta]
  · change 0 < Real.sqrt (4 - v ^ 2) / 2
    positivity

lemma p2CoefficientZeta_quadratic :
    p2CoefficientZeta ^ 2 - ((1 - Real.sqrt 2 : ℝ) : ℂ) * p2CoefficientZeta + 1 = 0 := by
  let v : ℝ := 1 - Real.sqrt 2
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hrad : 0 ≤ 4 - v ^ 2 := by dsimp [v]; nlinarith
  have hsq := Real.sq_sqrt hrad
  apply Complex.ext <;> simp [p2CoefficientZeta, pow_two, Complex.mul_re, Complex.mul_im]
  · change _ = _ at hsq
    dsimp [v] at hsq
    simp only [pow_two] at hsq
    nlinarith
  · ring

/-- The exact radical used in the interval computation is a root of the actual P₂. -/
lemma p2CoefficientZeta_root :
    p2CoefficientPolynomial.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta = 0 := by
  let v : ℂ := ((1 - Real.sqrt 2 : ℝ) : ℂ)
  have hvR : (1 - Real.sqrt 2 : ℝ) ^ 2 - 2 * (1 - Real.sqrt 2) - 1 = 0 := by
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    nlinarith
  have hv : v ^ 2 - 2 * v - 1 = 0 := by
    dsimp only [v]
    exact_mod_cast hvR
  have hq : p2CoefficientZeta ^ 2 - v * p2CoefficientZeta + 1 = 0 :=
    p2CoefficientZeta_quadratic
  calc
    p2CoefficientPolynomial.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta =
        (p2CoefficientZeta ^ 2 - (2 - v) * p2CoefficientZeta + 1) *
          (p2CoefficientZeta ^ 2 - v * p2CoefficientZeta + 1) +
          (v ^ 2 - 2 * v - 1) * p2CoefficientZeta ^ 2 := by
      simp [p2CoefficientPolynomial]
      ring
    _ = 0 := by rw [hq, hv]; ring

/-- A polynomial acts on a sequence by the literal finite combination of backward shifts. -/
noncomputable def polynomialShiftAction (g : ℤ → ℝ) (i : ℤ) : Polynomial ℤ →+ ℝ where
  toFun P := P.sum fun j c => (c : ℝ) * g (i - (j : ℤ))
  map_zero' := by simp
  map_add' P Q := by
    apply Polynomial.sum_add_index
    · intro j; simp
    · intro j a b; simp [add_mul]

lemma polynomialShiftAction_X_pow (g : ℤ → ℝ) (i : ℤ) (n : ℕ) :
    polynomialShiftAction g i (Polynomial.X ^ n) = g (i - (n : ℤ)) := by
  change (Polynomial.X ^ n : Polynomial ℤ).sum (fun j c => (c : ℝ) * g (i - (j : ℤ))) = _
  rw [Polynomial.X_pow_eq_monomial, Polynomial.sum_monomial_index]
  · simp
  · simp

/-- The ten literal impulses associated with `K_b`. -/
noncomputable def p2GreenBaseCoordinate (i : ℤ) : ℝ :=
  p2GreenCoordinate i - p2GreenCoordinate (i - 1) + p2GreenCoordinate (i - 2) -
    p2GreenCoordinate (i - 3) + p2GreenCoordinate (i - 4) - p2GreenCoordinate (i - 7) +
    p2GreenCoordinate (i - 8) - p2GreenCoordinate (i - 9) +
    p2GreenCoordinate (i - 10) - p2GreenCoordinate (i - 11)

/-- The 2685-coefficient definition is exactly a sparse twenty-impulse configuration.
This identity makes a direct certified evaluation of all2885core coordinates feasible. -/
lemma p2GreenSeedCoordinate_sparse (i : ℤ) :
    p2GreenSeedCoordinate i = p2GreenBaseCoordinate (i - 100) - p2GreenBaseCoordinate (i - 2773) := by
  have hsum : p2GreenSeedCoordinate i = polynomialShiftAction p2GreenCoordinate (i - 100)
      p2CoefficientSeed := by
    symm
    change p2CoefficientSeed.sum (fun j c => (c : ℝ) * p2GreenCoordinate (i - 100 - (j : ℤ))) = _
    exact Polynomial.sum_over_range' p2CoefficientSeed (fun j => by simp) 2685
      (Nat.lt_succ_of_le p2CoefficientSeed_degree)
  have hpoly : p2CoefficientSeed =
      (Polynomial.X ^ 0 - Polynomial.X ^ 1 + Polynomial.X ^ 2 - Polynomial.X ^ 3 +
        Polynomial.X ^ 4 - Polynomial.X ^ 7 + Polynomial.X ^ 8 - Polynomial.X ^ 9 +
        Polynomial.X ^ 10 - Polynomial.X ^ 11) -
      (Polynomial.X ^ (2673 + 0) - Polynomial.X ^ (2673 + 1) + Polynomial.X ^ (2673 + 2) -
        Polynomial.X ^ (2673 + 3) + Polynomial.X ^ (2673 + 4) - Polynomial.X ^ (2673 + 7) +
        Polynomial.X ^ (2673 + 8) - Polynomial.X ^ (2673 + 9) +
        Polynomial.X ^ (2673 + 10) - Polynomial.X ^ (2673 + 11)) := by
    simp only [p2CoefficientSeed, p2CoefficientBase]
    ring
  rw [hsum, hpoly]
  simp only [map_add, map_sub, polynomialShiftAction_X_pow, Int.natCast_add,
    p2GreenBaseCoordinate]
  norm_num [sub_sub]

end Salem
