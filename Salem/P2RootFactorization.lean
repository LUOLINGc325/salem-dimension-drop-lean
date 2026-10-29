module

public import Salem.P2GreenCore

@[expose] public section

open Polynomial
open scoped BigOperators

namespace Salem

/-- The four actual P₂ roots, in expanding, stable, upper and lower unit-circle order. -/
noncomputable def p2GreenRoot : Fin 4 → ℂ :=
  ![(p2CoefficientBeta : ℂ), (p2CoefficientR : ℂ), p2CoefficientZeta, star p2CoefficientZeta]

/-- The literal expanding radical satisfies the trace quadratic for `u=1+√2`. -/
lemma p2CoefficientBeta_quadratic :
    p2CoefficientBeta ^ 2 - (1 + Real.sqrt 2) * p2CoefficientBeta + 1 = 0 := by
  dsimp [p2CoefficientBeta]
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hrad : 0 ≤ (1 + Real.sqrt 2 : ℝ) ^ 2 - 4 := by nlinarith
  have hsq := Real.sq_sqrt hrad
  nlinarith

/-- Exact trace and product of the two actual real P₂ roots. -/
lemma p2CoefficientBetaR_trace_product :
    p2CoefficientBeta + p2CoefficientR = 1 + Real.sqrt 2 ∧
      p2CoefficientBeta * p2CoefficientR = 1 := by
  have hβ0 : p2CoefficientBeta ≠ 0 := by linarith [p2CoefficientBeta_lower]
  have hprod : p2CoefficientBeta * p2CoefficientR = 1 := by
    exact mul_inv_cancel₀ hβ0
  refine ⟨?_, hprod⟩
  apply mul_right_cancel₀ hβ0
  have hq := p2CoefficientBeta_quadratic
  nlinarith [hprod]

/-- Exact trace and product of the explicitly chosen unit conjugates. -/
lemma p2CoefficientZeta_trace_product :
    p2CoefficientZeta + star p2CoefficientZeta = ((1 - Real.sqrt 2 : ℝ) : ℂ) ∧
      p2CoefficientZeta * star p2CoefficientZeta = 1 := by
  constructor
  · apply Complex.ext <;> simp [p2CoefficientZeta]
  · calc
      _ = (Complex.normSq p2CoefficientZeta : ℂ) := Complex.mul_conj _
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, p2CoefficientZeta_unit.1]; norm_num

/-- The expanding and stable real roots and the two nonreal unit roots are all distinct. -/
lemma p2GreenRoot_injective : Function.Injective p2GreenRoot := by
  have hβr : (p2CoefficientBeta : ℂ) ≠ (p2CoefficientR : ℂ) := by
    intro h
    have hh := Complex.ofReal_injective h
    linarith [p2CoefficientBeta_lower, p2CoefficientR_bounds.2]
  have hrealζ (x : ℝ) : (x : ℂ) ≠ p2CoefficientZeta := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.ofReal_im] at hh
    linarith [p2CoefficientZeta_unit.2]
  have hrealstar (x : ℝ) : (x : ℂ) ≠ star p2CoefficientZeta := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.star_def, Complex.conj_im] at hh
    linarith [p2CoefficientZeta_unit.2]
  have hζstar : p2CoefficientZeta ≠ star p2CoefficientZeta := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith [p2CoefficientZeta_unit.2]
  have hβζ := hrealζ p2CoefficientBeta
  have hrζ := hrealζ p2CoefficientR
  have hβstar := hrealstar p2CoefficientBeta
  have hrstar := hrealstar p2CoefficientR
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [p2GreenRoot]

/-- None of the four actual roots vanishes, as required for bilateral spectral powers. -/
lemma p2GreenRoot_ne_zero (i : Fin 4) : p2GreenRoot i ≠ 0 := by
  have hβ : (p2CoefficientBeta : ℂ) ≠ 0 := by
    exact_mod_cast (show p2CoefficientBeta ≠ 0 by linarith [p2CoefficientBeta_lower])
  have hr : (p2CoefficientR : ℂ) ≠ 0 := by exact_mod_cast p2CoefficientR_bounds.1.ne'
  have hζ : p2CoefficientZeta ≠ 0 := by
    intro h
    have hh := p2CoefficientZeta_unit.1
    simp [h] at hh
  have hs : star p2CoefficientZeta ≠ 0 := star_ne_zero.mpr hζ
  fin_cases i <;> simp_all [p2GreenRoot]

/-- The actual P₂ is exactly the product over its four explicit simple roots.
This is the input needed by the shared Green-kernel moment and forcing theorems. -/
lemma p2GreenRoot_factorization :
    p2CoefficientPolynomial.map (Int.castRingHom ℂ) =
      ∏ i : Fin 4, (X - C (p2GreenRoot i)) := by
  let u : ℝ := 1 + Real.sqrt 2
  let v : ℝ := 1 - Real.sqrt 2
  have hsum : u + v = 2 := by dsimp [u, v]; ring
  have hprod : u * v = -1 := by
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    dsimp [u, v]
    nlinarith [hs]
  have hβsum : (p2CoefficientBeta : ℂ) + (p2CoefficientR : ℂ) = (u : ℂ) := by
    exact_mod_cast p2CoefficientBetaR_trace_product.1
  have hβprod : (p2CoefficientBeta : ℂ) * (p2CoefficientR : ℂ) = 1 := by
    exact_mod_cast p2CoefficientBetaR_trace_product.2
  have hζsum : p2CoefficientZeta + star p2CoefficientZeta = (v : ℂ) :=
    p2CoefficientZeta_trace_product.1
  have hζprod : p2CoefficientZeta * star p2CoefficientZeta = 1 :=
    p2CoefficientZeta_trace_product.2
  have hlinβ : (X ^ 2 - C (u : ℂ) * X + 1 : Polynomial ℂ) =
      (X - C (p2CoefficientBeta : ℂ)) * (X - C (p2CoefficientR : ℂ)) := by
    rw [← hβsum, C_add]
    have hp : C (p2CoefficientBeta : ℂ) * C (p2CoefficientR : ℂ) = (1 : Polynomial ℂ) := by
      rw [← C_mul, hβprod, C_1]
    linear_combination -hp
  have hlinζ : (X ^ 2 - C (v : ℂ) * X + 1 : Polynomial ℂ) =
      (X - C p2CoefficientZeta) * (X - C (star p2CoefficientZeta)) := by
    rw [← hζsum, C_add]
    have hp : C p2CoefficientZeta * C (star p2CoefficientZeta) = (1 : Polynomial ℂ) := by
      rw [← C_mul, hζprod, C_1]
    linear_combination -hp
  have hfactor : p2CoefficientPolynomial.map (Int.castRingHom ℂ) =
      (X ^ 2 - C (u : ℂ) * X + 1) * (X ^ 2 - C (v : ℂ) * X + 1) := by
    have hsumC : (u : ℂ) + (v : ℂ) = 2 := by exact_mod_cast hsum
    have hprodC : (u : ℂ) * (v : ℂ) = -1 := by exact_mod_cast hprod
    have hs : C (u : ℂ) + C (v : ℂ) = (2 : Polynomial ℂ) := by
      rw [← C_add, hsumC, C_ofNat]
    have hp : C (u : ℂ) * C (v : ℂ) = (-1 : Polynomial ℂ) := by
      rw [← C_mul, hprodC]
      norm_num
    simp only [p2CoefficientPolynomial, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_X]
    linear_combination (X ^ 3 + X) * hs - X ^ 2 * hp
  rw [hfactor, hlinβ, hlinζ]
  norm_num [p2GreenRoot, Fin.prod_univ_succ]
  ring

/-- Every enumerated actual root is a root of the actual mapped P₂ polynomial. -/
lemma p2GreenRoot_isRoot (i : Fin 4) :
    (p2CoefficientPolynomial.map (Int.castRingHom ℂ)).IsRoot (p2GreenRoot i) := by
  rw [p2GreenRoot_factorization]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

end Salem
