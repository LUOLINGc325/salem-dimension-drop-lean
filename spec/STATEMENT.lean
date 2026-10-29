module

public import Mathlib
public import Mathlib.Probability.ProductMeasure
public import Salem.P1ActualQuantitative
public import Salem.P2ActualQuantitative
public import Salem.QuarticDimensionCore

@[expose] public section

/-!
# Frozen endpoint statements for arXiv:2610.12072v2

The source file is `spec/paper-v2/Strict_Hausdorff-dimension_drop_for_Quartic_Salem_Bernoulli_convolutions.tex`.
The comments below cite the source lines in that v2 file.  The two theorem statements
are the exact endpoints requested by the paper (Theorems `thm:main` and
`thm:quantitative`, lines 186--206).

Both theorems are proved; the proofs are assembled from the modules under `Salem/`.
-/

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set

namespace Salem

/-- The equal-weight two-branch self-similar operator for the series in v2, lines 112--121.

The paper writes `W = ε₀ + β⁻¹ W'` with independent signs.  Its law is therefore the
fixed point of the two affine push-forwards below. -/
noncomputable def bernoulliStep (β : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.map (fun x : ℝ => β⁻¹ * x + 1) μ +
    (1 / 2 : ℝ≥0∞) • Measure.map (fun x : ℝ => β⁻¹ * x - 1) μ

/-- A probability measure satisfying the Bernoulli-convolution fixed-point equation.

This is the Mathlib measure-theoretic formulation of `ν_{β⁻¹} = Law(W)` from
v2, lines 112--121. -/
def IsBernoulliConvolution (β : ℝ) (μ : Measure ℝ) : Prop :=
  1 < β ∧ IsProbabilityMeasure μ ∧ μ = bernoulliStep β μ

/-- The symmetric sign law and its iid infinite product, used to realize the law of
`W = Σ εₖ β⁻ᵏ` directly (v2, lines 112--121). -/
noncomputable def signMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure signMeasure := by
  constructor
  rw [signMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _)]
  simpa [smul_eq_mul, one_div] using ENNReal.inv_two_add_inv_two

noncomputable def signProcess : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => signMeasure)

instance : IsProbabilityMeasure signProcess := by
  dsimp [signProcess]
  infer_instance

noncomputable def bernoulliSeries (β : ℝ) : (ℕ → ℝ) → ℝ :=
  fun ω => ∑' k : ℕ, ω k * β⁻¹ ^ k

lemma measurable_bernoulliSeries (β : ℝ) : Measurable (bernoulliSeries β) := by
  unfold bernoulliSeries
  refine Measurable.tsum (X := ℕ → ℝ) (E := ℝ) (ι := ℕ)
    (L := SummationFilter.unconditional ℕ)
    (f := fun k ω => ω k * β⁻¹ ^ k) ?_
  intro k
  fun_prop

/-- The Bernoulli convolution `ν_{β⁻¹}` from v2, lines 112--121, as the law of
the random series.  The fixed-point equation above is a later reusable theorem. -/
noncomputable def bernoulliConvolution (β : ℝ) : Measure ℝ :=
  if _hβ : 1 < β then Measure.map (bernoulliSeries β) signProcess else 0

/-- Salem's convention for the Hausdorff dimension of a measure, v2, lines 162--166:
`inf { dimH A | A is Borel and μ A = 1 }`.  `dimH` is Mathlib's Hausdorff dimension
of a set and `MeasurableSet` is Borel measurability on `ℝ`. -/
noncomputable def measureHausdorffDim (μ : Measure ℝ) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | ∃ A : Set ℝ, MeasurableSet A ∧ μ A = 1 ∧ dimH A = d}

/-- A quartic Salem number in the root-pattern form used in v2, lines 126--129 and
Proposition `prop:quartic-classification` at lines 736--743.

`P` is a monic irreducible quartic integer polynomial; its real roots are `β` and
`β⁻¹`, and the remaining conjugate pair is `ζ, star ζ` on the unit circle. -/
noncomputable def IsQuarticSalemNumber (β : ℝ) : Prop :=
  ∃ P : Polynomial ℤ, ∃ ζ : ℂ,
    P.Monic ∧
    P.natDegree = 4 ∧
    Irreducible (P.map (algebraMap ℤ ℚ)) ∧
    1 < β ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ) ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ) ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot ζ ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ) ∧
    ‖ζ‖ = 1 ∧
    ζ.im ≠ 0 ∧
    ∀ z : ℂ, (P.map (algebraMap ℤ ℂ)).IsRoot z →
      z = (β : ℂ) ∨ z = (β⁻¹ : ℂ) ∨ z = ζ ∨ z = star ζ

/-- The polynomial `P₁` in v2, equation (1.1), lines 169--174. -/
noncomputable def P1 : Polynomial ℤ :=
  Polynomial.X ^ 4 - Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X + 1

/-- The polynomial `P₂` in v2, equation (1.1), lines 169--174. -/
noncomputable def P2 : Polynomial ℤ :=
  Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 2 -
    2 * Polynomial.X + 1

/-- The explicit parameter `β₁` from v2, lines 176--182 (the larger root of `P₁`). -/
noncomputable def beta1 : ℝ :=
  let u : ℝ := (1 + Real.sqrt 13) / 2
  (u + Real.sqrt (u ^ 2 - 4)) / 2

/-- The explicit parameter `β₂` from v2, lines 176--182 (the larger root of `P₂`). -/
noncomputable def beta2 : ℝ :=
  let u : ℝ := 1 + Real.sqrt 2
  (u + Real.sqrt (u ^ 2 - 4)) / 2

/- Amendment 001: proved nondegeneracy guards. -/
theorem bernoulliConvolution_isBernoulliConvolution (β : ℝ) :
    1 < β → IsBernoulliConvolution β (bernoulliConvolution β) := by
  intro hβ
  have ae_signProcess_abs : ∀ᵐ ω ∂signProcess, ∀ n : ℕ, |ω n| = 1 := by
    apply ae_all_iff.2
    intro n
    have hs : ∀ᵐ x ∂signMeasure, |x| = 1 := by
      simp [signMeasure, ae_add_measure_iff]
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => signMeasure) n).quasiMeasurePreserving.ae hs

  have summable_bernoulliSeries (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
      (hω : ∀ n, |ω n| = 1) : Summable (fun k => ω k * β⁻¹ ^ k) := by
    have hb : |β⁻¹| < 1 := by
      rw [abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one hβ))]
      exact inv_lt_one_of_one_lt₀ hβ
    apply Summable.of_norm
    convert (summable_geometric_of_abs_lt_one hb) using 1
    ext k
    rw [norm_mul, Real.norm_eq_abs, hω k, one_mul]
    simp [abs_of_pos (lt_trans zero_lt_one hβ)]

  have bernoulliSeries_recursion (β : ℝ) (hβ : 1 < β) (ω : ℕ → ℝ)
      (hω : ∀ n, |ω n| = 1) :
      bernoulliSeries β ω = ω 0 + β⁻¹ * bernoulliSeries β (fun n => ω (n+1)) := by
    have hs := summable_bernoulliSeries β hβ ω hω
    unfold bernoulliSeries
    rw [← hs.sum_add_tsum_nat_add 1]
    simp only [Finset.sum_range_one, pow_zero, mul_one]
    congr 1
    rw [← tsum_mul_left]
    congr 1
    ext n
    rw [pow_succ]
    ring

  have signProcess_tail_law :
      Measure.map (fun (ω : ℕ → ℝ) n => ω (n+1)) signProcess = signProcess := by
    exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => signMeasure)
      (f := fun n : ℕ => n+1) (by intro a b h; exact Nat.add_right_cancel h)

  have signProcess_head_tail_indep :
      ProbabilityTheory.IndepFun (fun (ω : ℕ → ℝ) => ω 0)
        (fun (ω : ℕ → ℝ) n => ω (n+1)) signProcess := by
    have hi : ProbabilityTheory.iIndepFun (fun n (ω : ℕ → ℝ) => ω n) signProcess :=
      ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => signMeasure) (X := fun (_ : ℕ) (x : ℝ) => x) (by fun_prop)
    have h := hi.indepFun_set ({0} : Set ℕ) {n : ℕ | n ≠ 0} (by simp) (by fun_prop)
    exact h.comp (measurable_pi_apply (⟨0, by simp⟩ : ({0} : Set ℕ)))
      (show Measurable (fun (v : {n : ℕ // n ≠ 0} → ℝ) n =>
        v ⟨n+1, by omega⟩) from by fun_prop)

  have signProcess_series_tail_law (β : ℝ) :
      Measure.map (fun ω => bernoulliSeries β (fun n => ω (n+1))) signProcess =
        Measure.map (bernoulliSeries β) signProcess := by
    rw [← Function.comp_def, ← Measure.map_map (measurable_bernoulliSeries β)
      (by fun_prop), signProcess_tail_law]

  have signProcess_head_series_tail_joint (β : ℝ) :
      Measure.map (fun ω => (ω 0, bernoulliSeries β (fun n => ω (n+1)))) signProcess =
        signMeasure.prod (Measure.map (bernoulliSeries β) signProcess) := by
    have hi := signProcess_head_tail_indep.comp measurable_id (measurable_bernoulliSeries β)
    change ProbabilityTheory.IndepFun (fun (ω : ℕ → ℝ) => ω 0)
      (fun ω => bernoulliSeries β (fun n => ω (n+1))) signProcess at hi
    calc
      _ = (Measure.map (fun (ω : ℕ → ℝ) => ω 0) signProcess).prod
          (Measure.map (fun ω => bernoulliSeries β (fun n => ω (n+1))) signProcess) :=
        hi.map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
          ((measurable_bernoulliSeries β).comp (by fun_prop)).aemeasurable
      _ = _ := by
        rw [show Measure.map (fun (ω : ℕ → ℝ) => ω 0) signProcess = signMeasure from
          Measure.infinitePi_map_eval (fun _ : ℕ => signMeasure) 0]
        exact congrArg (Measure.prod signMeasure) (signProcess_series_tail_law β)

  have signMeasure_prod_affine (β : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
      Measure.map (fun p : ℝ × ℝ => p.1 + β⁻¹ * p.2) (signMeasure.prod μ) =
        bernoulliStep β μ := by
    unfold signMeasure bernoulliStep
    rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
      Measure.map_add _ _ (by fun_prop), Measure.map_smul _ (by fun_prop),
      Measure.map_smul _ (by fun_prop), Measure.dirac_prod, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 2 <;> congr 1 <;> ext x <;> dsimp <;> ring

  have bernoulliSeries_law_fixedpoint (β : ℝ) (hβ : 1 < β) :
      Measure.map (bernoulliSeries β) signProcess =
        bernoulliStep β (Measure.map (bernoulliSeries β) signProcess) := by
    calc
      _ = Measure.map (fun ω => ω 0 + β⁻¹ * bernoulliSeries β (fun n => ω (n+1)))
          signProcess := by
        apply Measure.map_congr
        filter_upwards [ae_signProcess_abs] with ω hω
        exact bernoulliSeries_recursion β hβ ω hω
      _ = Measure.map (fun p : ℝ × ℝ => p.1 + β⁻¹ * p.2)
          (Measure.map (fun ω => (ω 0, bernoulliSeries β (fun n => ω (n+1))))
            signProcess) := by
        exact (Measure.map_map (show Measurable (fun p : ℝ × ℝ => p.1 + β⁻¹ * p.2)
          from by fun_prop) (show Measurable (fun (ω : ℕ → ℝ) =>
            (ω 0, bernoulliSeries β (fun n => ω (n+1)))) from
              (measurable_pi_apply 0).prodMk
                ((measurable_bernoulliSeries β).comp (by fun_prop)))).symm
      _ = _ := by rw [signProcess_head_series_tail_joint, signMeasure_prod_affine]
  rw [bernoulliConvolution, dite_eq_left hβ]
  exact ⟨hβ, inferInstance, bernoulliSeries_law_fixedpoint β hβ⟩


open Polynomial in
/-- The first explicit parameter has the frozen quartic Salem root pattern. -/
theorem isQuarticSalemNumber_beta1 : IsQuarticSalemNumber beta1 := by
  have hmonic : P1.Monic := by
    unfold P1
    monicity <;> norm_num
  have hdeg : P1.natDegree = 4 := by
    unfold P1
    compute_degree <;> norm_num
  have hirr : Irreducible (P1.map (algebraMap ℤ ℚ)) := by
    apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp
    apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap ℤ (ZMod 2)) P1 hmonic
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have heq : P1.map (algebraMap ℤ (ZMod 2)) = cyclotomic 5 (ZMod 2) := by
      norm_num [P1, cyclotomic_prime, Finset.sum_range_succ]
      ext n
      simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
      split_ifs <;> simp_all
    rw [heq]
    apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5) (by decide) dvd_rfl
    rw [natDegree_cyclotomic]
    symm
    apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  have root_pattern  {P : Polynomial ℤ} {β u v : ℝ}
      (hβ : 1 < β) (hbq : β ^ 2 - u * β + 1 = 0)
      (hvlo : -2 < v) (hvhi : v < 2)
      (hfactor : P.map (algebraMap ℤ ℂ) =
        (X ^ 2 - C (u : ℂ) * X + 1) * (X ^ 2 - C (v : ℂ) * X + 1)) :
      ∃ ζ : ℂ,
        (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ) ∧
        (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ) ∧
        (P.map (algebraMap ℤ ℂ)).IsRoot ζ ∧
        (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ) ∧
        ‖ζ‖ = 1 ∧ ζ.im ≠ 0 ∧
        ∀ z : ℂ, (P.map (algebraMap ℤ ℂ)).IsRoot z →
          z = (β : ℂ) ∨ z = (β⁻¹ : ℂ) ∨ z = ζ ∨ z = star ζ := by
    have hb0 : β ≠ 0 := by linarith
    have hbsum : β + β⁻¹ = u := by
      apply (mul_right_cancel₀ hb0)
      rw [add_mul, inv_mul_cancel₀ hb0]
      nlinarith [hbq]
    let ζ : ℂ := ⟨v / 2, Real.sqrt (4 - v ^ 2) / 2⟩
    have hvpos : 0 < 4 - v ^ 2 := by nlinarith
    have hsqrt : (Real.sqrt (4 - v ^ 2)) ^ 2 = 4 - v ^ 2 :=
      Real.sq_sqrt (le_of_lt hvpos)
    have hζsum : ζ + star ζ = (v : ℂ) := by
      apply Complex.ext <;> simp [ζ]
    have hζprod : ζ * star ζ = (1 : ℂ) := by
      apply Complex.ext <;> simp [ζ, Complex.mul_re, Complex.mul_im] <;> nlinarith [hsqrt]
    have hζnorm : ‖ζ‖ = 1 := by
      have hnorm : ‖ζ‖ ^ 2 = 1 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        dsimp [ζ]
        nlinarith [hsqrt]
      nlinarith [norm_nonneg ζ]
    have hζim : ζ.im ≠ 0 := by
      dsimp [ζ]
      have := Real.sqrt_pos.mpr hvpos
      positivity
    have hβsumC : (β : ℂ) + (β⁻¹ : ℂ) = (u : ℂ) := by exact_mod_cast hbsum
    have hβprodC : (β : ℂ) * (β⁻¹ : ℂ) = (1 : ℂ) := by
      exact_mod_cast mul_inv_cancel₀ hb0
    have hlinβ : (X ^ 2 - C (u : ℂ) * X + 1 : Polynomial ℂ) =
        (X - C (β : ℂ)) * (X - C (β⁻¹ : ℂ)) := by
      rw [← hβsumC, C_add]
      have hp : C (β : ℂ) * C (β⁻¹ : ℂ) = (1 : Polynomial ℂ) := by
        rw [← C_mul, hβprodC, C_1]
      linear_combination -hp
    have hlinζ : (X ^ 2 - C (v : ℂ) * X + 1 : Polynomial ℂ) =
        (X - C ζ) * (X - C (star ζ)) := by
      rw [← hζsum, C_add]
      have hp : C ζ * C (star ζ) = (1 : Polynomial ℂ) := by
        rw [← C_mul, hζprod, C_1]
      linear_combination -hp
    have hfull : P.map (algebraMap ℤ ℂ) =
        ((X - C (β : ℂ)) * (X - C (β⁻¹ : ℂ))) *
          ((X - C ζ) * (X - C (star ζ))) := by
      rw [hfactor, hlinβ, hlinζ]
    refine ⟨ζ, ?_, ?_, ?_, ?_, hζnorm, hζim, ?_⟩
    · rw [hfull]; simp [IsRoot.def]
    · rw [hfull]; simp [IsRoot.def]
    · rw [hfull]; simp [IsRoot.def]
    · rw [hfull]; simp [IsRoot.def]
    · intro z hz
      rw [hfull] at hz
      simpa [IsRoot.def, mul_eq_zero, sub_eq_zero, or_assoc] using hz

  let u : ℝ := (1 + Real.sqrt 13) / 2
  let v : ℝ := (1 - Real.sqrt 13) / 2
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have hsn : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
  have hslo : (3 : ℝ) < Real.sqrt 13 := by nlinarith
  have hshi : (Real.sqrt 13 : ℝ) < 4 := by nlinarith
  have hu : 2 < u := by dsimp [u]; linarith
  have hrad : 0 ≤ u ^ 2 - 4 := by nlinarith
  have hsq : (Real.sqrt (u ^ 2 - 4)) ^ 2 = u ^ 2 - 4 := Real.sq_sqrt hrad
  have hsqnonneg : 0 ≤ Real.sqrt (u ^ 2 - 4) := Real.sqrt_nonneg _
  have hβ : 1 < beta1 := by change 1 < (u + Real.sqrt (u ^ 2 - 4)) / 2; linarith
  have hbq : beta1 ^ 2 - u * beta1 + 1 = 0 := by
    change ((u + Real.sqrt (u ^ 2 - 4)) / 2) ^ 2 -
      u * ((u + Real.sqrt (u ^ 2 - 4)) / 2) + 1 = 0
    nlinarith [hsq]
  have hvlo : -2 < v := by dsimp [v]; linarith
  have hvhi : v < 2 := by dsimp [v]; linarith
  have hfactor : P1.map (algebraMap ℤ ℂ) =
      (X ^ 2 - C (u : ℂ) * X + 1) * (X ^ 2 - C (v : ℂ) * X + 1) := by
    have hsum : u + v = 1 := by dsimp [u,v]; ring
    have hprod : u * v = -3 := by dsimp [u,v]; nlinarith [hs]
    have hsumC : C (u : ℂ) + C (v : ℂ) = (1 : Polynomial ℂ) := by
      rw [← C_add, ← Complex.ofReal_add, hsum, Complex.ofReal_one, C_1]
    have hprodC : C (u : ℂ) * C (v : ℂ) = (-3 : Polynomial ℂ) := by
      rw [← C_mul, ← Complex.ofReal_mul, hprod]
      norm_num [Polynomial.C_ofNat]
    simp only [P1, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    linear_combination (X ^ 3 + X) * hsumC - X ^ 2 * hprodC
  obtain ⟨ζ, hζ⟩ := root_pattern hβ hbq hvlo hvhi hfactor
  exact ⟨P1, ζ, hmonic, hdeg, hirr, hβ, hζ⟩

open Polynomial in
theorem isQuarticSalemNumber_beta2 : IsQuarticSalemNumber beta2 := by
  have hmonic : P2.Monic := by
    dsimp [P2]
    monicity <;> norm_num
  have hdeg : P2.natDegree = 4 := by
    dsimp [P2]
    compute_degree!
  have hirr : Irreducible (P2.map (algebraMap ℤ ℚ)) := by
    apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp
    apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap ℤ (ZMod 3)) P2 hmonic
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have heq : P2.map (algebraMap ℤ (ZMod 3)) = cyclotomic 5 (ZMod 3) := by
      norm_num [P2, cyclotomic_prime, Finset.sum_range_succ]
      ext n
      simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
      split_ifs <;> simp_all [coeff_X] <;> decide
    rw [heq]
    apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 3) (n := 5) (by decide) dvd_rfl
    rw [natDegree_cyclotomic]
    norm_num
    symm
    apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  have root_pattern {P : Polynomial ℤ} {β u v : ℝ}
      (hβ : 1 < β) (hbq : β ^ 2 - u * β + 1 = 0)
      (hvlo : -2 < v) (hvhi : v < 2)
      (hfactor : P.map (algebraMap ℤ ℂ) =
        (X ^ 2 - C (u : ℂ) * X + 1) * (X ^ 2 - C (v : ℂ) * X + 1)) :
      ∃ ζ : ℂ,
        (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ) ∧
        (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ) ∧
        (P.map (algebraMap ℤ ℂ)).IsRoot ζ ∧
        (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ) ∧
        ‖ζ‖ = 1 ∧ ζ.im ≠ 0 ∧
        ∀ z : ℂ, (P.map (algebraMap ℤ ℂ)).IsRoot z →
          z = (β : ℂ) ∨ z = (β⁻¹ : ℂ) ∨ z = ζ ∨ z = star ζ := by
    have hb0 : β ≠ 0 := by linarith
    have hbsum : β + β⁻¹ = u := by
      apply (mul_right_cancel₀ hb0)
      rw [add_mul, inv_mul_cancel₀ hb0]
      nlinarith [hbq]
    let ζ : ℂ := ⟨v / 2, Real.sqrt (4 - v ^ 2) / 2⟩
    have hvpos : 0 < 4 - v ^ 2 := by nlinarith
    have hsqrt : (Real.sqrt (4 - v ^ 2)) ^ 2 = 4 - v ^ 2 :=
      Real.sq_sqrt (le_of_lt hvpos)
    have hζsum : ζ + star ζ = (v : ℂ) := by
      apply Complex.ext <;> simp [ζ]
    have hζprod : ζ * star ζ = (1 : ℂ) := by
      apply Complex.ext <;> simp [ζ, Complex.mul_re, Complex.mul_im] <;> nlinarith [hsqrt]
    have hζnorm : ‖ζ‖ = 1 := by
      have hnorm : ‖ζ‖ ^ 2 = 1 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        dsimp [ζ]
        nlinarith [hsqrt]
      nlinarith [norm_nonneg ζ]
    have hζim : ζ.im ≠ 0 := by
      dsimp [ζ]
      have := Real.sqrt_pos.mpr hvpos
      positivity
    have hβsumC : (β : ℂ) + (β⁻¹ : ℂ) = (u : ℂ) := by exact_mod_cast hbsum
    have hβprodC : (β : ℂ) * (β⁻¹ : ℂ) = (1 : ℂ) := by
      exact_mod_cast mul_inv_cancel₀ hb0
    have hlinβ : (X ^ 2 - C (u : ℂ) * X + 1 : Polynomial ℂ) =
        (X - C (β : ℂ)) * (X - C (β⁻¹ : ℂ)) := by
      rw [← hβsumC, C_add]
      have hp : C (β : ℂ) * C (β⁻¹ : ℂ) = (1 : Polynomial ℂ) := by
        rw [← C_mul, hβprodC, C_1]
      linear_combination -hp
    have hlinζ : (X ^ 2 - C (v : ℂ) * X + 1 : Polynomial ℂ) =
        (X - C ζ) * (X - C (star ζ)) := by
      rw [← hζsum, C_add]
      have hp : C ζ * C (star ζ) = (1 : Polynomial ℂ) := by
        rw [← C_mul, hζprod, C_1]
      linear_combination -hp
    have hfull : P.map (algebraMap ℤ ℂ) =
        ((X - C (β : ℂ)) * (X - C (β⁻¹ : ℂ))) *
          ((X - C ζ) * (X - C (star ζ))) := by
      rw [hfactor, hlinβ, hlinζ]
    refine ⟨ζ, ?_, ?_, ?_, ?_, hζnorm, hζim, ?_⟩
    · rw [hfull]; simp [IsRoot.def]
    · rw [hfull]; simp [IsRoot.def]
    · rw [hfull]; simp [IsRoot.def]
    · rw [hfull]; simp [IsRoot.def]
    · intro z hz
      rw [hfull] at hz
      simpa [IsRoot.def, mul_eq_zero, sub_eq_zero, or_assoc] using hz

  let u : ℝ := 1 + Real.sqrt 2
  let v : ℝ := 1 - Real.sqrt 2
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hsnonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsone : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hslt : Real.sqrt 2 < (2 : ℝ) := by nlinarith
  have hβ : 1 < beta2 := by
    dsimp [beta2]
    have := Real.sqrt_nonneg ((1 + Real.sqrt 2) ^ 2 - 4)
    nlinarith
  have hbq : beta2 ^ 2 - u * beta2 + 1 = 0 := by
    dsimp [beta2, u]
    have hu : 0 ≤ (1 + Real.sqrt 2 : ℝ) ^ 2 - 4 := by nlinarith
    have hv := Real.sq_sqrt hu
    nlinarith
  have hvlo : -2 < v := by dsimp [v]; linarith
  have hvhi : v < 2 := by dsimp [v]; linarith
  have huvsum : u + v = 2 := by dsimp [u, v]; ring
  have huvprod : u * v = -1 := by dsimp [u, v]; nlinarith [hs]
  have hfactor : P2.map (algebraMap ℤ ℂ) =
      (X ^ 2 - C (u : ℂ) * X + 1) * (X ^ 2 - C (v : ℂ) * X + 1) := by
    have hsumC : (u : ℂ) + (v : ℂ) = 2 := by exact_mod_cast huvsum
    have hprodC : (u : ℂ) * (v : ℂ) = -1 := by exact_mod_cast huvprod
    have hsum : C (u : ℂ) + C (v : ℂ) = (2 : Polynomial ℂ) := by
      rw [← C_add, hsumC, Polynomial.C_ofNat]
    have hprod : C (u : ℂ) * C (v : ℂ) = (-1 : Polynomial ℂ) := by
      rw [← C_mul, hprodC]; norm_num
    simp only [P2, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_X]
    linear_combination (X ^ 3 + X) * hsum - X ^ 2 * hprod
  obtain ⟨ζ, hζ⟩ := root_pattern hβ hbq hvlo hvhi hfactor
  exact ⟨P2, ζ, hmonic, hdeg, hirr, hβ, hζ⟩

/- End Amendment 001 guards. -/

/-- v2 Theorem `thm:main`, lines 186--191. -/
theorem main (β : ℝ) (hβ : IsQuarticSalemNumber β) :
    measureHausdorffDim (bernoulliConvolution β) < 1 := by
  have h1 : ∃ F : Set ℝ, MeasurableSet F ∧
      ElementaryCore.bernoulliLaw QuarticCore.beta1 F = 1 ∧ dimH F < 1 := by
    have hquartic : QuarticCore.IsQuarticSalemNumber QuarticCore.beta1 :=
      isQuarticSalemNumber_beta1
    obtain ⟨F, hFm, hFmass, hFdim⟩ :=
      QuarticCore.exists_actual_quantitative_beta1_cover hquartic
    refine ⟨F, hFm, hFmass, hFdim.trans ?_⟩
    have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num : (1-(14 : ℝ)/10^24) < 1)
    simpa only [ENNReal.ofReal_one] using h
  have h2 : ∃ F : Set ℝ, MeasurableSet F ∧
      ElementaryCore.bernoulliLaw QuarticCore.beta2 F = 1 ∧ dimH F < 1 := by
    obtain ⟨F, hFm, hFmass, hFdim⟩ :=
      p2Actual_exists_quantitative_cover
    refine ⟨F, hFm, hFmass, hFdim.trans ?_⟩
    have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num : (1-(78 : ℝ)/10^23) < 1)
    simpa only [ENNReal.ofReal_one] using h
  have hquartic : QuarticCore.IsQuarticSalemNumber β := hβ
  obtain ⟨F, hFm, hFmass, hFdim⟩ := quartic_fullMass_dim_drop_of_two_covers h1 h2 hquartic
  have hb : 1 < β := by obtain ⟨_, _, _, _, _, hb, _⟩ := hβ; exact hb
  have hlaw : bernoulliConvolution β = ElementaryCore.bernoulliLaw β := by
    rw [bernoulliConvolution, dite_eq_left hb]
    rfl
  have hle : measureHausdorffDim (bernoulliConvolution β) ≤ dimH F := by
    exact sInf_le ⟨F, hFm, by simpa only [hlaw] using hFmass, rfl⟩
  exact hle.trans_lt hFdim

/-- v2 Theorem `thm:quantitative`, lines 199--206.

The rational forms are exact: `14 / 10^24 = 1.4·10⁻²³` and
`78 / 10^23 = 7.8·10⁻²²`. -/
theorem main_quantitative :
    measureHausdorffDim (bernoulliConvolution beta1) <
        (1 : ℝ≥0∞) - (14 : ℝ≥0∞) / 10 ^ 24 ∧
      measureHausdorffDim (bernoulliConvolution beta2) <
        (1 : ℝ≥0∞) - (78 : ℝ≥0∞) / 10 ^ 23 := by
  constructor
  · have hquartic : QuarticCore.IsQuarticSalemNumber QuarticCore.beta1 :=
      isQuarticSalemNumber_beta1
    obtain ⟨F, hFm, hFmass, hFdim⟩ :=
      QuarticCore.exists_actual_quantitative_beta1_cover hquartic
    have hb : 1 < beta1 := QuarticCore.one_lt_beta1
    have hlaw : bernoulliConvolution beta1 = ElementaryCore.bernoulliLaw QuarticCore.beta1 := by
      rw [bernoulliConvolution, dite_eq_left hb]
      rfl
    have hle : measureHausdorffDim (bernoulliConvolution beta1) ≤ dimH F := by
      exact sInf_le ⟨F, hFm, by simpa only [hlaw] using hFmass, rfl⟩
    have hconversion : ENNReal.ofReal (1-(14 : ℝ)/10^24) =
        (1 : ENNReal) - (14 : ENNReal)/10^24 := by
      rw [ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 14/10^24),
        ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    exact hle.trans_lt (hFdim.trans_eq hconversion)
  · obtain ⟨F, hFm, hFmass, hFdim⟩ :=
      p2Actual_exists_quantitative_cover
    have hb : 1 < beta2 := QuarticCore.one_lt_beta2
    have hlaw : bernoulliConvolution beta2 = ElementaryCore.bernoulliLaw QuarticCore.beta2 := by
      rw [bernoulliConvolution, dite_eq_left hb]
      rfl
    have hle : measureHausdorffDim (bernoulliConvolution beta2) ≤ dimH F := by
      exact sInf_le ⟨F, hFm, by simpa only [hlaw] using hFmass, rfl⟩
    have hconversion : ENNReal.ofReal (1-(78 : ℝ)/10^23) =
        (1 : ENNReal) - (78 : ENNReal)/10^23 := by
      rw [ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 78/10^23),
        ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    exact hle.trans_lt (hFdim.trans_eq hconversion)

end Salem
