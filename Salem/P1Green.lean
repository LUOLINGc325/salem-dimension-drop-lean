module

public import Salem.P1Analytic
public import Salem.P1Returns
public import Salem.P1Wave
public import Salem.GreenKernel
public import Salem.AtomSeparation

@[expose] public section

open scoped BigOperators
open Polynomial
namespace Salem
/-- The source P1 polynomial, restated in a cycle-free analytic module. -/
noncomputable def p1GreenPolynomial : Polynomial ℤ := X ^ 4 - X ^ 3 - X ^ 2 - X + 1
theorem p1GreenPolynomial_monic : p1GreenPolynomial.Monic := by
  dsimp [p1GreenPolynomial]
  monicity <;> norm_num
theorem p1GreenPolynomial_natDegree : p1GreenPolynomial.natDegree = 4 := by
  dsimp [p1GreenPolynomial]
  compute_degree <;> norm_num
theorem p1GreenPolynomial_eval (z : ℂ) :
    (p1GreenPolynomial.map (Int.castRingHom ℂ)).eval z = z ^ 4 - z ^ 3 - z ^ 2 - z + 1 := by
  simp [p1GreenPolynomial]
theorem p1GreenPolynomial_real_root {b : ℝ}
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (p1GreenPolynomial.map (Int.castRingHom ℂ)).IsRoot (b : ℂ) := by
  rw [Polynomial.IsRoot, p1GreenPolynomial_eval]
  exact_mod_cast hroot
theorem p1GreenPolynomial_inv_root {b : ℝ} (hb : b ≠ 0)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (p1GreenPolynomial.map (Int.castRingHom ℂ)).IsRoot ((b⁻¹ : ℝ) : ℂ) := by
  apply p1GreenPolynomial_real_root
  field_simp [hb]
  linear_combination hroot
theorem p1GreenPolynomial_neutral_root :
    (p1GreenPolynomial.map (Int.castRingHom ℂ)).IsRoot p1NeutralRoot := by
  rw [Polynomial.IsRoot, p1GreenPolynomial_eval]
  exact p1NeutralRoot_quartic
theorem p1GreenPolynomial_conjugate_root :
    (p1GreenPolynomial.map (Int.castRingHom ℂ)).IsRoot (star p1NeutralRoot) := by
  rw [Polynomial.IsRoot, p1GreenPolynomial_eval]
  simpa using congrArg star p1NeutralRoot_quartic
/-- The actual expanding parameter and certified neutral root supply the
complete four-root factorization used by the spectral Green sequence. -/
theorem p1Green_factorization {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    p1GreenPolynomial.map (Int.castRingHom ℂ) =
      ∏ i : Fin 4, (X - C (quarticSalemRoots b p1NeutralRoot i)) := by
  have him : p1NeutralRoot.im ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num) p1NeutralRoot_im_bounds.1)
  exact quartic_factorization_of_root_pattern p1GreenPolynomial p1GreenPolynomial_monic
    p1GreenPolynomial_natDegree (by linarith [hb]) p1NeutralRoot him
    (p1GreenPolynomial_real_root hroot)
    (p1GreenPolynomial_inv_root (ne_of_gt (by linarith [hb])) hroot)
    p1GreenPolynomial_neutral_root p1GreenPolynomial_conjugate_root
/-- Exact cleared identity for the four forcing impulses at `-7,-4,4,7`. -/
theorem p1_four_impulse_identity_cleared {R : Type*} [CommRing R] (x : R) :
    x ^ 14 - x ^ 11 - x ^ 3 + 1 - x ^ 4 * (x ^ 2 + x + 1) ^ 3 =
      (x ^ 10 + x ^ 9 + 2 * x ^ 8 + 3 * x ^ 7 + 4 * x ^ 6 + 5 * x ^ 5 +
        4 * x ^ 4 + 3 * x ^ 3 + 2 * x ^ 2 + x + 1) *
        (x ^ 4 - x ^ 3 - x ^ 2 - x + 1) := by ring
/-- At every nonzero P1 root, the four-impulse Laurent polynomial is
exactly the original power seed `U₁³`. -/
theorem p1_four_impulse_identity_at_root {K : Type*} [Field K] {x : K} (hx : x ≠ 0)
    (hroot : x ^ 4 - x ^ 3 - x ^ 2 - x + 1 = 0) :
    x ^ 7 - x ^ 4 - (x⁻¹) ^ 4 + (x⁻¹) ^ 7 = (x + 1 + x⁻¹) ^ 3 := by
  have h := p1_four_impulse_identity_cleared x
  rw [hroot, mul_zero] at h
  field_simp
  linear_combination h

theorem p1GreenRoots_ne_zero {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b) (j : Fin 4) :
    quarticSalemRoots b p1NeutralRoot j ≠ 0 := by
  have hbn : b ≠ 0 := ne_of_gt (by linarith [hb])
  have hzn : p1NeutralRoot ≠ 0 := by
    intro h
    have hn := p1NeutralRoot_norm
    rw [h] at hn
    norm_num at hn
  fin_cases j
  · change ((b⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hbn
  · change (b : ℂ) ≠ 0
    exact_mod_cast hbn
  · exact hzn
  · exact star_ne_zero.mpr hzn
theorem p1GreenRoots_equation {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (j : Fin 4) :
    (quarticSalemRoots b p1NeutralRoot j) ^ 4 - (quarticSalemRoots b p1NeutralRoot j) ^ 3 -
      (quarticSalemRoots b p1NeutralRoot j) ^ 2 - (quarticSalemRoots b p1NeutralRoot j) + 1 = 0 := by
  have he : (p1GreenPolynomial.map (Int.castRingHom ℂ)).eval
      (quarticSalemRoots b p1NeutralRoot j) = 0 := by
    rw [p1Green_factorization hb hroot, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp
  rwa [p1GreenPolynomial_eval] at he
/-- The actual P1 spectral Green function, with the expanding root at index one. -/
noncomputable def p1GreenComplex (b : ℝ) (i : ℤ) : ℂ :=
  quarticSpectralGreen (p1GreenPolynomial.map (Int.castRingHom ℂ))
    (quarticSalemRoots b p1NeutralRoot) 1 i
/-- The real P1 Green coordinate used in the finite four-impulse construction. -/
noncomputable def p1GreenCoordinate (b : ℝ) (i : ℤ) : ℝ := (p1GreenComplex b i).re
theorem p1GreenComplex_forcing {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    reciprocalQuarticOperator (1 : ℂ) (-1) (p1GreenComplex b) t = if t = 0 then 1 else 0 := by
  have him : p1NeutralRoot.im ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num) p1NeutralRoot_im_bounds.1)
  apply quarticSpectralGreen_forcing (p1GreenPolynomial.map (Int.castRingHom ℂ))
    (quarticSalemRoots b p1NeutralRoot) 1
    (quarticSalemRoots_injective (by linarith [hb]) p1NeutralRoot him)
    (p1Green_factorization hb hroot) (p1GreenRoots_ne_zero hb)
  intro j
  simpa [sub_eq_add_neg] using p1GreenRoots_equation hb hroot j
theorem p1GreenCoordinate_forcing {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenCoordinate b) t = if t = 0 then 1 else 0 := by
  have h := congrArg Complex.re (p1GreenComplex_forcing hb hroot t)
  by_cases ht : t = 0
  · simpa [reciprocalQuarticOperator, p1GreenCoordinate, ht] using h
  · simpa [reciprocalQuarticOperator, p1GreenCoordinate, ht] using h
theorem p1GreenPolynomial_derivative_eval (z : ℂ) :
    (p1GreenPolynomial.map (Int.castRingHom ℂ)).derivative.eval z =
      4 * z ^ 3 - 3 * z ^ 2 - 2 * z - 1 := by
  simp [p1GreenPolynomial]
  ring
/-- The expanding real left branch, with exactly the source normalization. -/
theorem p1GreenCoordinate_left (b : ℝ) {i : ℤ} (hi : i ≤ 0) :
    p1GreenCoordinate b i = -(4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1)⁻¹ * b ^ (i - 1) := by
  change (quarticSpectralGreen (p1GreenPolynomial.map (Int.castRingHom ℂ))
    (quarticSalemRoots b p1NeutralRoot) 1 i).re = _
  rw [quarticSpectralGreen_left _ _ _ hi]
  norm_num only [quarticSalemRoots, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [p1GreenPolynomial_derivative_eval]
  have hd : 4 * (b : ℂ) ^ 3 - 3 * (b : ℂ) ^ 2 - 2 * (b : ℂ) - 1 =
      ((4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hd]
  norm_cast

def p1GreenImpulseShift : Fin 4 → ℤ := ![-7, -4, 4, 7]
def p1GreenImpulseCoefficient : Fin 4 → ℤ := ![1, -1, -1, 1]
/-- The true four-impulse P1 Green trajectory.  This sequence retains its
outgoing neutral wave; it is distinct from the square-summable localization. -/
noncomputable def p1GreenSeed (b : ℝ) (t : ℤ) : ℝ :=
  finiteGreenConvolution Finset.univ p1GreenImpulseShift
    (fun j => (p1GreenImpulseCoefficient j : ℝ)) (p1GreenCoordinate b) t
theorem p1GreenSeed_four_terms (b : ℝ) (t : ℤ) :
    p1GreenSeed b t = p1GreenCoordinate b (t + 7) - p1GreenCoordinate b (t + 4) -
      p1GreenCoordinate b (t - 4) + p1GreenCoordinate b (t - 7) := by
  norm_num [p1GreenSeed, finiteGreenConvolution, p1GreenImpulseShift,
    p1GreenImpulseCoefficient, Fin.sum_univ_succ, sub_neg_eq_add]
  ring
theorem p1GreenSeed_forcing {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenSeed b) t =
      ∑ j : Fin 4, if t = p1GreenImpulseShift j then (p1GreenImpulseCoefficient j : ℝ) else 0 := by
  exact finiteGreenConvolution_forcing 1 (-1) Finset.univ p1GreenImpulseShift
    (fun j => (p1GreenImpulseCoefficient j : ℝ)) (p1GreenCoordinate b)
    (p1GreenCoordinate_forcing hb hroot) t
theorem p1GreenSeed_integer_forcing {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    ∃ m : ℤ, reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenSeed b) t = (m : ℝ) := by
  refine ⟨∑ j : Fin 4, if t = p1GreenImpulseShift j then p1GreenImpulseCoefficient j else 0, ?_⟩
  rw [p1GreenSeed_forcing hb hroot]
  push_cast
  rfl
theorem p1GreenSeed_forcing_core {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (j : Fin 23) :
    reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenSeed b) ((j : ℕ) - (11 : ℤ)) =
      (p1SeedCoreForcing j : ℝ) := by
  rw [p1GreenSeed_forcing hb hroot]
  fin_cases j <;> norm_num [p1GreenImpulseShift, p1GreenImpulseCoefficient,
    p1SeedCoreForcing, Fin.sum_univ_succ]
theorem p1_four_impulse_zpow_identity {K : Type*} [Field K] {x : K} (hx : x ≠ 0)
    (hroot : x ^ 4 - x ^ 3 - x ^ 2 - x + 1 = 0) :
    x ^ (7 : ℤ) - x ^ (4 : ℤ) - x ^ (-4 : ℤ) + x ^ (-7 : ℤ) = (x + 1 + x⁻¹) ^ 3 := by
  norm_num only [zpow_ofNat, zpow_neg]
  simpa [inv_pow] using p1_four_impulse_identity_at_root hx hroot
/-- The four-impulse Green trajectory has exactly the original `U₁³`
expanding anchor on the full incoming half-line. -/
theorem p1GreenSeed_left {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : t ≤ -7) :
    p1GreenSeed b t = p1SeedExpandingOrbit b t := by
  have hbn : b ≠ 0 := ne_of_gt (by linarith [hb])
  have hF := p1_four_impulse_zpow_identity hbn hroot
  have hp (k : ℤ) : b ^ (t + k - 1) = b ^ (t - 1) * b ^ k := by
    rw [show t + k - 1 = (t - 1) + k by omega, zpow_add₀ hbn]
  have hm4 : b ^ (t - 4 - 1) = b ^ (t - 1) * b ^ (-4 : ℤ) := by
    simpa only [sub_eq_add_neg] using hp (-4)
  have hm7 : b ^ (t - 7 - 1) = b ^ (t - 1) * b ^ (-7 : ℤ) := by
    simpa only [sub_eq_add_neg] using hp (-7)
  rw [p1GreenSeed_four_terms,
    p1GreenCoordinate_left b (show t + 7 ≤ 0 by omega),
    p1GreenCoordinate_left b (show t + 4 ≤ 0 by omega),
    p1GreenCoordinate_left b (show t - 4 ≤ 0 by omega),
    p1GreenCoordinate_left b (show t - 7 ≤ 0 by omega)]
  dsimp [p1SeedExpandingOrbit]
  rw [hp 7, hp 4, hm4, hm7]
  linear_combination -(4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1)⁻¹ * b ^ (t - 1) * hF

theorem p1SeedLocalizedSequence_core (b : ℝ) (j : Fin 27) :
    p1SeedLocalizedSequence b ((j : ℕ) - (11 : ℤ)) = p1SeedCoreCoordinate b j := by
  change p1SeedLocalizedSequence b (p1SeedIndex (.inl j)) = _
  simp only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl]
theorem p1SeedLocalizedSequence_forcing_core {b : ℝ}
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (j : Fin 23) :
    reciprocalQuarticOperator (1 : ℝ) (-1) (p1SeedLocalizedSequence b) ((j : ℕ) - (11 : ℤ)) =
      (p1SeedCoreForcing j : ℝ) := by
  have hc := p1SeedCoreCoordinate_forcing hroot j
  have h4 : (j : ℕ) - (11 : ℤ) + 4 = ((j : ℕ) + 4 : ℕ) - (11 : ℤ) := by omega
  have h3 : (j : ℕ) - (11 : ℤ) + 3 = ((j : ℕ) + 3 : ℕ) - (11 : ℤ) := by omega
  have h2 : (j : ℕ) - (11 : ℤ) + 2 = ((j : ℕ) + 2 : ℕ) - (11 : ℤ) := by omega
  have h1 : (j : ℕ) - (11 : ℤ) + 1 = ((j : ℕ) + 1 : ℕ) - (11 : ℤ) := by omega
  dsimp only [reciprocalQuarticOperator]
  rw [h4, h3, h2, h1,
    p1SeedLocalizedSequence_core b ⟨(j : ℕ) + 4, by omega⟩,
    p1SeedLocalizedSequence_core b ⟨(j : ℕ) + 3, by omega⟩,
    p1SeedLocalizedSequence_core b ⟨(j : ℕ) + 2, by omega⟩,
    p1SeedLocalizedSequence_core b ⟨(j : ℕ) + 1, by omega⟩,
    p1SeedLocalizedSequence_core b ⟨(j : ℕ), by omega⟩]
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using hc
/-- The actual Green trajectory equals all 27 independently certified
centered orbit coordinates, by the exact incoming anchor and finite recurrence. -/
theorem p1GreenSeed_core {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (j : Fin 27) :
    p1GreenSeed b ((j : ℕ) - (11 : ℤ)) = p1SeedCoreCoordinate b j := by
  let f : ℕ → ℝ := fun n => p1GreenSeed b ((n : ℤ) - 11)
  let g : ℕ → ℝ := fun n => p1SeedLocalizedSequence b ((n : ℤ) - 11)
  have he : ∀ n < 27, f n = g n := by
    apply finite_reciprocalQuartic_agreement (A := (1 : ℝ)) (B := (-1 : ℝ))
    · intro n hn
      dsimp [f, g]
      exact (p1GreenSeed_left hb hroot (by omega)).trans
        (p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (by omega)).symm
    · intro n hn
      let k : Fin 23 := ⟨n, by omega⟩
      have hs := (p1GreenSeed_forcing_core hb hroot k).trans
        (p1SeedLocalizedSequence_forcing_core hroot k).symm
      change reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenSeed b) ((n : ℤ) - 11) =
        reciprocalQuarticOperator (1 : ℝ) (-1) (p1SeedLocalizedSequence b) ((n : ℤ) - 11) at hs
      have h4 : ((n + 4 : ℕ) : ℤ) - 11 = (n : ℤ) - 11 + 4 := by omega
      have h3 : ((n + 3 : ℕ) : ℤ) - 11 = (n : ℤ) - 11 + 3 := by omega
      have h2 : ((n + 2 : ℕ) : ℤ) - 11 = (n : ℤ) - 11 + 2 := by omega
      have h1 : ((n + 1 : ℕ) : ℤ) - 11 = (n : ℤ) - 11 + 1 := by omega
      dsimp only [f, g]
      rw [h4, h3, h2, h1]
      exact hs
  have h := he (j : ℕ) j.isLt
  dsimp only [f, g] at h
  rwa [p1SeedLocalizedSequence_core b j] at h
/-- The true seed trajectory and the localization agree through the
whole core and incoming half-line.  The outgoing neutral wave is retained in Y. -/
theorem p1GreenSeed_eq_localized_left {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : t ≤ 15) :
    p1GreenSeed b t = p1SeedLocalizedSequence b t := by
  by_cases hlo : t < -11
  · exact (p1GreenSeed_left hb hroot (by omega)).trans
      (p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (by omega)).symm
  · let j : Fin 27 := ⟨(t + 11).toNat, by omega⟩
    have he : (j : ℕ) - (11 : ℤ) = t := by dsimp [j]; omega
    rw [← he, p1GreenSeed_core hb hroot j, p1SeedLocalizedSequence_core b j]

theorem p1GreenImpulse_eval_at_root {K : Type*} [Field K] {x : K} (hx : x ≠ 0)
    (hroot : x ^ 4 - x ^ 3 - x ^ 2 - x + 1 = 0) :
    (∑ j : Fin 4, (p1GreenImpulseCoefficient j : K) * x ^ (-p1GreenImpulseShift j)) =
      (x + 1 + x⁻¹) ^ 3 := by
  have h := p1_four_impulse_zpow_identity hx hroot
  norm_num [p1GreenImpulseCoefficient, p1GreenImpulseShift, Fin.sum_univ_succ]
  norm_num only [zpow_ofNat, zpow_neg] at h
  linear_combination h
noncomputable def p1GreenSeedComplex (b : ℝ) (t : ℤ) : ℂ :=
  finiteGreenConvolution Finset.univ p1GreenImpulseShift
    (fun j => (p1GreenImpulseCoefficient j : ℂ)) (p1GreenComplex b) t
theorem p1GreenSeedComplex_re (b : ℝ) (t : ℤ) :
    (p1GreenSeedComplex b t).re = p1GreenSeed b t := by
  simp [p1GreenSeedComplex, p1GreenSeed, finiteGreenConvolution, Complex.re_sum,
    Complex.mul_re, p1GreenCoordinate]
/-- The actual outgoing spectral modes of the four-impulse seed use the
original `U₁³` coefficient at every root; all forcing lies to their left. -/
theorem p1GreenSeedComplex_right {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : 7 < t) :
    p1GreenSeedComplex b t =
      ∑ a ∈ (Finset.univ : Finset (Fin 4)).erase 1,
        ((p1GreenPolynomial.map (Int.castRingHom ℂ)).derivative.eval
          (quarticSalemRoots b p1NeutralRoot a))⁻¹ *
          (quarticSalemRoots b p1NeutralRoot a) ^ (t - 1) *
          (quarticSalemRoots b p1NeutralRoot a + 1 +
            (quarticSalemRoots b p1NeutralRoot a)⁻¹) ^ 3 := by
  have hs (j : Fin 4) (_ : j ∈ (Finset.univ : Finset (Fin 4))) : p1GreenImpulseShift j < t := by
    fin_cases j <;> norm_num [p1GreenImpulseShift] <;> omega
  have he (a : Fin 4) := p1GreenImpulse_eval_at_root
    (p1GreenRoots_ne_zero hb a) (p1GreenRoots_equation hb hroot a)
  have h := finiteGreenConvolution_right (p1GreenPolynomial.map (Int.castRingHom ℂ))
    (quarticSalemRoots b p1NeutralRoot) 1 (p1GreenRoots_ne_zero hb) Finset.univ
    p1GreenImpulseShift (fun j => (p1GreenImpulseCoefficient j : ℂ)) t hs
  simp_rw [he] at h
  exact h

noncomputable def p1PowerSeedMode (z : ℂ) (t : ℤ) : ℂ :=
  (4 * z ^ 3 - 3 * z ^ 2 - 2 * z - 1)⁻¹ * z ^ (t - 1) * (z + 1 + z⁻¹) ^ 3
theorem p1PowerSeedMode_conjugate (z : ℂ) (t : ℤ) :
    p1PowerSeedMode (star z) t = star (p1PowerSeedMode z t) := by
  simp [p1PowerSeedMode]
theorem p1PowerSeedMode_neutral (t : ℤ) :
    p1PowerSeedMode p1NeutralRoot t = p1SeedNeutralCoefficient * p1NeutralRoot ^ (t - 1) := by
  dsimp [p1PowerSeedMode, p1SeedNeutralCoefficient]
  ring
theorem p1PowerSeedMode_ofReal (x : ℝ) (t : ℤ) :
    p1PowerSeedMode (x : ℂ) t =
      (((4 * x ^ 3 - 3 * x ^ 2 - 2 * x - 1)⁻¹ * x ^ (t - 1) *
        (x + 1 + x⁻¹) ^ 3 : ℝ) : ℂ) := by
  dsimp [p1PowerSeedMode]
  push_cast
  rfl
theorem p1PowerSeedMode_stable {b : ℝ} (hb : b ≠ 0)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    p1PowerSeedMode ((b⁻¹ : ℝ) : ℂ) t = ((p1SeedExpandingOrbit b (4 - t) : ℝ) : ℂ) := by
  rw [p1PowerSeedMode_ofReal]
  have hq : b ^ 4 - (1 : ℝ) * b ^ 3 + (-1 : ℝ) * b ^ 2 - 1 * b + 1 = 0 := by
    simpa [sub_eq_add_neg] using hroot
  have hs := reciprocalQuarticStableMode_reflection hb hq ((b + 1 + b⁻¹) ^ 3) t
  have hu : b⁻¹ + 1 + (b⁻¹)⁻¹ = b + 1 + b⁻¹ := by simp; ring
  rw [hu]
  apply congrArg (fun x : ℝ => (x : ℂ))
  simpa [reciprocalQuarticDerivativeValue, p1SeedExpandingOrbit, sub_eq_add_neg, mul_neg] using hs
theorem p1GreenSeedComplex_three_modes {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : 7 < t) :
    p1GreenSeedComplex b t = p1PowerSeedMode ((b⁻¹ : ℝ) : ℂ) t +
      p1PowerSeedMode p1NeutralRoot t + p1PowerSeedMode (star p1NeutralRoot) t := by
  have h := p1GreenSeedComplex_right hb hroot ht
  simp_rw [p1GreenPolynomial_derivative_eval] at h
  change p1GreenSeedComplex b t = ∑ a ∈ (Finset.univ : Finset (Fin 4)).erase 1,
    p1PowerSeedMode (quarticSalemRoots b p1NeutralRoot a) t at h
  rw [h]
  have he : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  rw [he]
  norm_num [quarticSalemRoots, add_assoc]
/-- The actual outgoing trajectory is the reflected stable mode plus
the certified neutral wave, with the exact source phase. -/
theorem p1GreenSeed_right {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : 7 < t) :
    p1GreenSeed b t = p1SeedExpandingOrbit b (4 - t) + p1SeedNeutralWave t := by
  have hn : b ≠ 0 := ne_of_gt (by linarith [hb])
  have h := congrArg Complex.re (p1GreenSeedComplex_three_modes hb hroot ht)
  rw [p1PowerSeedMode_conjugate] at h
  simp only [p1GreenSeedComplex_re, Complex.add_re, p1PowerSeedMode_stable hn hroot,
    Complex.ofReal_re, Complex.star_def, Complex.conj_re,
    p1PowerSeedMode_neutral] at h
  simpa only [p1SeedNeutralWave, neutralModeWave, two_mul, add_assoc] using h
theorem p1SeedLocalizedSequence_eq_reflected_orbit (b : ℝ) {t : ℤ} (ht : 16 ≤ t) :
    p1SeedLocalizedSequence b t = p1SeedExpandingOrbit b (4 - t) := by
  let n : ℕ := (t - 16).toNat
  have he : t = 16 + (n : ℤ) := by dsimp [n]; omega
  rw [he]
  change p1SeedLocalizedSequence b (p1SeedIndex (.inr (.inr n))) = _
  simp only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inr]
  rw [p1SeedStableTail_eq_orbit]
  congr 1
  omega
/-- This is the actual restoration relation between the true trajectory
and its localized finite-action profile, including its outgoing switch index. -/
theorem p1GreenSeed_restoration {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    p1GreenSeed b t = p1SeedLocalizedSequence b t +
      if 16 ≤ t then p1SeedNeutralWave t else 0 := by
  by_cases ht : 16 ≤ t
  · rw [ite_eq_left ht, p1GreenSeed_right hb hroot (by omega : 7 < t),
      p1SeedLocalizedSequence_eq_reflected_orbit b ht]
  · rw [ite_eq_right ht, add_zero]
    exact p1GreenSeed_eq_localized_left hb hroot (by omega)
/-- Every true P1 seed coordinate is canonical; no totalized logarithm at
a zero cosine is used in its Fourier interpretation. -/
theorem p1GreenSeed_abs_lt_half {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    |p1GreenSeed b t| < (1 / 2 : ℝ) := by
  have hH := p1_seed_localized_margin_refined hb hroot t
  have hD := p1SeedNeutralAmplitude_bounds.2
  change 2 * ‖p1SeedNeutralCoefficient‖ < (1014602 / 10 ^ 8 : ℝ) at hD
  have hW : |if 16 ≤ t then p1SeedNeutralWave t else 0| ≤ 2 * ‖p1SeedNeutralCoefficient‖ := by
    split_ifs
    · exact abs_p1SeedNeutralWave_le t
    · simp
  rw [p1GreenSeed_restoration hb hroot]
  calc
    _ ≤ |p1SeedLocalizedSequence b t| + |if 16 ≤ t then p1SeedNeutralWave t else 0| := abs_add_le _ _
    _ ≤ (1 / 2 - 1951 / 25000) + 2 * ‖p1SeedNeutralCoefficient‖ := add_le_add hH hW
    _ < (1 / 2 : ℝ) := by linarith

theorem p1GreenSeed_cos_pos {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    0 < Real.cos (Real.pi * p1GreenSeed b t) := by
  have ht := p1GreenSeed_abs_lt_half hb hroot t
  apply Real.cos_pos_of_mem_Ioo
  apply abs_lt.mp
  rw [abs_mul, abs_of_pos Real.pi_pos]
  nlinarith [mul_lt_mul_of_pos_left ht Real.pi_pos]

theorem p1SeedNeutralWave_recurrence (t : ℤ) :
    reciprocalQuarticOperator (1 : ℝ) (-1) p1SeedNeutralWave t = 0 := by
  have hroot : p1NeutralRoot ^ 4 - (1 : ℂ) * p1NeutralRoot ^ 3 +
      (-1 : ℂ) * p1NeutralRoot ^ 2 - 1 * p1NeutralRoot + 1 = 0 := by
    simpa [sub_eq_add_neg] using p1NeutralRoot_quartic
  have h := reciprocalQuarticOperator_mode p1NeutralRoot_ne_zero hroot p1SeedNeutralCoefficient t
  change reciprocalQuarticOperator (1 : ℝ) (-1)
    (fun i => 2 * (p1SeedNeutralCoefficient * p1NeutralRoot ^ (i - 1)).re) t = 0
  rw [reciprocalQuarticOperator_const_mul, reciprocalQuarticOperator_re]
  norm_num only [Complex.ofReal_one, Complex.ofReal_neg]
  rw [h]
  simp
theorem p1GreenSeed_forcing_symmetric {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenSeed b) (-t) =
      reciprocalQuarticOperator (1 : ℝ) (-1) (p1GreenSeed b) t := by
  rw [p1GreenSeed_forcing hb hroot, p1GreenSeed_forcing hb hroot]
  norm_num [p1GreenImpulseShift, p1GreenImpulseCoefficient, Fin.sum_univ_succ,
    neg_eq_iff_eq_neg]
  ring
/-- Exact raw reciprocity of the actual Green trajectory, derived from
its symmetric finite forcing and incoming spectral modes.  The neutral wave
is retained explicitly; this is not a symmetry assertion about localized H. -/
theorem p1GreenSeed_reflection {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    p1GreenSeed b (4 - t) = p1GreenSeed b t - p1SeedNeutralWave t := by
  refine reciprocalQuartic_eq_of_left (A := (1 : ℝ)) (B := (-1 : ℝ))
    (f := fun i => p1GreenSeed b (4 - i))
    (g := fun i => p1GreenSeed b i - p1SeedNeutralWave i) (a := (-7 : ℤ)) ?_ ?_ t
  · intro i hi
    rw [p1GreenSeed_right hb hroot (by omega : 7 < 4 - i),
      show 4 - (4 - i) = i by omega, p1SeedNeutralWave_reflection,
      p1GreenSeed_left hb hroot hi]
    ring
  · intro i
    rw [reciprocalQuarticOperator_sub, reciprocalQuarticOperator_reflection,
      show 4 - i - 4 = -i by omega, p1SeedNeutralWave_recurrence,
      p1GreenSeed_forcing_symmetric hb hroot, sub_zero]

/-- The exact core duality needed by the mirror construction.  Its
interval hypotheses are essential: outgoing localization removes the wave. -/
theorem p1SeedLocalizedSequence_core_reflection {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ha : -11 ≤ t) (ht : t ≤ 15) :
    p1SeedLocalizedSequence b (4 - t) = p1SeedLocalizedSequence b t - p1SeedNeutralWave t := by
  have h := p1GreenSeed_reflection hb hroot t
  rw [p1GreenSeed_eq_localized_left hb hroot (by omega : 4 - t ≤ 15),
    p1GreenSeed_eq_localized_left hb hroot ht] at h
  exact h

end Salem
