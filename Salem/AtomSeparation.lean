module

public import Mathlib

@[expose] public section

open scoped BigOperators
open Polynomial

namespace Salem

/-- A polynomial nonzero at one conjugate of an irreducible monic integer polynomial
has a nonzero integer resultant. The rational coprimality step uses Gauss's lemma. -/
theorem integer_resultant_ne_zero_of_irreducible_root
    (P A : ℤ[X]) (hPmonic : P.Monic) (hPirr : Irreducible P)
    (r : ℂ) (hPr : P.eval₂ (Int.castRingHom ℂ) r = 0)
    (hAr : A.eval₂ (Int.castRingHom ℂ) r ≠ 0) :
    P.resultant A ≠ 0 := by
  have hnotZ : ¬ P ∣ A := by
    intro hd
    exact hAr (eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (Int.castRingHom ℂ) r hd hPr)
  have hnotQ : ¬ P.map (Int.castRingHom ℚ) ∣ A.map (Int.castRingHom ℚ) := by
    intro hd
    exact hnotZ ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast P A hPmonic.isPrimitive).2 hd)
  have hPQ : Irreducible (P.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hPmonic.isPrimitive).1 hPirr
  have hcop := (hPQ.isCoprime_or_dvd (A.map (Int.castRingHom ℚ))).resolve_right hnotQ
  have hres := resultant_ne_zero _ _ hcop
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  intro hz
  apply hres
  simp only [natDegree_map_eq_of_injective hinj, resultant_map_map, hz, map_zero]

/-- The integer resultant is exactly the product over the supplied complete root factorization. -/
theorem integer_resultant_eq_prod_eval
    (P A : ℤ[X]) {d : ℕ} (r : Fin d → ℂ)
    (hfactor : P.map (Int.castRingHom ℂ) = ∏ i, (X - C (r i))) :
    (Int.castRingHom ℂ) (P.resultant A) = ∏ i, A.eval₂ (Int.castRingHom ℂ) (r i) := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  calc
    _ = (P.map (Int.castRingHom ℂ)).resultant (A.map (Int.castRingHom ℂ)) := by
      simpa only [natDegree_map_eq_of_injective hinj] using
        (resultant_map_map P A P.natDegree A.natDegree (Int.castRingHom ℂ)).symm
    _ = _ := by
      rw [hfactor, resultant_prod_left Finset.univ _ _ _ (by simp) le_rfl]
      simp only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ le_rfl, eval_map]

/-- The product of all conjugate values has absolute value at least one.
This is the integer algebraic-norm step, proved through the actual integer resultant. -/
theorem one_le_prod_norm_eval_of_irreducible
    (P A : ℤ[X]) (hPmonic : P.Monic) (hPirr : Irreducible P)
    {d : ℕ} (r : Fin d → ℂ)
    (hfactor : P.map (Int.castRingHom ℂ) = ∏ i, (X - C (r i)))
    (i : Fin d) (hPr : P.eval₂ (Int.castRingHom ℂ) (r i) = 0)
    (hAr : A.eval₂ (Int.castRingHom ℂ) (r i) ≠ 0) :
    1 ≤ ∏ j, ‖A.eval₂ (Int.castRingHom ℂ) (r j)‖ := by
  have hz := integer_resultant_ne_zero_of_irreducible_root P A hPmonic hPirr (r i) hPr hAr
  have hi : (1 : ℤ) ≤ |P.resultant A| := by
    have : (0 : ℤ) < |P.resultant A| := abs_pos.2 hz
    omega
  have heq := congrArg (fun z : ℂ => ‖z‖) (integer_resultant_eq_prod_eval P A r hfactor)
  rw [norm_prod] at heq
  rw [← heq]
  change (1 : ℝ) ≤ ‖((P.resultant A : ℤ) : ℂ)‖
  rw [Complex.norm_intCast]
  exact_mod_cast hi

/-- The integer polynomial of a finite half-difference word. -/
noncomputable def digitDifferencePolynomial {N : ℕ} (d : Fin N → ℤ) : ℤ[X] :=
  ∑ j : Fin N, monomial (j : ℕ) (d j)

theorem norm_eval₂_digitDifferencePolynomial_le {N : ℕ} (d : Fin N → ℤ)
    (hd : ∀ j, |d j| ≤ 1) (z : ℂ) :
    ‖(digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) z‖ ≤
      ∑ j : Fin N, ‖z‖ ^ (j : ℕ) := by
  rw [digitDifferencePolynomial, eval₂_finsetSum]
  simp only [eval₂_monomial]
  calc
    _ ≤ ∑ j : Fin N, ‖(Int.castRingHom ℂ) (d j) * z ^ (j : ℕ)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      have hcoeff : ‖(Int.castRingHom ℂ) (d j)‖ ≤ 1 := by
        change ‖((d j : ℤ) : ℂ)‖ ≤ 1
        rw [Complex.norm_intCast]
        exact_mod_cast hd j
      rw [norm_mul, norm_pow]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (norm_nonneg z) (j : ℕ))

/-- At a unit-circle conjugate each half-difference value has norm at most the word length. -/
theorem norm_eval₂_digitDifferencePolynomial_le_length {N : ℕ} (d : Fin N → ℤ)
    (hd : ∀ j, |d j| ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) z‖ ≤ N := by
  simpa only [hz, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using norm_eval₂_digitDifferencePolynomial_le d hd z

/-- At the expanding real conjugate the half-difference is bounded by the exact geometric sum. -/
theorem norm_eval₂_digitDifferencePolynomial_real_lt {N : ℕ} (d : Fin N → ℤ)
    (hd : ∀ j, |d j| ≤ 1) {β : ℝ} (hβ : 1 < β) :
    ‖(digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) (β : ℂ)‖ <
      β ^ N / (β - 1) := by
  have hnorm : ‖(β : ℂ)‖ = β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  apply (norm_eval₂_digitDifferencePolynomial_le d hd (β : ℂ)).trans_lt
  rw [hnorm]
  apply (lt_div_iff₀ (by linarith : 0 < β - 1)).2
  rw [Fin.sum_univ_eq_sum_range (fun j => β ^ j) N]
  have heq := geom_sum_mul β N
  linarith

/-- A monic polynomial with a full list of distinct roots has the asserted linear factorization. -/
theorem integer_polynomial_factorization_of_roots (P : ℤ[X]) (hP : P.Monic)
    {d : ℕ} (hdegree : P.natDegree = d) (r : Fin d → ℂ)
    (hinj : Function.Injective r)
    (hroot : ∀ i, (P.map (Int.castRingHom ℂ)).IsRoot (r i)) :
    P.map (Int.castRingHom ℂ) = ∏ i, (X - C (r i)) := by
  apply eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C r Finset.univ)
    (hP.map (Int.castRingHom ℂ))
  · exact Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
      (fun i => dvd_iff_isRoot.2 (hroot i))
  · rw [natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℂ) from
      Int.cast_injective), hdegree,
      natDegree_prod_of_monic Finset.univ (fun i : Fin d => X - C (r i))
        (fun i _ => monic_X_sub_C (r i))]
    simp

/-- Exact interval occupancy for a finite set with a positive separation distance. -/
theorem card_le_one_add_length_div_separation (s : Finset ℝ)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hmem : ∀ x ∈ s, a ≤ x ∧ x ≤ b)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) :
    (s.card : ℝ) ≤ 1 + (b - a) / δ := by
  classical
  by_cases hs : s.card = 0
  · rw [hs]
    have : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.2 hab) hδ.le
    norm_num
    linarith
  have hn : 0 < s.card := Nat.pos_of_ne_zero hs
  let f := s.orderEmbOfFin rfl
  have hstep (i : ℕ) (hi : i + 1 < s.card) :
      δ ≤ f ⟨i + 1, hi⟩ - f ⟨i, by omega⟩ := by
    have hlt : f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩ := f.strictMono (by simp)
    have h := hsep _ (s.orderEmbOfFin_mem rfl _) _ (s.orderEmbOfFin_mem rfl _) hlt.ne
    rw [abs_of_nonpos (sub_nonpos.2 hlt.le)] at h
    linarith
  have hlower : ∀ (i : ℕ) (hi : i < s.card), a + δ * (i : ℝ) ≤ f ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simpa using (hmem _ (s.orderEmbOfFin_mem rfl ⟨0, hi⟩)).1
    | succ i ih =>
      intro hi
      have hi' : i < s.card := by omega
      have hp := ih hi'
      have hg := hstep i hi
      push_cast
      linarith
  have hi : s.card - 1 < s.card := by omega
  have hl := hlower (s.card - 1) hi
  have hu := (hmem _ (s.orderEmbOfFin_mem rfl ⟨s.card - 1, hi⟩)).2
  rw [Nat.cast_sub (by omega : 1 ≤ s.card), Nat.cast_one] at hl
  have hcard : (s.card : ℝ) - 1 ≤ (b - a) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  linarith

/-- The four conjugates in the quartic Salem root pattern, with the contracting root first. -/
noncomputable def quarticSalemRoots (β : ℝ) (ζ : ℂ) : Fin 4 → ℂ :=
  ![((β⁻¹ : ℝ) : ℂ), (β : ℂ), ζ, star ζ]

/-- The exact half-difference separation obtained from the four conjugate bounds. -/
theorem quartic_halfDifference_norm_lower_bound
    (P : ℤ[X]) (hPmonic : P.Monic) (hPirr : Irreducible P)
    {β : ℝ} (hβ : 1 < β) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hfactor : P.map (Int.castRingHom ℂ) =
      ∏ i : Fin 4, (X - C (quarticSalemRoots β ζ i)))
    {N : ℕ} (hN : 0 < N) (d : Fin N → ℤ) (hd : ∀ j, |d j| ≤ 1)
    (hu : (digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ) ≠ 0) :
    (β - 1) / (β ^ N * (N : ℝ) ^ 2) ≤
      ‖(digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ)‖ := by
  let A := digitDifferencePolynomial d
  have hPr : P.eval₂ (Int.castRingHom ℂ) (quarticSalemRoots β ζ 0) = 0 := by
    rw [← eval_map, hfactor, Fin.prod_univ_four]
    simp
  have hproduct := one_le_prod_norm_eval_of_irreducible P A hPmonic hPirr
    (quarticSalemRoots β ζ) hfactor 0 hPr hu
  simp only [Fin.prod_univ_four] at hproduct
  change 1 ≤ ‖A.eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ)‖ *
    ‖A.eval₂ (Int.castRingHom ℂ) (β : ℂ)‖ *
    ‖A.eval₂ (Int.castRingHom ℂ) ζ‖ * ‖A.eval₂ (Int.castRingHom ℂ) (star ζ)‖ at hproduct
  have hExpand := (norm_eval₂_digitDifferencePolynomial_real_lt d hd hβ).le
  have hunit := norm_eval₂_digitDifferencePolynomial_le_length d hd ζ hζ
  have hunit' := norm_eval₂_digitDifferencePolynomial_le_length d hd (star ζ)
    (by simpa only [norm_star] using hζ)
  have hmul : 1 ≤ ‖A.eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ)‖ *
      (β ^ N / (β - 1)) * (N : ℝ) * (N : ℝ) := by
    apply hproduct.trans
    gcongr
  have heq : ‖A.eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ)‖ *
      (β ^ N / (β - 1)) * (N : ℝ) * (N : ℝ) =
      (‖A.eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ)‖ * β ^ N * (N : ℝ) ^ 2) /
        (β - 1) := by ring
  rw [heq] at hmul
  have hmul' := (le_div_iff₀ (by linarith : 0 < β - 1)).1 hmul
  apply (div_le_iff₀ (mul_pos (pow_pos (by linarith : 0 < β) N)
    (sq_pos_of_pos (Nat.cast_pos.2 hN)))).2
  nlinarith

theorem quarticSalemRoots_injective {β : ℝ} (hβ : 1 < β) (ζ : ℂ) (hζim : ζ.im ≠ 0) :
    Function.Injective (quarticSalemRoots β ζ) := by
  have hrealne (x : ℝ) : (x : ℂ) ≠ ζ := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.ofReal_im] at him
    exact hζim him.symm
  have hrealne' (x : ℝ) : (x : ℂ) ≠ star ζ := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    apply hζim
    linarith
  have hstarne : ζ ≠ star ζ := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    apply hζim
    linarith
  have hβne : ((β⁻¹ : ℝ) : ℂ) ≠ (β : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re] at hre
    have hβinv := inv_lt_one_of_one_lt₀ hβ
    linarith
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [quarticSalemRoots] at hij ⊢
  all_goals first | exact (hβne hij).elim | exact (hβne hij.symm).elim |
    exact (hrealne _ hij).elim | exact (hrealne _ hij.symm).elim |
    exact (hrealne' _ hij).elim | exact (hrealne' _ hij.symm).elim |
    exact (hstarne hij).elim | exact (hstarne hij.symm).elim

/-- The four-root hypotheses alone supply the complete factorization used in the norm estimate. -/
theorem quartic_factorization_of_root_pattern
    (P : ℤ[X]) (hPmonic : P.Monic) (hdegree : P.natDegree = 4)
    {β : ℝ} (hβ : 1 < β) (ζ : ℂ) (hζim : ζ.im ≠ 0)
    (hβroot : (P.map (Int.castRingHom ℂ)).IsRoot (β : ℂ))
    (hβinvroot : (P.map (Int.castRingHom ℂ)).IsRoot ((β⁻¹ : ℝ) : ℂ))
    (hζroot : (P.map (Int.castRingHom ℂ)).IsRoot ζ)
    (hstarroot : (P.map (Int.castRingHom ℂ)).IsRoot (star ζ)) :
    P.map (Int.castRingHom ℂ) = ∏ i : Fin 4, (X - C (quarticSalemRoots β ζ i)) := by
  apply integer_polynomial_factorization_of_roots P hPmonic hdegree
    (quarticSalemRoots β ζ) (quarticSalemRoots_injective hβ ζ hζim)
  intro i
  fin_cases i
  · exact hβinvroot
  · exact hβroot
  · exact hζroot
  · exact hstarroot

theorem eval₂_digitDifferencePolynomial_real {N : ℕ} (d : Fin N → ℤ) (x : ℝ) :
    (digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) (x : ℂ) =
      ((∑ j : Fin N, (d j : ℝ) * x ^ (j : ℕ) : ℝ) : ℂ) := by
  rw [digitDifferencePolynomial, eval₂_finsetSum]
  simp only [eval₂_monomial]
  push_cast
  rfl

/-- Source-exact separation for every nonzero half-difference, from the full quartic root data. -/
theorem quartic_halfDifference_lower_bound
    (P : ℤ[X]) (hPmonic : P.Monic) (hdegree : P.natDegree = 4)
    (hPirr : Irreducible (P.map (Int.castRingHom ℚ)))
    {β : ℝ} (hβ : 1 < β) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζim : ζ.im ≠ 0)
    (hβroot : (P.map (Int.castRingHom ℂ)).IsRoot (β : ℂ))
    (hβinvroot : (P.map (Int.castRingHom ℂ)).IsRoot ((β⁻¹ : ℝ) : ℂ))
    (hζroot : (P.map (Int.castRingHom ℂ)).IsRoot ζ)
    (hstarroot : (P.map (Int.castRingHom ℂ)).IsRoot (star ζ))
    {N : ℕ} (hN : 0 < N) (d : Fin N → ℤ) (hd : ∀ j, |d j| ≤ 1)
    (hu : (∑ j : Fin N, (d j : ℝ) * β⁻¹ ^ (j : ℕ)) ≠ 0) :
    (β - 1) / (β ^ N * (N : ℝ) ^ 2) ≤
      |∑ j : Fin N, (d j : ℝ) * β⁻¹ ^ (j : ℕ)| := by
  have hPirrZ : Irreducible P :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hPmonic.isPrimitive).2 hPirr
  have hfactor := quartic_factorization_of_root_pattern P hPmonic hdegree hβ ζ hζim
    hβroot hβinvroot hζroot hstarroot
  have huC : (digitDifferencePolynomial d).eval₂ (Int.castRingHom ℂ) ((β⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [eval₂_digitDifferencePolynomial_real]
    exact_mod_cast hu
  have h := quartic_halfDifference_norm_lower_bound P hPmonic hPirrZ hβ ζ hζ hfactor hN d hd huC
  rw [eval₂_digitDifferencePolynomial_real, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Actual finite sign sums, with the same zero-based power convention as the paper. -/
noncomputable def finiteSignAtom (β : ℝ) {N : ℕ} (w : Fin N → Bool) : ℝ :=
  ∑ j : Fin N, (if w j then (1 : ℝ) else -1) * β⁻¹ ^ (j : ℕ)

/-- Ternary half-differences of two sign words. -/
def signWordHalfDifference {N : ℕ} (s t : Fin N → Bool) (j : Fin N) : ℤ :=
  if s j then (if t j then 0 else 1) else (if t j then -1 else 0)

theorem signWordHalfDifference_abs_le_one {N : ℕ} (s t : Fin N → Bool) (j : Fin N) :
    |signWordHalfDifference s t j| ≤ 1 := by
  cases hs : s j <;> cases ht : t j <;> norm_num [signWordHalfDifference, hs, ht]

theorem finiteSignAtom_sub_eq_twice_halfDifference (β : ℝ) {N : ℕ} (s t : Fin N → Bool) :
    finiteSignAtom β s - finiteSignAtom β t =
      2 * ∑ j : Fin N, (signWordHalfDifference s t j : ℝ) * β⁻¹ ^ (j : ℕ) := by
  rw [finiteSignAtom, finiteSignAtom, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases hs : s j <;> cases ht : t j <;> norm_num [signWordHalfDifference, hs, ht] <;> ring

/-- The finite set of distinct sign atoms; repeated word values are merged. -/
noncomputable def finiteSignAtoms (β : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (finiteSignAtom β : (Fin N → Bool) → ℝ)

noncomputable def finiteSignAtomsInInterval (β : ℝ) (N : ℕ) (a b : ℝ) : Finset ℝ := by
  classical
  exact (finiteSignAtoms β N).filter (fun x => x ∈ Set.Icc a b)

/-- The exact separation constant in v2 Lemma `lem:entropy`. -/
noncomputable def atomSeparationConstant (β R : ℝ) : ℝ :=
  1 + (1 + 2 * R) / (2 * (β - 1))

/-- A cell of the infinite series restricts its finite prefix to the paper's enlarged window. -/
theorem prefix_mem_window_of_cell_and_tail {W X η R k : ℝ}
    (hcell : W ∈ Set.Ico (k * η) ((k + 1) * η)) (htail : |W - X| ≤ R * η) :
    X ∈ Set.Icc (η * (k - R)) (η * (k + 1 + R)) := by
  have ht := abs_le.1 htail
  constructor <;> nlinarith [hcell.1, hcell.2]

section QuarticAtoms

variable (P : ℤ[X]) (hPmonic : P.Monic) (hdegree : P.natDegree = 4)
  (hPirr : Irreducible (P.map (Int.castRingHom ℚ)))
  {β : ℝ} (hβ : 1 < β) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζim : ζ.im ≠ 0)
  (hβroot : (P.map (Int.castRingHom ℂ)).IsRoot (β : ℂ))
  (hβinvroot : (P.map (Int.castRingHom ℂ)).IsRoot ((β⁻¹ : ℝ) : ℂ))
  (hζroot : (P.map (Int.castRingHom ℂ)).IsRoot ζ)
  (hstarroot : (P.map (Int.castRingHom ℂ)).IsRoot (star ζ))

include hPmonic hdegree hPirr hβ hζ hζim hβroot hβinvroot hζroot hstarroot

/-- Distinct actual sign atoms have the source-exact separation, including the factor two. -/
theorem finiteSignAtom_separation {N : ℕ} (hN : 0 < N) (s t : Fin N → Bool)
    (hne : finiteSignAtom β s ≠ finiteSignAtom β t) :
    2 * (β - 1) / (β ^ N * (N : ℝ) ^ 2) ≤ |finiteSignAtom β s - finiteSignAtom β t| := by
  have heq := finiteSignAtom_sub_eq_twice_halfDifference β s t
  have hu : (∑ j : Fin N, (signWordHalfDifference s t j : ℝ) * β⁻¹ ^ (j : ℕ)) ≠ 0 := by
    intro hz
    apply hne
    apply sub_eq_zero.1
    rw [heq, hz, mul_zero]
  have h := quartic_halfDifference_lower_bound P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot hN (signWordHalfDifference s t)
    (signWordHalfDifference_abs_le_one s t) hu
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

/-- Every interval contains at most the exact separation count of distinct merged sign atoms. -/
theorem card_finiteSignAtomsInInterval_le {N : ℕ} (hN : 0 < N)
    {a b : ℝ} (hab : a ≤ b) :
    ((finiteSignAtomsInInterval β N a b).card : ℝ) ≤
      1 + (b - a) / (2 * (β - 1) / (β ^ N * (N : ℝ) ^ 2)) := by
  classical
  apply card_le_one_add_length_div_separation _ hab
    (div_pos (mul_pos (by norm_num) (by linarith))
      (mul_pos (pow_pos (by linarith : 0 < β) N) (sq_pos_of_pos (Nat.cast_pos.2 hN))))
  · intro x hx
    exact (Finset.mem_filter.1 hx).2
  · intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 hx).1
    have hy' := (Finset.mem_filter.1 hy).1
    rcases Finset.mem_image.1 hx' with ⟨s, _, rfl⟩
    rcases Finset.mem_image.1 hy' with ⟨t, _, rfl⟩
    exact finiteSignAtom_separation P hPmonic hdegree hPirr hβ ζ hζ hζim
      hβroot hβinvroot hζroot hstarroot hN s t hxy

/-- The enlarged grid cell contains at most `C_sep * N²` distinct finite sign atoms,
with exactly the source constant and no separation or occupancy premise. -/
theorem card_finiteSignAtoms_gridWindow_le {N : ℕ} (hN : 0 < N)
    {R : ℝ} (hR : 0 ≤ R) (k : ℝ) :
    ((finiteSignAtomsInInterval β N
      (β⁻¹ ^ N * (k - R)) (β⁻¹ ^ N * (k + 1 + R))).card : ℝ) ≤
      atomSeparationConstant β R * (N : ℝ) ^ 2 := by
  have hβpos : 0 < β := by linarith
  have hβm : 0 < β - 1 := by linarith
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hη : 0 ≤ β⁻¹ ^ N := pow_nonneg (inv_nonneg.2 hβpos.le) N
  have hab : β⁻¹ ^ N * (k - R) ≤ β⁻¹ ^ N * (k + 1 + R) :=
    mul_le_mul_of_nonneg_left (by linarith) hη
  have hcard := card_finiteSignAtomsInInterval_le P hPmonic hdegree hPirr hβ ζ hζ hζim
    hβroot hβinvroot hζroot hstarroot hN hab
  have hratio :
      (β⁻¹ ^ N * (k + 1 + R) - β⁻¹ ^ N * (k - R)) /
          (2 * (β - 1) / (β ^ N * (N : ℝ) ^ 2)) =
        ((1 + 2 * R) / (2 * (β - 1))) * (N : ℝ) ^ 2 := by
    rw [inv_pow]
    field_simp [pow_ne_zero N hβpos.ne', hβm.ne', hNpos.ne']
    ring
  rw [hratio] at hcard
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  unfold atomSeparationConstant
  nlinarith

end QuarticAtoms

end Salem
