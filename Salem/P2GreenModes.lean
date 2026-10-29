module

public import Salem.P2GreenCore

@[expose] public section

namespace Salem

/-- The base convolution is a single real mode before its first impulse. -/
lemma p2GreenBaseCoordinate_left {i : ℤ} (hi : i ≤ 0) :
    p2GreenBaseCoordinate i =
      -p2CoefficientKappa p2CoefficientBeta *
        p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR *
          p2CoefficientR ^ (1 - i).toNat := by
  let N := (1 - i).toNat
  have hg (j : ℤ) (hj : 0 ≤ j) : p2GreenCoordinate (i - j) =
      -p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ (N + j.toNat) := by
    have hji : i - j ≤ 0 := by omega
    have he : (1 - (i - j)).toNat = N + j.toNat := by dsimp [N]; omega
    simp only [p2GreenCoordinate, p2GreenStableCoordinate, p2GreenNeutralCoordinate,
      ite_eq_left hji, add_zero, he]
  have h0 : p2GreenCoordinate i = -p2CoefficientKappa p2CoefficientBeta * p2CoefficientR ^ N := by
    simpa only [sub_zero, Int.toNat_zero, Nat.add_zero] using hg 0 (by norm_num)
  unfold p2GreenBaseCoordinate
  rw [h0, hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num),
    hg 4 (by norm_num), hg 7 (by norm_num), hg 8 (by norm_num),
    hg 9 (by norm_num), hg 10 (by norm_num), hg 11 (by norm_num)]
  norm_num
  simp only [N, p2CoefficientBase, Polynomial.eval₂_one, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_add, pow_zero, pow_one]
  ring

/-- After the eleven base impulses, exact anti-reciprocity of `K_b` reduces
the base convolution to one stable mode and one neutral mode. -/
lemma p2GreenBaseCoordinate_right {i : ℤ} (hi : 12 ≤ i) :
    p2GreenBaseCoordinate i =
      -p2CoefficientKappa p2CoefficientR *
        p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR *
          p2CoefficientR ^ (i - 12).toNat -
      2 * (p2CoefficientKappaComplex p2CoefficientZeta *
        p2CoefficientBase.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta *
          p2CoefficientZeta ^ (i - 12).toNat).re := by
  let N := (i - 12).toNat
  have hg (j : ℤ) (hj0 : 0 ≤ j) (hj : j ≤ 11) : p2GreenCoordinate (i - j) =
      p2CoefficientKappa p2CoefficientR * p2CoefficientR ^ (N + (11 - j).toNat) +
        2 * (p2CoefficientKappaComplex p2CoefficientZeta *
          p2CoefficientZeta ^ (N + (11 - j).toNat)).re := by
    have hji : ¬(i - j ≤ 0) := by omega
    have he : (i - j - 1).toNat = N + (11 - j).toNat := by dsimp [N]; omega
    simp only [p2GreenCoordinate, p2GreenStableCoordinate, p2GreenNeutralCoordinate,
      ite_eq_right hji, he]
  have h0 : p2GreenCoordinate i =
      p2CoefficientKappa p2CoefficientR * p2CoefficientR ^ (N + 11) +
        2 * (p2CoefficientKappaComplex p2CoefficientZeta * p2CoefficientZeta ^ (N + 11)).re := by
    simpa using hg 0 (by norm_num) (by norm_num)
  unfold p2GreenBaseCoordinate
  rw [h0, hg 1 (by norm_num) (by norm_num), hg 2 (by norm_num) (by norm_num), hg 3 (by norm_num) (by norm_num),
    hg 4 (by norm_num) (by norm_num), hg 7 (by norm_num) (by norm_num), hg 8 (by norm_num) (by norm_num),
    hg 9 (by norm_num) (by norm_num), hg 10 (by norm_num) (by norm_num), hg 11 (by norm_num) (by norm_num)]
  norm_num
  simp only [N, p2CoefficientBase, Polynomial.eval₂_one, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_add, pow_zero, pow_one,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- The first 101 core positions lie before every Green junction and reduce to one mode. -/
lemma p2GreenSeedCoordinate_left_mode {i : ℤ} (hi : i ≤ 100) :
    p2GreenSeedCoordinate i =
      -p2CoefficientKappa p2CoefficientBeta *
        p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR *
          p2CoefficientR ^ (101 - i).toNat := by
  rw [p2GreenSeedCoordinate_sparse, p2GreenBaseCoordinate_left (by omega),
    p2GreenBaseCoordinate_left (by omega)]
  have h1 : (1 - (i - 100)).toNat = (101 - i).toNat := by omega
  have h2 : (1 - (i - 2773)).toNat = (101 - i).toNat + 2673 := by omega
  simp only [h1, h2, pow_add, p2CoefficientSeed, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  ring

/-- Beyond the last Green junction the full seed is one stable and one neutral mode.
The exponent starts at 2785, dictated by spectral exponent i−1 and seed degree 2684. -/
lemma p2GreenSeedCoordinate_right_mode {i : ℤ} (hi : 2785 ≤ i) :
    p2GreenSeedCoordinate i =
      p2CoefficientKappa p2CoefficientR *
        p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR *
          p2CoefficientR ^ (i - 2785).toNat +
      2 * (p2CoefficientKappaComplex p2CoefficientZeta *
        p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta *
          p2CoefficientZeta ^ (i - 2785).toNat).re := by
  rw [p2GreenSeedCoordinate_sparse, p2GreenBaseCoordinate_right (by omega),
    p2GreenBaseCoordinate_right (by omega)]
  have h1 : (i - 100 - 12).toNat = (i - 2785).toNat + 2673 := by omega
  have h2 : (i - 2773 - 12).toNat = (i - 2785).toNat := by omega
  simp only [h1, h2, pow_add, p2CoefficientSeed, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

end Salem
