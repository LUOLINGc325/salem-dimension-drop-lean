module

public import Salem.P2FiniteData

public import Salem.P2GreenModes
public import Salem.P2Neutral

@[expose] public section

namespace Salem

lemma p2FastGrid_pos : 0 < p2FastGrid := by norm_num [p2FastGrid]

lemma p2FastRData_contains : p2FastRData.Contains p2CoefficientR := by
  apply RationalInterval.contains_of_subset p2CoreRData_contains <;>
    norm_num [p2FastRData, p2CoreRData]
lemma p2FastKappaBetaData_contains : p2FastKappaBetaData.Contains (p2CoefficientKappa p2CoefficientBeta) := by
  apply RationalInterval.contains_of_subset p2CoreKappaBetaData_contains <;>
    norm_num [p2FastKappaBetaData, p2CoreKappaBetaData]
lemma p2FastKappaRData_contains : p2FastKappaRData.Contains (p2CoefficientKappa p2CoefficientR) := by
  apply RationalInterval.contains_of_subset p2CoreKappaRData_contains <;>
    norm_num [p2FastKappaRData, p2CoreKappaRData]
lemma p2FastZetaData_contains : p2FastZetaData.Contains p2CoefficientZeta := by
  apply ComplexRationalBox.contains_of_subset p2CoreZetaData_contains <;>
    norm_num [p2FastZetaData, p2CoreZetaData]
lemma p2FastKappaZetaData_contains :
    p2FastKappaZetaData.Contains (p2CoefficientKappaComplex p2CoefficientZeta) := by
  apply ComplexRationalBox.contains_of_subset p2CoreKappaZetaData_contains <;>
    norm_num [p2FastKappaZetaData, p2CoreKappaZetaData]

lemma p2GreenStablePowerInterval_contains (n : ℕ) :
    (p2GreenStablePowerInterval n).Contains (p2CoefficientR ^ n) := by
  by_cases hn : 48 ≤ n
  · have hp : p2CoefficientR ^ n ≤ (1 / 10 ^ 12 : ℝ) := by
      calc
        p2CoefficientR ^ n ≤ (11 / 20 : ℝ) ^ n :=
          pow_le_pow_left₀ p2CoefficientR_bounds.1.le p2CoefficientR_bounds.2 n
        _ ≤ (11 / 20 : ℝ) ^ 48 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ ≤ 1 / 10 ^ 12 := by norm_num
    simpa only [p2GreenStablePowerInterval, ite_eq_left hn, RationalInterval.Contains,
      Rat.cast_zero, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      And.intro (pow_nonneg p2CoefficientR_bounds.1.le n) hp
  · simpa only [p2GreenStablePowerInterval, ite_eq_right hn] using
      RationalInterval.powRounded_contains p2FastGrid_pos p2FastRData_contains n

def p2GreenBaseRealPolynomialInterval : RationalInterval :=
  let I := p2FastRData
  let A := (I.powRounded p2FastGrid 0).sub (I.powRounded p2FastGrid 1)
  let B := A.add (I.powRounded p2FastGrid 2)
  let C := B.sub (I.powRounded p2FastGrid 3)
  let D := C.add (I.powRounded p2FastGrid 4)
  let E := D.sub (I.powRounded p2FastGrid 7)
  let F := E.add (I.powRounded p2FastGrid 8)
  let G := F.sub (I.powRounded p2FastGrid 9)
  let H := G.add (I.powRounded p2FastGrid 10)
  (H.sub (I.powRounded p2FastGrid 11)).round p2FastGrid

lemma p2GreenBaseRealPolynomialInterval_contains : p2GreenBaseRealPolynomialInterval.Contains
    (p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR) := by
  have hp (n : ℕ) := RationalInterval.powRounded_contains p2FastGrid_pos p2FastRData_contains n
  have hA := RationalInterval.sub_contains (hp 0) (hp 1)
  have hB := RationalInterval.add_contains hA (hp 2)
  have hC := RationalInterval.sub_contains hB (hp 3)
  have hD := RationalInterval.add_contains hC (hp 4)
  have hE := RationalInterval.sub_contains hD (hp 7)
  have hF := RationalInterval.add_contains hE (hp 8)
  have hG := RationalInterval.sub_contains hF (hp 9)
  have hH := RationalInterval.add_contains hG (hp 10)
  have h := RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.sub_contains hH (hp 11))
  simpa only [p2GreenBaseRealPolynomialInterval, p2CoefficientBase, Polynomial.eval₂_sub,
    Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X] using h

def p2GreenSeedRealPolynomialInterval : RationalInterval :=
  (p2GreenBaseRealPolynomialInterval.mul
    ((RationalInterval.point 1).sub (p2GreenStablePowerInterval 2673))).round p2FastGrid

lemma p2GreenSeedRealPolynomialInterval_contains : p2GreenSeedRealPolynomialInterval.Contains
    (p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR) := by
  have h := RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.mul_contains p2GreenBaseRealPolynomialInterval_contains
      (RationalInterval.sub_contains (by simpa using RationalInterval.point_contains 1)
        (p2GreenStablePowerInterval_contains 2673)))
  simpa only [p2GreenSeedRealPolynomialInterval, p2CoefficientSeed, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow, Polynomial.eval₂_X] using h

def p2BaseLeftModeComputed : RationalInterval :=
  (p2FastKappaBetaData.neg.mul p2GreenBaseRealPolynomialInterval).round p2FastGrid

def p2BaseRightModeComputed : RationalInterval :=
  (p2FastKappaRData.neg.mul p2GreenBaseRealPolynomialInterval).round p2FastGrid

def p2BaseNeutralModeComputed : ComplexRationalBox :=
  ((p2FastKappaZetaData.mul (p2GreenBasePolynomialBox p2FastZetaData)).neg).round p2FastGrid

def p2SeedLeftModeComputed : RationalInterval :=
  (p2FastKappaBetaData.neg.mul p2GreenSeedRealPolynomialInterval).round p2FastGrid

def p2SeedRightModeComputed : RationalInterval :=
  (p2FastKappaRData.mul p2GreenSeedRealPolynomialInterval).round p2FastGrid

def p2SeedNeutralModeComputed : ComplexRationalBox :=
  (p2FastKappaZetaData.mul (p2GreenSeedPolynomialBox p2FastZetaData)).round p2FastGrid

lemma p2BaseLeftModeComputed_contains : p2BaseLeftModeComputed.Contains
    (-p2CoefficientKappa p2CoefficientBeta *
      p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR) :=
  RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.mul_contains (RationalInterval.neg_contains p2FastKappaBetaData_contains)
      p2GreenBaseRealPolynomialInterval_contains)

lemma p2BaseRightModeComputed_contains : p2BaseRightModeComputed.Contains
    (-p2CoefficientKappa p2CoefficientR *
      p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR) :=
  RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.mul_contains (RationalInterval.neg_contains p2FastKappaRData_contains)
      p2GreenBaseRealPolynomialInterval_contains)

lemma p2BaseNeutralModeComputed_contains : p2BaseNeutralModeComputed.Contains
    (-(p2CoefficientKappaComplex p2CoefficientZeta *
      p2CoefficientBase.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta)) :=
  ComplexRationalBox.round_contains p2FastGrid_pos
    (ComplexRationalBox.neg_contains (ComplexRationalBox.mul_contains p2FastKappaZetaData_contains
      (p2GreenBasePolynomialBox_contains p2FastZetaData_contains)))

lemma p2SeedLeftModeComputed_contains : p2SeedLeftModeComputed.Contains
    (-p2CoefficientKappa p2CoefficientBeta *
      p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR) :=
  RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.mul_contains (RationalInterval.neg_contains p2FastKappaBetaData_contains)
      p2GreenSeedRealPolynomialInterval_contains)

lemma p2SeedRightModeComputed_contains : p2SeedRightModeComputed.Contains
    (p2CoefficientKappa p2CoefficientR *
      p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR) :=
  RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.mul_contains p2FastKappaRData_contains p2GreenSeedRealPolynomialInterval_contains)

lemma p2SeedNeutralModeComputed_contains : p2SeedNeutralModeComputed.Contains
    (p2CoefficientKappaComplex p2CoefficientZeta *
      p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta) :=
  ComplexRationalBox.round_contains p2FastGrid_pos
    (ComplexRationalBox.mul_contains p2FastKappaZetaData_contains
      (p2GreenSeedPolynomialBox_contains p2FastZetaData_contains))

lemma p2ModeData_equalities :
    p2BaseLeftModeData = p2BaseLeftModeComputed ∧
    p2BaseRightModeData = p2BaseRightModeComputed ∧
    p2BaseNeutralModeData = p2BaseNeutralModeComputed ∧
    p2SeedLeftModeData = p2SeedLeftModeComputed ∧
    p2SeedRightModeData = p2SeedRightModeComputed ∧
    p2SeedNeutralModeData = p2SeedNeutralModeComputed := by
  decide +kernel

lemma p2BaseLeftModeData_contains : p2BaseLeftModeData.Contains
    (-p2CoefficientKappa p2CoefficientBeta *
      p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR) := by
  rw [p2ModeData_equalities.1]
  exact p2BaseLeftModeComputed_contains

lemma p2BaseRightModeData_contains : p2BaseRightModeData.Contains
    (-p2CoefficientKappa p2CoefficientR *
      p2CoefficientBase.eval₂ (Int.castRingHom ℝ) p2CoefficientR) := by
  rw [p2ModeData_equalities.2.1]
  exact p2BaseRightModeComputed_contains

lemma p2BaseNeutralModeData_contains : p2BaseNeutralModeData.Contains
    (-(p2CoefficientKappaComplex p2CoefficientZeta *
      p2CoefficientBase.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta)) := by
  rw [p2ModeData_equalities.2.2.1]
  exact p2BaseNeutralModeComputed_contains

lemma p2SeedLeftModeData_contains : p2SeedLeftModeData.Contains
    (-p2CoefficientKappa p2CoefficientBeta *
      p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR) := by
  rw [p2ModeData_equalities.2.2.2.1]
  exact p2SeedLeftModeComputed_contains

lemma p2SeedRightModeData_contains : p2SeedRightModeData.Contains
    (p2CoefficientKappa p2CoefficientR *
      p2CoefficientSeed.eval₂ (Int.castRingHom ℝ) p2CoefficientR) := by
  rw [p2ModeData_equalities.2.2.2.2.1]
  exact p2SeedRightModeComputed_contains

lemma p2SeedNeutralModeData_contains : p2SeedNeutralModeData.Contains
    (p2CoefficientKappaComplex p2CoefficientZeta *
      p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta) := by
  rw [p2ModeData_equalities.2.2.2.2.2]
  exact p2SeedNeutralModeComputed_contains

end Salem
