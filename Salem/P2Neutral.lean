module

public import Salem.P2Returns
public import Salem.P2GreenData

@[expose] public section

namespace Salem

/-- The actual outgoing neutral coefficient of the preprocessing seed. -/
noncomputable def p2GreenSeedNeutralCoefficient : ℂ :=
  p2CoefficientKappaComplex p2CoefficientZeta * (p2CoefficientZeta⁻¹) ^ 101 *
    p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) p2CoefficientZeta⁻¹

noncomputable def p2GreenSeedNeutralAmplitude : ℝ := 2 * ‖p2GreenSeedNeutralCoefficient‖

/-- The exact odd direct difference multiplier of the neutral coefficient. -/
noncomputable def p2GreenFinalNeutralCoefficient : ℂ :=
  (1 - (p2CoefficientZeta⁻¹) ^ 1846082221) * p2GreenSeedNeutralCoefficient

noncomputable def p2GreenFinalNeutralAmplitude : ℝ := 2 * ‖p2GreenFinalNeutralCoefficient‖

def p2GreenZetaInvBox : ComplexRationalBox := p2CoreZetaData.conj

lemma p2GreenZetaInvBox_contains : p2GreenZetaInvBox.Contains p2CoefficientZeta⁻¹ := by
  rw [Complex.inv_eq_conj p2CoefficientZeta_unit.1]
  exact ComplexRationalBox.conj_contains p2CoreZetaData_contains

/-- Certified evaluation of the ten-term base polynomial at any complex box. -/
def p2GreenBasePolynomialBox (I : ComplexRationalBox) : ComplexRationalBox :=
  let A := (I.powRounded p2GreenGrid 0).sub (I.powRounded p2GreenGrid 1)
  let B := A.add (I.powRounded p2GreenGrid 2)
  let C := B.sub (I.powRounded p2GreenGrid 3)
  let D := C.add (I.powRounded p2GreenGrid 4)
  let E := D.sub (I.powRounded p2GreenGrid 7)
  let F := E.add (I.powRounded p2GreenGrid 8)
  let G := F.sub (I.powRounded p2GreenGrid 9)
  let H := G.add (I.powRounded p2GreenGrid 10)
  (H.sub (I.powRounded p2GreenGrid 11)).round p2GreenGrid

lemma p2GreenBasePolynomialBox_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    (p2GreenBasePolynomialBox I).Contains (p2CoefficientBase.eval₂ (Int.castRingHom ℂ) z) := by
  have hp (n : ℕ) := ComplexRationalBox.powRounded_contains p2GreenGrid_pos hz n
  have hA := ComplexRationalBox.sub_contains (hp 0) (hp 1)
  have hB := ComplexRationalBox.add_contains hA (hp 2)
  have hC := ComplexRationalBox.sub_contains hB (hp 3)
  have hD := ComplexRationalBox.add_contains hC (hp 4)
  have hE := ComplexRationalBox.sub_contains hD (hp 7)
  have hF := ComplexRationalBox.add_contains hE (hp 8)
  have hG := ComplexRationalBox.sub_contains hF (hp 9)
  have hH := ComplexRationalBox.add_contains hG (hp 10)
  have h := ComplexRationalBox.round_contains p2GreenGrid_pos
    (ComplexRationalBox.sub_contains hH (hp 11))
  simpa only [p2GreenBasePolynomialBox, p2CoefficientBase, Polynomial.eval₂_sub,
    Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X] using h

def p2GreenSeedPolynomialBox (I : ComplexRationalBox) : ComplexRationalBox :=
  ((p2GreenBasePolynomialBox I).mul
    (ComplexRationalBox.one.sub (I.powRounded p2GreenGrid 2673))).round p2GreenGrid

lemma p2GreenSeedPolynomialBox_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    (p2GreenSeedPolynomialBox I).Contains (p2CoefficientSeed.eval₂ (Int.castRingHom ℂ) z) := by
  have h := ComplexRationalBox.round_contains p2GreenGrid_pos
    (ComplexRationalBox.mul_contains (p2GreenBasePolynomialBox_contains hz)
      (ComplexRationalBox.sub_contains ComplexRationalBox.one_contains
        (ComplexRationalBox.powRounded_contains p2GreenGrid_pos hz 2673)))
  simpa only [p2GreenSeedPolynomialBox, p2CoefficientSeed, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow, Polynomial.eval₂_X] using h

def p2GreenSeedNeutralBox : ComplexRationalBox :=
  ((p2CoreKappaZetaData.mul (p2GreenZetaInvBox.powRounded p2GreenGrid 101)).mul
    (p2GreenSeedPolynomialBox p2GreenZetaInvBox)).round p2GreenGrid

lemma p2GreenSeedNeutralBox_contains :
    p2GreenSeedNeutralBox.Contains p2GreenSeedNeutralCoefficient := by
  exact ComplexRationalBox.round_contains p2GreenGrid_pos
    (ComplexRationalBox.mul_contains
      (ComplexRationalBox.mul_contains p2CoreKappaZetaData_contains
        (ComplexRationalBox.powRounded_contains p2GreenGrid_pos p2GreenZetaInvBox_contains 101))
      (p2GreenSeedPolynomialBox_contains p2GreenZetaInvBox_contains))

def p2GreenFinalNeutralBox : ComplexRationalBox :=
  ((ComplexRationalBox.one.sub
      (p2GreenZetaInvBox.powRounded p2GreenGrid 1846082221)).mul p2GreenSeedNeutralBox).round p2GreenGrid

lemma p2GreenFinalNeutralBox_contains :
    p2GreenFinalNeutralBox.Contains p2GreenFinalNeutralCoefficient := by
  exact ComplexRationalBox.round_contains p2GreenGrid_pos
    (ComplexRationalBox.mul_contains
      (ComplexRationalBox.sub_contains ComplexRationalBox.one_contains
        (ComplexRationalBox.powRounded_contains p2GreenGrid_pos p2GreenZetaInvBox_contains 1846082221))
      p2GreenSeedNeutralBox_contains)

/-- Exact kernel checks of the actual small neutral coefficients. -/
lemma p2GreenNeutralBox_bounds :
    p2GreenSeedNeutralBox.ExcludesZero ∧
    p2GreenSeedNeutralBox.normSqUpper < (4674807 / (2 * 10 ^ 12) : ℚ) ^ 2 ∧
    p2GreenFinalNeutralBox.ExcludesZero ∧
    p2GreenFinalNeutralBox.normSqUpper < (1105305 / (2 * 10 ^ 21) : ℚ) ^ 2 := by
  decide +kernel

lemma p2GreenSeedNeutralAmplitude_bounds :
    0 < p2GreenSeedNeutralAmplitude ∧ p2GreenSeedNeutralAmplitude < (4674807 / 10 ^ 12 : ℝ) := by
  have hp := ComplexRationalBox.norm_pos p2GreenSeedNeutralBox_contains p2GreenNeutralBox_bounds.1
  have hs : (p2GreenSeedNeutralBox.normSqUpper : ℝ) < (4674807 / (2 * 10 ^ 12) : ℝ) ^ 2 := by
    have h : (p2GreenSeedNeutralBox.normSqUpper : ℝ) <
        (((4674807 / (2 * 10 ^ 12) : ℚ) ^ 2 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr p2GreenNeutralBox_bounds.2.1
    norm_num at h ⊢
    exact h
  have hb := ComplexRationalBox.norm_lt p2GreenSeedNeutralBox_contains (by norm_num) hs
  dsimp [p2GreenSeedNeutralAmplitude]
  constructor <;> linarith

lemma p2GreenFinalNeutralAmplitude_bounds :
    0 < p2GreenFinalNeutralAmplitude ∧ p2GreenFinalNeutralAmplitude < (1105305 / 10 ^ 21 : ℝ) := by
  have hp := ComplexRationalBox.norm_pos p2GreenFinalNeutralBox_contains p2GreenNeutralBox_bounds.2.2.1
  have hs : (p2GreenFinalNeutralBox.normSqUpper : ℝ) < (1105305 / (2 * 10 ^ 21) : ℝ) ^ 2 := by
    have h : (p2GreenFinalNeutralBox.normSqUpper : ℝ) <
        (((1105305 / (2 * 10 ^ 21) : ℚ) ^ 2 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr p2GreenNeutralBox_bounds.2.2.2
    norm_num at h ⊢
    exact h
  have hb := ComplexRationalBox.norm_lt p2GreenFinalNeutralBox_contains (by norm_num) hs
  dsimp [p2GreenFinalNeutralAmplitude]
  constructor <;> linarith

end Salem
