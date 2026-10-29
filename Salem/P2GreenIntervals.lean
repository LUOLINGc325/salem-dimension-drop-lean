module

public import Salem.P2GreenCore

@[expose] public section

namespace Salem

def p2GreenGrid : ℕ := 10 ^ 40
lemma p2GreenGrid_pos : 0 < p2GreenGrid := by norm_num [p2GreenGrid]

def p2GreenSqrt2Interval : RationalInterval :=
  (RationalInterval.point 2).sqrt p2GreenGrid

def p2GreenTraceUInterval : RationalInterval :=
  (RationalInterval.point 1).add p2GreenSqrt2Interval

def p2GreenTraceVInterval : RationalInterval :=
  (RationalInterval.point 1).sub p2GreenSqrt2Interval

def p2GreenBetaRadicandInterval : RationalInterval :=
  (p2GreenTraceUInterval.mul p2GreenTraceUInterval).sub (RationalInterval.point 4)

def p2GreenBetaInterval : RationalInterval :=
  ((p2GreenTraceUInterval.add (p2GreenBetaRadicandInterval.sqrt p2GreenGrid)).mul
    (RationalInterval.point (1 / 2))).round p2GreenGrid

def p2GreenRInterval : RationalInterval := p2GreenBetaInterval.inv.round p2GreenGrid

def p2GreenZetaRadicandInterval : RationalInterval :=
  (RationalInterval.point 4).sub (p2GreenTraceVInterval.mul p2GreenTraceVInterval)

def p2GreenZetaBox : ComplexRationalBox :=
  ComplexRationalBox.round p2GreenGrid
    ⟨p2GreenTraceVInterval.mul (RationalInterval.point (1 / 2)),
     (p2GreenZetaRadicandInterval.sqrt p2GreenGrid).mul (RationalInterval.point (1 / 2))⟩

lemma p2GreenSqrt2Interval_contains : p2GreenSqrt2Interval.Contains (Real.sqrt 2) := by
  exact RationalInterval.sqrt_contains p2GreenGrid_pos
    (by simpa using RationalInterval.point_contains 2) (by norm_num [RationalInterval.point])

lemma p2GreenTraceUInterval_contains : p2GreenTraceUInterval.Contains (1 + Real.sqrt 2) := by
  exact RationalInterval.add_contains (by simpa using RationalInterval.point_contains 1)
    p2GreenSqrt2Interval_contains

lemma p2GreenTraceVInterval_contains : p2GreenTraceVInterval.Contains (1 - Real.sqrt 2) := by
  exact RationalInterval.sub_contains (by simpa using RationalInterval.point_contains 1)
    p2GreenSqrt2Interval_contains

lemma p2GreenBetaInterval_contains : p2GreenBetaInterval.Contains p2CoefficientBeta := by
  have hrad : p2GreenBetaRadicandInterval.Contains ((1 + Real.sqrt 2) ^ 2 - 4) := by
    simpa only [p2GreenBetaRadicandInterval, pow_two] using
      RationalInterval.sub_contains
        (RationalInterval.mul_contains p2GreenTraceUInterval_contains p2GreenTraceUInterval_contains)
        (by simpa using RationalInterval.point_contains 4)
  have hroot := RationalInterval.sqrt_contains p2GreenGrid_pos hrad
    (by decide +kernel : 0 ≤ p2GreenBetaRadicandInterval.lo)
  have hsum := RationalInterval.add_contains p2GreenTraceUInterval_contains hroot
  have hhalf := RationalInterval.mul_contains hsum (RationalInterval.point_contains (1 / 2))
  have hr := RationalInterval.round_contains p2GreenGrid_pos hhalf
  simpa only [p2GreenBetaInterval, p2CoefficientBeta, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_ofNat,
    div_eq_mul_inv, one_mul] using hr

lemma p2GreenRInterval_contains : p2GreenRInterval.Contains p2CoefficientR := by
  exact RationalInterval.round_contains p2GreenGrid_pos
    (RationalInterval.inv_contains p2GreenBetaInterval_contains
      (by decide +kernel : 0 < p2GreenBetaInterval.lo))

lemma p2GreenZetaBox_contains : p2GreenZetaBox.Contains p2CoefficientZeta := by
  have hrad : p2GreenZetaRadicandInterval.Contains (4 - (1 - Real.sqrt 2) ^ 2) := by
    simpa only [p2GreenZetaRadicandInterval, pow_two] using RationalInterval.sub_contains
      (by simpa using RationalInterval.point_contains 4)
      (RationalInterval.mul_contains p2GreenTraceVInterval_contains p2GreenTraceVInterval_contains)
  have hroot := RationalInterval.sqrt_contains p2GreenGrid_pos hrad
    (by decide +kernel : 0 ≤ p2GreenZetaRadicandInterval.lo)
  apply ComplexRationalBox.round_contains p2GreenGrid_pos
  constructor
  · simpa only [p2CoefficientZeta, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_ofNat,
      div_eq_mul_inv, one_mul] using
      RationalInterval.mul_contains p2GreenTraceVInterval_contains
        (RationalInterval.point_contains (1 / 2))
  · simpa only [p2CoefficientZeta, Rat.cast_div, Rat.cast_inv, Rat.cast_one, Rat.cast_ofNat,
      div_eq_mul_inv, one_mul] using
      RationalInterval.mul_contains hroot (RationalInterval.point_contains (1 / 2))

/-- Horner evaluation of the actual real derivative on an interval. -/
def p2GreenDerivativeInterval (I : RationalInterval) : RationalInterval :=
  (((((RationalInterval.point 4).mul I).sub (RationalInterval.point 6)).mul I).add
    (RationalInterval.point 2)).mul I |>.sub (RationalInterval.point 2)

lemma p2GreenDerivativeInterval_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    (p2GreenDerivativeInterval I).Contains (p2CoefficientDerivative x) := by
  have h := RationalInterval.sub_contains
    (RationalInterval.mul_contains
      (RationalInterval.add_contains
        (RationalInterval.mul_contains
          (RationalInterval.sub_contains
            (RationalInterval.mul_contains
              (by simpa using RationalInterval.point_contains 4) hx)
            (by simpa using RationalInterval.point_contains 6)) hx)
        (by simpa using RationalInterval.point_contains 2)) hx)
    (by simpa using RationalInterval.point_contains 2)
  change (p2GreenDerivativeInterval I).Contains (((4 * x - 6) * x + 2) * x - 2) at h
  convert h using 1
  dsimp [p2CoefficientDerivative]
  ring

def p2GreenKappaBetaInterval : RationalInterval :=
  (p2GreenDerivativeInterval p2GreenBetaInterval).inv.round p2GreenGrid

def p2GreenKappaRInterval : RationalInterval :=
  (p2GreenDerivativeInterval p2GreenRInterval).inv.round p2GreenGrid

lemma p2GreenKappaBetaInterval_contains :
    p2GreenKappaBetaInterval.Contains (p2CoefficientKappa p2CoefficientBeta) := by
  have h := RationalInterval.round_contains p2GreenGrid_pos
    (RationalInterval.inv_contains
      (p2GreenDerivativeInterval_contains p2GreenBetaInterval_contains)
      (by decide +kernel : 0 < (p2GreenDerivativeInterval p2GreenBetaInterval).lo))
  simpa only [p2GreenKappaBetaInterval, p2CoefficientKappa, p2CoefficientDerivative_eval] using h

lemma p2GreenKappaRInterval_contains :
    p2GreenKappaRInterval.Contains (p2CoefficientKappa p2CoefficientR) := by
  have h := RationalInterval.round_contains p2GreenGrid_pos
    (RationalInterval.inv_contains_of_neg
      (p2GreenDerivativeInterval_contains p2GreenRInterval_contains)
      (by decide +kernel : (p2GreenDerivativeInterval p2GreenRInterval).hi < 0))
  simpa only [p2GreenKappaRInterval, p2CoefficientKappa, p2CoefficientDerivative_eval] using h

def p2GreenRealBox (q : ℚ) : ComplexRationalBox :=
  ComplexRationalBox.ofRealInterval (RationalInterval.point q)

lemma p2GreenRealBox_contains (q : ℚ) : (p2GreenRealBox q).Contains (q : ℂ) := by
  simpa only [p2GreenRealBox, Complex.ofReal_ratCast] using
    ComplexRationalBox.ofRealInterval_contains (RationalInterval.point_contains q)

def p2GreenDerivativeBox (I : ComplexRationalBox) : ComplexRationalBox :=
  (((((p2GreenRealBox 4).mul I).sub (p2GreenRealBox 6)).mul I).add
    (p2GreenRealBox 2)).mul I |>.sub (p2GreenRealBox 2)

lemma p2GreenDerivative_complex_eval (z : ℂ) :
    p2CoefficientPolynomial.derivative.eval₂ (Int.castRingHom ℂ) z =
      4 * z ^ 3 - 6 * z ^ 2 + 2 * z - 2 := by
  simp [p2CoefficientPolynomial]
  ring

lemma p2GreenDerivativeBox_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    (p2GreenDerivativeBox I).Contains
      (p2CoefficientPolynomial.derivative.eval₂ (Int.castRingHom ℂ) z) := by
  have h := ComplexRationalBox.sub_contains
    (ComplexRationalBox.mul_contains
      (ComplexRationalBox.add_contains
        (ComplexRationalBox.mul_contains
          (ComplexRationalBox.sub_contains
            (ComplexRationalBox.mul_contains (by simpa using p2GreenRealBox_contains 4) hz)
            (by simpa using p2GreenRealBox_contains 6)) hz)
        (by simpa using p2GreenRealBox_contains 2)) hz)
    (by simpa using p2GreenRealBox_contains 2)
  change (p2GreenDerivativeBox I).Contains (((4 * z - 6) * z + 2) * z - 2) at h
  convert h using 1
  rw [p2GreenDerivative_complex_eval]
  ring

def p2GreenKappaZetaBox : ComplexRationalBox :=
  (p2GreenDerivativeBox p2GreenZetaBox).inv.round p2GreenGrid

lemma p2GreenKappaZetaBox_contains :
    p2GreenKappaZetaBox.Contains (p2CoefficientKappaComplex p2CoefficientZeta) := by
  exact ComplexRationalBox.round_contains p2GreenGrid_pos
    (ComplexRationalBox.inv_contains
      (p2GreenDerivativeBox_contains p2GreenZetaBox_contains)
      (by decide +kernel : 0 < (p2GreenDerivativeBox p2GreenZetaBox).normSqInterval.lo))

end Salem
