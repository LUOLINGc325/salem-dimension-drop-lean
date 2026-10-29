module

public import Salem.P2FiniteData

public import Salem.P2GreenModeData

@[expose] public section

namespace Salem

lemma p2GreenFastRawCoordinateInterval_contains (i : ℤ) :
    (p2GreenFastRawCoordinateInterval i).Contains (p2GreenCoordinate i) := by
  by_cases hi : i ≤ 0
  · have h := RationalInterval.round_contains p2FastGrid_pos
      (RationalInterval.mul_contains
        (RationalInterval.neg_contains p2FastKappaBetaData_contains)
        (RationalInterval.powRounded_contains p2FastGrid_pos p2FastRData_contains (1 - i).toNat))
    simpa only [p2GreenFastRawCoordinateInterval, p2GreenCoordinate, p2GreenStableCoordinate,
      p2GreenNeutralCoordinate, ite_eq_left hi, add_zero] using h
  · have hp := RationalInterval.powRounded_contains p2FastGrid_pos
      p2FastRData_contains (i - 1).toNat
    have hz := ComplexRationalBox.powRounded_contains p2FastGrid_pos
      p2FastZetaData_contains (i - 1).toNat
    have hn := RationalInterval.mul_contains
      (by simpa using RationalInterval.point_contains 2)
      (ComplexRationalBox.mul_contains p2FastKappaZetaData_contains hz).1
    have h := RationalInterval.round_contains p2FastGrid_pos
      (RationalInterval.add_contains
        (RationalInterval.mul_contains p2FastKappaRData_contains hp) hn)
    simpa only [p2GreenFastRawCoordinateInterval, p2GreenCoordinate, p2GreenStableCoordinate,
      p2GreenNeutralCoordinate, ite_eq_right hi] using h

lemma p2GreenFastRawBaseInterval_contains (i : ℤ) :
    (p2GreenFastRawBaseInterval i).Contains (p2GreenBaseCoordinate i) := by
  have hA := RationalInterval.sub_contains (p2GreenFastRawCoordinateInterval_contains i)
    (p2GreenFastRawCoordinateInterval_contains (i - 1))
  have hB := RationalInterval.add_contains hA (p2GreenFastRawCoordinateInterval_contains (i - 2))
  have hC := RationalInterval.sub_contains hB (p2GreenFastRawCoordinateInterval_contains (i - 3))
  have hD := RationalInterval.add_contains hC (p2GreenFastRawCoordinateInterval_contains (i - 4))
  have hE := RationalInterval.sub_contains hD (p2GreenFastRawCoordinateInterval_contains (i - 7))
  have hF := RationalInterval.add_contains hE (p2GreenFastRawCoordinateInterval_contains (i - 8))
  have hG := RationalInterval.sub_contains hF (p2GreenFastRawCoordinateInterval_contains (i - 9))
  have hH := RationalInterval.add_contains hG (p2GreenFastRawCoordinateInterval_contains (i - 10))
  have h := RationalInterval.round_contains p2FastGrid_pos
    (RationalInterval.sub_contains hH (p2GreenFastRawCoordinateInterval_contains (i - 11)))
  simpa only [p2GreenFastRawBaseInterval, p2GreenBaseCoordinate] using h

lemma p2GreenFastBaseInterval_contains (i : ℤ) :
    (p2GreenFastBaseInterval i).Contains (p2GreenBaseCoordinate i) := by
  by_cases hleft : i ≤ 0
  · have h := RationalInterval.round_contains p2FastGrid_pos
      (RationalInterval.mul_contains p2BaseLeftModeData_contains
        (p2GreenStablePowerInterval_contains (1 - i).toNat))
    simpa only [p2GreenFastBaseInterval, ite_eq_left hleft, p2GreenBaseCoordinate_left hleft] using h
  · by_cases hright : 12 ≤ i
    · have hp := ComplexRationalBox.powRounded_contains p2FastGrid_pos
        p2FastZetaData_contains (i - 12).toNat
      have hn := RationalInterval.mul_contains
        (by simpa using RationalInterval.point_contains 2)
        (ComplexRationalBox.mul_contains p2BaseNeutralModeData_contains hp).1
      have h := RationalInterval.round_contains p2FastGrid_pos
        (RationalInterval.add_contains
          (RationalInterval.mul_contains p2BaseRightModeData_contains
            (p2GreenStablePowerInterval_contains (i - 12).toNat)) hn)
      simpa only [p2GreenFastBaseInterval, ite_eq_right hleft, ite_eq_left hright,
        p2GreenBaseCoordinate_right hright, neg_mul, mul_neg, Complex.neg_re, sub_eq_add_neg] using h
    · simpa only [p2GreenFastBaseInterval, ite_eq_right hleft, ite_eq_right hright] using
        p2GreenFastRawBaseInterval_contains i

lemma p2GreenFastSeedInterval_contains (i : ℤ) :
    (p2GreenFastSeedInterval i).Contains (p2GreenSeedCoordinate i) := by
  by_cases hleft : i ≤ 100
  · have h := RationalInterval.round_contains p2FastGrid_pos
      (RationalInterval.mul_contains p2SeedLeftModeData_contains
        (p2GreenStablePowerInterval_contains (101 - i).toNat))
    simpa only [p2GreenFastSeedInterval, ite_eq_left hleft,
      p2GreenSeedCoordinate_left_mode hleft] using h
  · by_cases hright : 2785 ≤ i
    · have hp := ComplexRationalBox.powRounded_contains p2FastGrid_pos
        p2FastZetaData_contains (i - 2785).toNat
      have hn := RationalInterval.mul_contains
        (by simpa using RationalInterval.point_contains 2)
        (ComplexRationalBox.mul_contains p2SeedNeutralModeData_contains hp).1
      have h := RationalInterval.round_contains p2FastGrid_pos
        (RationalInterval.add_contains
          (RationalInterval.mul_contains p2SeedRightModeData_contains
            (p2GreenStablePowerInterval_contains (i - 2785).toNat)) hn)
      simpa only [p2GreenFastSeedInterval, ite_eq_right hleft, ite_eq_left hright,
        p2GreenSeedCoordinate_right_mode hright] using h
    · have h := RationalInterval.round_contains p2FastGrid_pos
        (RationalInterval.sub_contains (p2GreenFastBaseInterval_contains (i - 100))
          (p2GreenFastBaseInterval_contains (i - 2773)))
      simpa only [p2GreenFastSeedInterval, ite_eq_right hleft, ite_eq_right hright,
        p2GreenSeedCoordinate_sparse] using h

lemma p2GreenFastCoreRadius_upper (j : Fin 2885) :
    (p2GreenFastSeedInterval (j.val : ℤ)).absUpper ≤ p2GreenFastCoreRadius j := by
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000)).mpr (Int.le_ceil _)

lemma p2GreenFastCoreRadius_nonneg (j : Fin 2885) : 0 ≤ p2GreenFastCoreRadius j :=
  (RationalInterval.absUpper_nonneg _).trans (p2GreenFastCoreRadius_upper j)

lemma p2GreenFastCoreCoordinate_abs_le (j : Fin 2885) :
    |p2GreenSeedCoordinate (j.val : ℤ)| ≤ (p2GreenFastCoreRadius j : ℝ) := by
  have h := RationalInterval.abs_le_absUpper (p2GreenFastSeedInterval_contains (j.val : ℤ))
  exact h.trans (by exact_mod_cast p2GreenFastCoreRadius_upper j)

end Salem
