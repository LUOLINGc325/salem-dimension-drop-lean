module

public import Salem.IntervalData

@[expose] public section

namespace Salem

def p2FastGrid : ℕ := 10 ^ 12

def p2FastRData : RationalInterval := ⟨531010056459 / 10 ^ 12, 531010056460 / 10 ^ 12⟩

def p2FastKappaBetaData : RationalInterval := ⟨138841380999 / 10 ^ 12, 138841381000 / 10 ^ 12⟩

def p2FastKappaRData : RationalInterval := ⟨-492394771593 / 10 ^ 12, -492394771592 / 10 ^ 12⟩

def p2FastZetaData : ComplexRationalBox :=
  ⟨⟨-207106781187 / 10 ^ 12, -207106781186 / 10 ^ 12⟩,
   ⟨978318343478 / 10 ^ 12, 978318343479 / 10 ^ 12⟩⟩

def p2FastKappaZetaData : ComplexRationalBox :=
  ⟨⟨176776695296 / 10 ^ 12, 176776695297 / 10 ^ 12⟩,
   ⟨-37423045981 / 10 ^ 12, -37423045980 / 10 ^ 12⟩⟩

/-- Beyond exponent 48 a simple exact rational comparison replaces stable powers. -/
def p2GreenStablePowerInterval (n : ℕ) : RationalInterval :=
  if 48 ≤ n then ⟨0, 1 / 10 ^ 12⟩ else p2FastRData.powRounded p2FastGrid n

/-- Small explicit mode boxes avoid recomputing constant polynomial evaluations
in each finite coordinate.  Equality is checked by the Lean kernel below. -/
def p2BaseLeftModeData : RationalInterval := ⟨-93389688405 / 10 ^ 12, -93389688401 / 10 ^ 12⟩

def p2BaseRightModeData : RationalInterval := ⟨331202368910 / 10 ^ 12, 331202368919 / 10 ^ 12⟩

def p2BaseNeutralModeData : ComplexRationalBox :=
  ⟨⟨1262658457 / 10 ^ 12, 1262658484 / 10 ^ 12⟩,
   ⟨-8167732091 / 10 ^ 12, -8167732064 / 10 ^ 12⟩⟩

def p2SeedLeftModeData : RationalInterval := ⟨-93389688405 / 10 ^ 12, -93389688401 / 10 ^ 12⟩

def p2SeedRightModeData : RationalInterval := ⟨-331202368919 / 10 ^ 12, -331202368910 / 10 ^ 12⟩

def p2SeedNeutralModeData : ComplexRationalBox :=
  ⟨⟨-2310696 / 10 ^ 12, -2309335 / 10 ^ 12⟩,
   ⟨-357453 / 10 ^ 12, -356093 / 10 ^ 12⟩⟩

/-- A computed enclosure of the actual bilateral Green coordinate. -/
def p2GreenFastRawCoordinateInterval (i : ℤ) : RationalInterval :=
  if i ≤ 0 then
    (p2FastKappaBetaData.neg.mul
      (p2FastRData.powRounded p2FastGrid (1 - i).toNat)).round p2FastGrid
  else
    ((p2FastKappaRData.mul (p2FastRData.powRounded p2FastGrid (i - 1).toNat)).add
      ((RationalInterval.point 2).mul
        (p2FastKappaZetaData.mul
          (p2FastZetaData.powRounded p2FastGrid (i - 1).toNat)).re)).round p2FastGrid

/-- The ten base impulses are enclosed with exact interval arithmetic. -/
def p2GreenFastRawBaseInterval (i : ℤ) : RationalInterval :=
  let A := (p2GreenFastRawCoordinateInterval i).sub (p2GreenFastRawCoordinateInterval (i - 1))
  let B := A.add (p2GreenFastRawCoordinateInterval (i - 2))
  let C := B.sub (p2GreenFastRawCoordinateInterval (i - 3))
  let D := C.add (p2GreenFastRawCoordinateInterval (i - 4))
  let E := D.sub (p2GreenFastRawCoordinateInterval (i - 7))
  let F := E.add (p2GreenFastRawCoordinateInterval (i - 8))
  let G := F.sub (p2GreenFastRawCoordinateInterval (i - 9))
  let H := G.add (p2GreenFastRawCoordinateInterval (i - 10))
  (H.sub (p2GreenFastRawCoordinateInterval (i - 11))).round p2FastGrid

/-- Evaluate the base profile by closed homogeneous modes outside its eleven junctions. -/
def p2GreenFastBaseInterval (i : ℤ) : RationalInterval :=
  if i ≤ 0 then
    (p2BaseLeftModeData.mul (p2GreenStablePowerInterval (1 - i).toNat)).round p2FastGrid
  else if 12 ≤ i then
    ((p2BaseRightModeData.mul (p2GreenStablePowerInterval (i - 12).toNat)).add
      ((RationalInterval.point 2).mul
        (p2BaseNeutralModeData.mul
          (p2FastZetaData.powRounded p2FastGrid (i - 12).toNat)).re)).round p2FastGrid
  else p2GreenFastRawBaseInterval i

/-- Evaluate the complete actual seed by its exact homogeneous exterior pieces
and the two short junction windows. -/
def p2GreenFastSeedInterval (i : ℤ) : RationalInterval :=
  if i ≤ 100 then
    (p2SeedLeftModeData.mul (p2GreenStablePowerInterval (101 - i).toNat)).round p2FastGrid
  else if 2785 ≤ i then
    ((p2SeedRightModeData.mul (p2GreenStablePowerInterval (i - 2785).toNat)).add
      ((RationalInterval.point 2).mul
        (p2SeedNeutralModeData.mul
          (p2FastZetaData.powRounded p2FastGrid (i - 2785).toNat)).re)).round p2FastGrid
  else
    ((p2GreenFastBaseInterval (i - 100)).sub
      (p2GreenFastBaseInterval (i - 2773))).round p2FastGrid

def p2GreenFastCoreRadius (j : Fin 2885) : ℚ :=
  ((RationalInterval.point (p2GreenFastSeedInterval (j.val : ℤ)).absUpper).round 1000000).hi

end Salem
