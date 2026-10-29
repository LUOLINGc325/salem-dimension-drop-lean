module

public import Salem.P2GreenIntervals

@[expose] public section

namespace Salem

/-- Explicit rational input data for finite checking.  Each datum is proved
exactly equal to the previously certified computable interval. -/
def p2CoreRData : RationalInterval :=
  ⟨5310100564595691846327412588476429880087 / 10 ^ 40,
   5310100564595691846327412588476429880088 / 10 ^ 40⟩

def p2CoreKappaBetaData : RationalInterval :=
  ⟨1388413809993088088299126521182059307752 / 10 ^ 40,
   1388413809993088088299126521182059307753 / 10 ^ 40⟩

def p2CoreKappaRData : RationalInterval :=
  ⟨-4923947715925825710303348331706304504177 / 10 ^ 40,
   -4923947715925825710303348331706304504175 / 10 ^ 40⟩

def p2CoreZetaData : ComplexRationalBox :=
  ⟨⟨-2071067811865475244008443621048490392849 / 10 ^ 40,
     -2071067811865475244008443621048490392848 / 10 ^ 40⟩,
   ⟨9783183434785159564221044363850222152532 / 10 ^ 40,
     9783183434785159564221044363850222152533 / 10 ^ 40⟩⟩

def p2CoreKappaZetaData : ComplexRationalBox :=
  ⟨⟨1767766952966368811002110905262122598210 / 10 ^ 40,
     1767766952966368811002110905262122598214 / 10 ^ 40⟩,
   ⟨-374230459806210899290571337925617197335 / 10 ^ 40,
     -374230459806210899290571337925617197333 / 10 ^ 40⟩⟩

lemma p2CoreData_equalities :
    p2CoreRData = p2GreenRInterval ∧
    p2CoreKappaBetaData = p2GreenKappaBetaInterval ∧
    p2CoreKappaRData = p2GreenKappaRInterval ∧
    p2CoreZetaData = p2GreenZetaBox ∧
    p2CoreKappaZetaData = p2GreenKappaZetaBox := by
  decide +kernel

lemma p2CoreRData_contains : p2CoreRData.Contains p2CoefficientR := by
  rw [p2CoreData_equalities.1]
  exact p2GreenRInterval_contains

lemma p2CoreKappaBetaData_contains :
    p2CoreKappaBetaData.Contains (p2CoefficientKappa p2CoefficientBeta) := by
  rw [p2CoreData_equalities.2.1]
  exact p2GreenKappaBetaInterval_contains

lemma p2CoreKappaRData_contains : p2CoreKappaRData.Contains (p2CoefficientKappa p2CoefficientR) := by
  rw [p2CoreData_equalities.2.2.1]
  exact p2GreenKappaRInterval_contains

lemma p2CoreZetaData_contains : p2CoreZetaData.Contains p2CoefficientZeta := by
  rw [p2CoreData_equalities.2.2.2.1]
  exact p2GreenZetaBox_contains

lemma p2CoreKappaZetaData_contains :
    p2CoreKappaZetaData.Contains (p2CoefficientKappaComplex p2CoefficientZeta) := by
  rw [p2CoreData_equalities.2.2.2.2]
  exact p2GreenKappaZetaBox_contains

end Salem
