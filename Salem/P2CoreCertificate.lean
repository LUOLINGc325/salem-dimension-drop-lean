module

public import Salem.P2CoreAssembly
public import Salem.P2CoreChecks
public import Salem.CosineTail

@[expose] public section

namespace Salem

open scoped BigOperators

/-- The actual 2885-coordinate seed is strictly inside the centered interval. -/
theorem p2GreenSeedCoordinate_core_abs_le (i : Fin 2885) :
    |p2GreenSeedCoordinate (i.val : ℤ)| ≤ (2 / 5 : ℝ) := by
  have h := (p2GreenFastCoreCoordinate_abs_le i).trans
    (Rat.cast_le.2 (p2Core_radius_le_of_checks p2Core_all_checks i))
  norm_num at h
  exact h

/-- Exact rational computation bounds the actual full seed action. -/
theorem p2GreenSeedCoordinate_core_action_le_exact :
    (∑ i : Fin 2885, cosinePotential (p2GreenSeedCoordinate (i.val : ℤ))) ≤
      (23712521 / 1000000 : ℝ) :=
  p2Core_action_le_of_checks p2Core_all_checks

/-- A convenient cap for the unchanged P2 direct-difference construction. -/
theorem p2GreenSeedCoordinate_core_action_le :
    (∑ i : Fin 2885, cosinePotential (p2GreenSeedCoordinate (i.val : ℤ))) ≤
      (4743 / 200 : ℝ) :=
  p2GreenSeedCoordinate_core_action_le_exact.trans (by norm_num)

/-- The core enclosure proves nonvanishing of every actual cosine factor. -/
theorem p2GreenSeedCoordinate_core_cos_pos (i : Fin 2885) :
    0 < Real.cos (Real.pi * p2GreenSeedCoordinate (i.val : ℤ)) :=
  cosinePotential_cos_pos ((p2GreenSeedCoordinate_core_abs_le i).trans_lt (by norm_num))

end Salem
