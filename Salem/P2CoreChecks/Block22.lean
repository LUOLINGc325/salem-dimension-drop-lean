module

public import Salem.P2CoreChecks.Block21

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2816 through 2823. -/
theorem p2CoreCheck352 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 352 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 352 ≤ p2CoreChunkBudget 352 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2824 through 2831. -/
theorem p2CoreCheck353 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 353 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 353 ≤ p2CoreChunkBudget 353 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2832 through 2839. -/
theorem p2CoreCheck354 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 354 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 354 ≤ p2CoreChunkBudget 354 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2840 through 2847. -/
theorem p2CoreCheck355 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 355 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 355 ≤ p2CoreChunkBudget 355 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2848 through 2855. -/
theorem p2CoreCheck356 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 356 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 356 ≤ p2CoreChunkBudget 356 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2856 through 2863. -/
theorem p2CoreCheck357 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 357 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 357 ≤ p2CoreChunkBudget 357 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2864 through 2871. -/
theorem p2CoreCheck358 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 358 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 358 ≤ p2CoreChunkBudget 358 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2872 through 2879. -/
theorem p2CoreCheck359 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 359 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 359 ≤ p2CoreChunkBudget 359 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2880 through 2884. -/
theorem p2CoreCheck360 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 360 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 360 ≤ p2CoreChunkBudget 360 := by decide +kernel

end Salem
