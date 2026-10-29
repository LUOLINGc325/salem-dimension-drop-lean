module

public import Salem.P2CoreChecks.Block20

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2688 through 2695. -/
theorem p2CoreCheck336 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 336 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 336 ≤ p2CoreChunkBudget 336 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2696 through 2703. -/
theorem p2CoreCheck337 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 337 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 337 ≤ p2CoreChunkBudget 337 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2704 through 2711. -/
theorem p2CoreCheck338 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 338 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 338 ≤ p2CoreChunkBudget 338 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2712 through 2719. -/
theorem p2CoreCheck339 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 339 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 339 ≤ p2CoreChunkBudget 339 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2720 through 2727. -/
theorem p2CoreCheck340 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 340 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 340 ≤ p2CoreChunkBudget 340 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2728 through 2735. -/
theorem p2CoreCheck341 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 341 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 341 ≤ p2CoreChunkBudget 341 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2736 through 2743. -/
theorem p2CoreCheck342 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 342 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 342 ≤ p2CoreChunkBudget 342 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2744 through 2751. -/
theorem p2CoreCheck343 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 343 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 343 ≤ p2CoreChunkBudget 343 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2752 through 2759. -/
theorem p2CoreCheck344 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 344 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 344 ≤ p2CoreChunkBudget 344 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2760 through 2767. -/
theorem p2CoreCheck345 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 345 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 345 ≤ p2CoreChunkBudget 345 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2768 through 2775. -/
theorem p2CoreCheck346 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 346 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 346 ≤ p2CoreChunkBudget 346 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2776 through 2783. -/
theorem p2CoreCheck347 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 347 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 347 ≤ p2CoreChunkBudget 347 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2784 through 2791. -/
theorem p2CoreCheck348 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 348 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 348 ≤ p2CoreChunkBudget 348 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2792 through 2799. -/
theorem p2CoreCheck349 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 349 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 349 ≤ p2CoreChunkBudget 349 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2800 through 2807. -/
theorem p2CoreCheck350 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 350 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 350 ≤ p2CoreChunkBudget 350 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2808 through 2815. -/
theorem p2CoreCheck351 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 351 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 351 ≤ p2CoreChunkBudget 351 := by decide +kernel

end Salem
