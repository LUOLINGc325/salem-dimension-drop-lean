module

public import Salem.P2CoreChecks.Block19

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2560 through 2567. -/
theorem p2CoreCheck320 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 320 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 320 ≤ p2CoreChunkBudget 320 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2568 through 2575. -/
theorem p2CoreCheck321 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 321 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 321 ≤ p2CoreChunkBudget 321 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2576 through 2583. -/
theorem p2CoreCheck322 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 322 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 322 ≤ p2CoreChunkBudget 322 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2584 through 2591. -/
theorem p2CoreCheck323 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 323 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 323 ≤ p2CoreChunkBudget 323 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2592 through 2599. -/
theorem p2CoreCheck324 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 324 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 324 ≤ p2CoreChunkBudget 324 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2600 through 2607. -/
theorem p2CoreCheck325 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 325 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 325 ≤ p2CoreChunkBudget 325 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2608 through 2615. -/
theorem p2CoreCheck326 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 326 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 326 ≤ p2CoreChunkBudget 326 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2616 through 2623. -/
theorem p2CoreCheck327 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 327 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 327 ≤ p2CoreChunkBudget 327 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2624 through 2631. -/
theorem p2CoreCheck328 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 328 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 328 ≤ p2CoreChunkBudget 328 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2632 through 2639. -/
theorem p2CoreCheck329 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 329 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 329 ≤ p2CoreChunkBudget 329 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2640 through 2647. -/
theorem p2CoreCheck330 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 330 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 330 ≤ p2CoreChunkBudget 330 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2648 through 2655. -/
theorem p2CoreCheck331 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 331 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 331 ≤ p2CoreChunkBudget 331 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2656 through 2663. -/
theorem p2CoreCheck332 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 332 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 332 ≤ p2CoreChunkBudget 332 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2664 through 2671. -/
theorem p2CoreCheck333 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 333 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 333 ≤ p2CoreChunkBudget 333 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2672 through 2679. -/
theorem p2CoreCheck334 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 334 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 334 ≤ p2CoreChunkBudget 334 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2680 through 2687. -/
theorem p2CoreCheck335 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 335 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 335 ≤ p2CoreChunkBudget 335 := by decide +kernel

end Salem
