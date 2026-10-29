module

public import Salem.P2CoreChecks.Block03

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 512 through 519. -/
theorem p2CoreCheck064 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 64 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 64 ≤ p2CoreChunkBudget 64 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 520 through 527. -/
theorem p2CoreCheck065 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 65 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 65 ≤ p2CoreChunkBudget 65 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 528 through 535. -/
theorem p2CoreCheck066 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 66 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 66 ≤ p2CoreChunkBudget 66 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 536 through 543. -/
theorem p2CoreCheck067 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 67 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 67 ≤ p2CoreChunkBudget 67 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 544 through 551. -/
theorem p2CoreCheck068 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 68 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 68 ≤ p2CoreChunkBudget 68 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 552 through 559. -/
theorem p2CoreCheck069 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 69 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 69 ≤ p2CoreChunkBudget 69 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 560 through 567. -/
theorem p2CoreCheck070 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 70 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 70 ≤ p2CoreChunkBudget 70 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 568 through 575. -/
theorem p2CoreCheck071 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 71 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 71 ≤ p2CoreChunkBudget 71 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 576 through 583. -/
theorem p2CoreCheck072 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 72 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 72 ≤ p2CoreChunkBudget 72 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 584 through 591. -/
theorem p2CoreCheck073 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 73 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 73 ≤ p2CoreChunkBudget 73 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 592 through 599. -/
theorem p2CoreCheck074 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 74 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 74 ≤ p2CoreChunkBudget 74 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 600 through 607. -/
theorem p2CoreCheck075 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 75 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 75 ≤ p2CoreChunkBudget 75 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 608 through 615. -/
theorem p2CoreCheck076 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 76 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 76 ≤ p2CoreChunkBudget 76 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 616 through 623. -/
theorem p2CoreCheck077 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 77 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 77 ≤ p2CoreChunkBudget 77 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 624 through 631. -/
theorem p2CoreCheck078 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 78 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 78 ≤ p2CoreChunkBudget 78 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 632 through 639. -/
theorem p2CoreCheck079 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 79 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 79 ≤ p2CoreChunkBudget 79 := by decide +kernel

end Salem
