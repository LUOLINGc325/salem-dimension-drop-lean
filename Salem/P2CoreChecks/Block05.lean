module

public import Salem.P2CoreChecks.Block04

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 640 through 647. -/
theorem p2CoreCheck080 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 80 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 80 ≤ p2CoreChunkBudget 80 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 648 through 655. -/
theorem p2CoreCheck081 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 81 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 81 ≤ p2CoreChunkBudget 81 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 656 through 663. -/
theorem p2CoreCheck082 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 82 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 82 ≤ p2CoreChunkBudget 82 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 664 through 671. -/
theorem p2CoreCheck083 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 83 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 83 ≤ p2CoreChunkBudget 83 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 672 through 679. -/
theorem p2CoreCheck084 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 84 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 84 ≤ p2CoreChunkBudget 84 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 680 through 687. -/
theorem p2CoreCheck085 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 85 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 85 ≤ p2CoreChunkBudget 85 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 688 through 695. -/
theorem p2CoreCheck086 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 86 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 86 ≤ p2CoreChunkBudget 86 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 696 through 703. -/
theorem p2CoreCheck087 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 87 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 87 ≤ p2CoreChunkBudget 87 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 704 through 711. -/
theorem p2CoreCheck088 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 88 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 88 ≤ p2CoreChunkBudget 88 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 712 through 719. -/
theorem p2CoreCheck089 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 89 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 89 ≤ p2CoreChunkBudget 89 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 720 through 727. -/
theorem p2CoreCheck090 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 90 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 90 ≤ p2CoreChunkBudget 90 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 728 through 735. -/
theorem p2CoreCheck091 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 91 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 91 ≤ p2CoreChunkBudget 91 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 736 through 743. -/
theorem p2CoreCheck092 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 92 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 92 ≤ p2CoreChunkBudget 92 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 744 through 751. -/
theorem p2CoreCheck093 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 93 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 93 ≤ p2CoreChunkBudget 93 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 752 through 759. -/
theorem p2CoreCheck094 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 94 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 94 ≤ p2CoreChunkBudget 94 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 760 through 767. -/
theorem p2CoreCheck095 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 95 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 95 ≤ p2CoreChunkBudget 95 := by decide +kernel

end Salem
