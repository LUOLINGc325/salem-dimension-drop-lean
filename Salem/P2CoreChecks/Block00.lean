module

public import Salem.P2CoreData

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 0 through 7. -/
theorem p2CoreCheck000 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 0 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 0 ≤ p2CoreChunkBudget 0 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 8 through 15. -/
theorem p2CoreCheck001 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 1 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 1 ≤ p2CoreChunkBudget 1 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 16 through 23. -/
theorem p2CoreCheck002 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 2 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 2 ≤ p2CoreChunkBudget 2 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 24 through 31. -/
theorem p2CoreCheck003 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 3 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 3 ≤ p2CoreChunkBudget 3 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 32 through 39. -/
theorem p2CoreCheck004 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 4 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 4 ≤ p2CoreChunkBudget 4 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 40 through 47. -/
theorem p2CoreCheck005 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 5 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 5 ≤ p2CoreChunkBudget 5 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 48 through 55. -/
theorem p2CoreCheck006 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 6 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 6 ≤ p2CoreChunkBudget 6 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 56 through 63. -/
theorem p2CoreCheck007 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 7 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 7 ≤ p2CoreChunkBudget 7 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 64 through 71. -/
theorem p2CoreCheck008 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 8 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 8 ≤ p2CoreChunkBudget 8 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 72 through 79. -/
theorem p2CoreCheck009 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 9 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 9 ≤ p2CoreChunkBudget 9 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 80 through 87. -/
theorem p2CoreCheck010 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 10 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 10 ≤ p2CoreChunkBudget 10 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 88 through 95. -/
theorem p2CoreCheck011 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 11 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 11 ≤ p2CoreChunkBudget 11 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 96 through 103. -/
theorem p2CoreCheck012 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 12 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 12 ≤ p2CoreChunkBudget 12 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 104 through 111. -/
theorem p2CoreCheck013 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 13 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 13 ≤ p2CoreChunkBudget 13 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 112 through 119. -/
theorem p2CoreCheck014 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 14 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 14 ≤ p2CoreChunkBudget 14 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 120 through 127. -/
theorem p2CoreCheck015 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 15 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 15 ≤ p2CoreChunkBudget 15 := by decide +kernel

end Salem
