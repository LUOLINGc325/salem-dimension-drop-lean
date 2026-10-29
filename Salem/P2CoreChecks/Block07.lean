module

public import Salem.P2CoreChecks.Block06

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 896 through 903. -/
theorem p2CoreCheck112 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 112 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 112 ≤ p2CoreChunkBudget 112 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 904 through 911. -/
theorem p2CoreCheck113 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 113 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 113 ≤ p2CoreChunkBudget 113 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 912 through 919. -/
theorem p2CoreCheck114 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 114 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 114 ≤ p2CoreChunkBudget 114 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 920 through 927. -/
theorem p2CoreCheck115 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 115 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 115 ≤ p2CoreChunkBudget 115 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 928 through 935. -/
theorem p2CoreCheck116 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 116 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 116 ≤ p2CoreChunkBudget 116 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 936 through 943. -/
theorem p2CoreCheck117 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 117 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 117 ≤ p2CoreChunkBudget 117 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 944 through 951. -/
theorem p2CoreCheck118 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 118 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 118 ≤ p2CoreChunkBudget 118 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 952 through 959. -/
theorem p2CoreCheck119 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 119 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 119 ≤ p2CoreChunkBudget 119 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 960 through 967. -/
theorem p2CoreCheck120 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 120 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 120 ≤ p2CoreChunkBudget 120 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 968 through 975. -/
theorem p2CoreCheck121 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 121 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 121 ≤ p2CoreChunkBudget 121 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 976 through 983. -/
theorem p2CoreCheck122 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 122 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 122 ≤ p2CoreChunkBudget 122 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 984 through 991. -/
theorem p2CoreCheck123 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 123 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 123 ≤ p2CoreChunkBudget 123 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 992 through 999. -/
theorem p2CoreCheck124 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 124 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 124 ≤ p2CoreChunkBudget 124 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1000 through 1007. -/
theorem p2CoreCheck125 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 125 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 125 ≤ p2CoreChunkBudget 125 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1008 through 1015. -/
theorem p2CoreCheck126 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 126 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 126 ≤ p2CoreChunkBudget 126 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1016 through 1023. -/
theorem p2CoreCheck127 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 127 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 127 ≤ p2CoreChunkBudget 127 := by decide +kernel

end Salem
