module

public import Salem.P2CoreChecks.Block07

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1024 through 1031. -/
theorem p2CoreCheck128 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 128 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 128 ≤ p2CoreChunkBudget 128 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1032 through 1039. -/
theorem p2CoreCheck129 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 129 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 129 ≤ p2CoreChunkBudget 129 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1040 through 1047. -/
theorem p2CoreCheck130 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 130 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 130 ≤ p2CoreChunkBudget 130 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1048 through 1055. -/
theorem p2CoreCheck131 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 131 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 131 ≤ p2CoreChunkBudget 131 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1056 through 1063. -/
theorem p2CoreCheck132 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 132 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 132 ≤ p2CoreChunkBudget 132 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1064 through 1071. -/
theorem p2CoreCheck133 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 133 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 133 ≤ p2CoreChunkBudget 133 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1072 through 1079. -/
theorem p2CoreCheck134 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 134 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 134 ≤ p2CoreChunkBudget 134 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1080 through 1087. -/
theorem p2CoreCheck135 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 135 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 135 ≤ p2CoreChunkBudget 135 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1088 through 1095. -/
theorem p2CoreCheck136 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 136 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 136 ≤ p2CoreChunkBudget 136 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1096 through 1103. -/
theorem p2CoreCheck137 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 137 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 137 ≤ p2CoreChunkBudget 137 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1104 through 1111. -/
theorem p2CoreCheck138 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 138 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 138 ≤ p2CoreChunkBudget 138 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1112 through 1119. -/
theorem p2CoreCheck139 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 139 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 139 ≤ p2CoreChunkBudget 139 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1120 through 1127. -/
theorem p2CoreCheck140 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 140 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 140 ≤ p2CoreChunkBudget 140 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1128 through 1135. -/
theorem p2CoreCheck141 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 141 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 141 ≤ p2CoreChunkBudget 141 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1136 through 1143. -/
theorem p2CoreCheck142 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 142 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 142 ≤ p2CoreChunkBudget 142 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1144 through 1151. -/
theorem p2CoreCheck143 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 143 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 143 ≤ p2CoreChunkBudget 143 := by decide +kernel

end Salem
