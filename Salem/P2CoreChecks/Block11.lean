module

public import Salem.P2CoreChecks.Block10

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1408 through 1415. -/
theorem p2CoreCheck176 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 176 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 176 ≤ p2CoreChunkBudget 176 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1416 through 1423. -/
theorem p2CoreCheck177 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 177 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 177 ≤ p2CoreChunkBudget 177 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1424 through 1431. -/
theorem p2CoreCheck178 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 178 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 178 ≤ p2CoreChunkBudget 178 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1432 through 1439. -/
theorem p2CoreCheck179 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 179 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 179 ≤ p2CoreChunkBudget 179 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1440 through 1447. -/
theorem p2CoreCheck180 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 180 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 180 ≤ p2CoreChunkBudget 180 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1448 through 1455. -/
theorem p2CoreCheck181 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 181 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 181 ≤ p2CoreChunkBudget 181 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1456 through 1463. -/
theorem p2CoreCheck182 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 182 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 182 ≤ p2CoreChunkBudget 182 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1464 through 1471. -/
theorem p2CoreCheck183 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 183 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 183 ≤ p2CoreChunkBudget 183 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1472 through 1479. -/
theorem p2CoreCheck184 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 184 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 184 ≤ p2CoreChunkBudget 184 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1480 through 1487. -/
theorem p2CoreCheck185 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 185 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 185 ≤ p2CoreChunkBudget 185 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1488 through 1495. -/
theorem p2CoreCheck186 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 186 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 186 ≤ p2CoreChunkBudget 186 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1496 through 1503. -/
theorem p2CoreCheck187 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 187 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 187 ≤ p2CoreChunkBudget 187 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1504 through 1511. -/
theorem p2CoreCheck188 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 188 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 188 ≤ p2CoreChunkBudget 188 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1512 through 1519. -/
theorem p2CoreCheck189 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 189 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 189 ≤ p2CoreChunkBudget 189 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1520 through 1527. -/
theorem p2CoreCheck190 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 190 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 190 ≤ p2CoreChunkBudget 190 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1528 through 1535. -/
theorem p2CoreCheck191 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 191 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 191 ≤ p2CoreChunkBudget 191 := by decide +kernel

end Salem
