module

public import Salem.P2CoreChecks.Block11

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1536 through 1543. -/
theorem p2CoreCheck192 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 192 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 192 ≤ p2CoreChunkBudget 192 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1544 through 1551. -/
theorem p2CoreCheck193 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 193 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 193 ≤ p2CoreChunkBudget 193 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1552 through 1559. -/
theorem p2CoreCheck194 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 194 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 194 ≤ p2CoreChunkBudget 194 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1560 through 1567. -/
theorem p2CoreCheck195 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 195 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 195 ≤ p2CoreChunkBudget 195 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1568 through 1575. -/
theorem p2CoreCheck196 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 196 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 196 ≤ p2CoreChunkBudget 196 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1576 through 1583. -/
theorem p2CoreCheck197 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 197 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 197 ≤ p2CoreChunkBudget 197 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1584 through 1591. -/
theorem p2CoreCheck198 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 198 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 198 ≤ p2CoreChunkBudget 198 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1592 through 1599. -/
theorem p2CoreCheck199 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 199 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 199 ≤ p2CoreChunkBudget 199 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1600 through 1607. -/
theorem p2CoreCheck200 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 200 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 200 ≤ p2CoreChunkBudget 200 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1608 through 1615. -/
theorem p2CoreCheck201 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 201 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 201 ≤ p2CoreChunkBudget 201 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1616 through 1623. -/
theorem p2CoreCheck202 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 202 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 202 ≤ p2CoreChunkBudget 202 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1624 through 1631. -/
theorem p2CoreCheck203 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 203 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 203 ≤ p2CoreChunkBudget 203 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1632 through 1639. -/
theorem p2CoreCheck204 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 204 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 204 ≤ p2CoreChunkBudget 204 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1640 through 1647. -/
theorem p2CoreCheck205 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 205 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 205 ≤ p2CoreChunkBudget 205 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1648 through 1655. -/
theorem p2CoreCheck206 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 206 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 206 ≤ p2CoreChunkBudget 206 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1656 through 1663. -/
theorem p2CoreCheck207 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 207 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 207 ≤ p2CoreChunkBudget 207 := by decide +kernel

end Salem
