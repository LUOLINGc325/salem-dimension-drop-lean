module

public import Salem.P2CoreChecks.Block12

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1664 through 1671. -/
theorem p2CoreCheck208 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 208 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 208 ≤ p2CoreChunkBudget 208 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1672 through 1679. -/
theorem p2CoreCheck209 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 209 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 209 ≤ p2CoreChunkBudget 209 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1680 through 1687. -/
theorem p2CoreCheck210 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 210 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 210 ≤ p2CoreChunkBudget 210 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1688 through 1695. -/
theorem p2CoreCheck211 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 211 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 211 ≤ p2CoreChunkBudget 211 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1696 through 1703. -/
theorem p2CoreCheck212 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 212 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 212 ≤ p2CoreChunkBudget 212 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1704 through 1711. -/
theorem p2CoreCheck213 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 213 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 213 ≤ p2CoreChunkBudget 213 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1712 through 1719. -/
theorem p2CoreCheck214 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 214 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 214 ≤ p2CoreChunkBudget 214 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1720 through 1727. -/
theorem p2CoreCheck215 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 215 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 215 ≤ p2CoreChunkBudget 215 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1728 through 1735. -/
theorem p2CoreCheck216 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 216 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 216 ≤ p2CoreChunkBudget 216 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1736 through 1743. -/
theorem p2CoreCheck217 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 217 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 217 ≤ p2CoreChunkBudget 217 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1744 through 1751. -/
theorem p2CoreCheck218 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 218 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 218 ≤ p2CoreChunkBudget 218 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1752 through 1759. -/
theorem p2CoreCheck219 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 219 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 219 ≤ p2CoreChunkBudget 219 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1760 through 1767. -/
theorem p2CoreCheck220 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 220 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 220 ≤ p2CoreChunkBudget 220 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1768 through 1775. -/
theorem p2CoreCheck221 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 221 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 221 ≤ p2CoreChunkBudget 221 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1776 through 1783. -/
theorem p2CoreCheck222 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 222 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 222 ≤ p2CoreChunkBudget 222 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1784 through 1791. -/
theorem p2CoreCheck223 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 223 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 223 ≤ p2CoreChunkBudget 223 := by decide +kernel

end Salem
