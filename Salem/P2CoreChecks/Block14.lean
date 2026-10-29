module

public import Salem.P2CoreChecks.Block13

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1792 through 1799. -/
theorem p2CoreCheck224 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 224 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 224 ≤ p2CoreChunkBudget 224 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1800 through 1807. -/
theorem p2CoreCheck225 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 225 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 225 ≤ p2CoreChunkBudget 225 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1808 through 1815. -/
theorem p2CoreCheck226 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 226 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 226 ≤ p2CoreChunkBudget 226 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1816 through 1823. -/
theorem p2CoreCheck227 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 227 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 227 ≤ p2CoreChunkBudget 227 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1824 through 1831. -/
theorem p2CoreCheck228 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 228 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 228 ≤ p2CoreChunkBudget 228 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1832 through 1839. -/
theorem p2CoreCheck229 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 229 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 229 ≤ p2CoreChunkBudget 229 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1840 through 1847. -/
theorem p2CoreCheck230 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 230 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 230 ≤ p2CoreChunkBudget 230 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1848 through 1855. -/
theorem p2CoreCheck231 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 231 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 231 ≤ p2CoreChunkBudget 231 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1856 through 1863. -/
theorem p2CoreCheck232 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 232 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 232 ≤ p2CoreChunkBudget 232 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1864 through 1871. -/
theorem p2CoreCheck233 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 233 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 233 ≤ p2CoreChunkBudget 233 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1872 through 1879. -/
theorem p2CoreCheck234 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 234 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 234 ≤ p2CoreChunkBudget 234 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1880 through 1887. -/
theorem p2CoreCheck235 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 235 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 235 ≤ p2CoreChunkBudget 235 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1888 through 1895. -/
theorem p2CoreCheck236 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 236 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 236 ≤ p2CoreChunkBudget 236 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1896 through 1903. -/
theorem p2CoreCheck237 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 237 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 237 ≤ p2CoreChunkBudget 237 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1904 through 1911. -/
theorem p2CoreCheck238 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 238 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 238 ≤ p2CoreChunkBudget 238 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1912 through 1919. -/
theorem p2CoreCheck239 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 239 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 239 ≤ p2CoreChunkBudget 239 := by decide +kernel

end Salem
