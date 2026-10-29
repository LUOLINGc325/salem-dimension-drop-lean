module

public import Salem.P2CoreChecks.Block14

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1920 through 1927. -/
theorem p2CoreCheck240 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 240 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 240 ≤ p2CoreChunkBudget 240 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1928 through 1935. -/
theorem p2CoreCheck241 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 241 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 241 ≤ p2CoreChunkBudget 241 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1936 through 1943. -/
theorem p2CoreCheck242 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 242 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 242 ≤ p2CoreChunkBudget 242 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1944 through 1951. -/
theorem p2CoreCheck243 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 243 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 243 ≤ p2CoreChunkBudget 243 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1952 through 1959. -/
theorem p2CoreCheck244 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 244 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 244 ≤ p2CoreChunkBudget 244 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1960 through 1967. -/
theorem p2CoreCheck245 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 245 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 245 ≤ p2CoreChunkBudget 245 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1968 through 1975. -/
theorem p2CoreCheck246 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 246 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 246 ≤ p2CoreChunkBudget 246 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1976 through 1983. -/
theorem p2CoreCheck247 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 247 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 247 ≤ p2CoreChunkBudget 247 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1984 through 1991. -/
theorem p2CoreCheck248 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 248 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 248 ≤ p2CoreChunkBudget 248 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1992 through 1999. -/
theorem p2CoreCheck249 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 249 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 249 ≤ p2CoreChunkBudget 249 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2000 through 2007. -/
theorem p2CoreCheck250 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 250 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 250 ≤ p2CoreChunkBudget 250 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2008 through 2015. -/
theorem p2CoreCheck251 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 251 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 251 ≤ p2CoreChunkBudget 251 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2016 through 2023. -/
theorem p2CoreCheck252 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 252 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 252 ≤ p2CoreChunkBudget 252 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2024 through 2031. -/
theorem p2CoreCheck253 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 253 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 253 ≤ p2CoreChunkBudget 253 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2032 through 2039. -/
theorem p2CoreCheck254 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 254 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 254 ≤ p2CoreChunkBudget 254 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2040 through 2047. -/
theorem p2CoreCheck255 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 255 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 255 ≤ p2CoreChunkBudget 255 := by decide +kernel

end Salem
