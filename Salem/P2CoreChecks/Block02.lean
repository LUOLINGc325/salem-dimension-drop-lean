module

public import Salem.P2CoreChecks.Block01

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 256 through 263. -/
theorem p2CoreCheck032 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 32 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 32 ≤ p2CoreChunkBudget 32 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 264 through 271. -/
theorem p2CoreCheck033 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 33 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 33 ≤ p2CoreChunkBudget 33 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 272 through 279. -/
theorem p2CoreCheck034 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 34 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 34 ≤ p2CoreChunkBudget 34 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 280 through 287. -/
theorem p2CoreCheck035 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 35 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 35 ≤ p2CoreChunkBudget 35 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 288 through 295. -/
theorem p2CoreCheck036 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 36 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 36 ≤ p2CoreChunkBudget 36 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 296 through 303. -/
theorem p2CoreCheck037 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 37 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 37 ≤ p2CoreChunkBudget 37 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 304 through 311. -/
theorem p2CoreCheck038 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 38 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 38 ≤ p2CoreChunkBudget 38 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 312 through 319. -/
theorem p2CoreCheck039 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 39 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 39 ≤ p2CoreChunkBudget 39 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 320 through 327. -/
theorem p2CoreCheck040 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 40 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 40 ≤ p2CoreChunkBudget 40 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 328 through 335. -/
theorem p2CoreCheck041 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 41 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 41 ≤ p2CoreChunkBudget 41 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 336 through 343. -/
theorem p2CoreCheck042 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 42 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 42 ≤ p2CoreChunkBudget 42 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 344 through 351. -/
theorem p2CoreCheck043 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 43 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 43 ≤ p2CoreChunkBudget 43 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 352 through 359. -/
theorem p2CoreCheck044 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 44 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 44 ≤ p2CoreChunkBudget 44 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 360 through 367. -/
theorem p2CoreCheck045 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 45 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 45 ≤ p2CoreChunkBudget 45 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 368 through 375. -/
theorem p2CoreCheck046 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 46 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 46 ≤ p2CoreChunkBudget 46 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 376 through 383. -/
theorem p2CoreCheck047 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 47 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 47 ≤ p2CoreChunkBudget 47 := by decide +kernel

end Salem
