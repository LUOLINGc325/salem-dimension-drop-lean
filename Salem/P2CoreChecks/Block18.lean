module

public import Salem.P2CoreChecks.Block17

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2304 through 2311. -/
theorem p2CoreCheck288 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 288 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 288 ≤ p2CoreChunkBudget 288 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2312 through 2319. -/
theorem p2CoreCheck289 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 289 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 289 ≤ p2CoreChunkBudget 289 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2320 through 2327. -/
theorem p2CoreCheck290 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 290 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 290 ≤ p2CoreChunkBudget 290 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2328 through 2335. -/
theorem p2CoreCheck291 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 291 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 291 ≤ p2CoreChunkBudget 291 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2336 through 2343. -/
theorem p2CoreCheck292 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 292 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 292 ≤ p2CoreChunkBudget 292 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2344 through 2351. -/
theorem p2CoreCheck293 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 293 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 293 ≤ p2CoreChunkBudget 293 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2352 through 2359. -/
theorem p2CoreCheck294 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 294 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 294 ≤ p2CoreChunkBudget 294 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2360 through 2367. -/
theorem p2CoreCheck295 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 295 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 295 ≤ p2CoreChunkBudget 295 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2368 through 2375. -/
theorem p2CoreCheck296 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 296 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 296 ≤ p2CoreChunkBudget 296 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2376 through 2383. -/
theorem p2CoreCheck297 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 297 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 297 ≤ p2CoreChunkBudget 297 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2384 through 2391. -/
theorem p2CoreCheck298 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 298 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 298 ≤ p2CoreChunkBudget 298 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2392 through 2399. -/
theorem p2CoreCheck299 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 299 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 299 ≤ p2CoreChunkBudget 299 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2400 through 2407. -/
theorem p2CoreCheck300 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 300 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 300 ≤ p2CoreChunkBudget 300 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2408 through 2415. -/
theorem p2CoreCheck301 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 301 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 301 ≤ p2CoreChunkBudget 301 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2416 through 2423. -/
theorem p2CoreCheck302 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 302 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 302 ≤ p2CoreChunkBudget 302 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2424 through 2431. -/
theorem p2CoreCheck303 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 303 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 303 ≤ p2CoreChunkBudget 303 := by decide +kernel

end Salem
