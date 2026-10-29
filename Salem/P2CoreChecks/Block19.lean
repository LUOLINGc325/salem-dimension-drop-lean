module

public import Salem.P2CoreChecks.Block18

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2432 through 2439. -/
theorem p2CoreCheck304 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 304 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 304 ≤ p2CoreChunkBudget 304 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2440 through 2447. -/
theorem p2CoreCheck305 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 305 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 305 ≤ p2CoreChunkBudget 305 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2448 through 2455. -/
theorem p2CoreCheck306 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 306 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 306 ≤ p2CoreChunkBudget 306 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2456 through 2463. -/
theorem p2CoreCheck307 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 307 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 307 ≤ p2CoreChunkBudget 307 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2464 through 2471. -/
theorem p2CoreCheck308 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 308 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 308 ≤ p2CoreChunkBudget 308 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2472 through 2479. -/
theorem p2CoreCheck309 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 309 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 309 ≤ p2CoreChunkBudget 309 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2480 through 2487. -/
theorem p2CoreCheck310 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 310 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 310 ≤ p2CoreChunkBudget 310 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2488 through 2495. -/
theorem p2CoreCheck311 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 311 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 311 ≤ p2CoreChunkBudget 311 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2496 through 2503. -/
theorem p2CoreCheck312 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 312 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 312 ≤ p2CoreChunkBudget 312 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2504 through 2511. -/
theorem p2CoreCheck313 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 313 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 313 ≤ p2CoreChunkBudget 313 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2512 through 2519. -/
theorem p2CoreCheck314 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 314 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 314 ≤ p2CoreChunkBudget 314 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2520 through 2527. -/
theorem p2CoreCheck315 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 315 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 315 ≤ p2CoreChunkBudget 315 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2528 through 2535. -/
theorem p2CoreCheck316 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 316 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 316 ≤ p2CoreChunkBudget 316 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2536 through 2543. -/
theorem p2CoreCheck317 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 317 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 317 ≤ p2CoreChunkBudget 317 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2544 through 2551. -/
theorem p2CoreCheck318 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 318 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 318 ≤ p2CoreChunkBudget 318 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2552 through 2559. -/
theorem p2CoreCheck319 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 319 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 319 ≤ p2CoreChunkBudget 319 := by decide +kernel

end Salem
