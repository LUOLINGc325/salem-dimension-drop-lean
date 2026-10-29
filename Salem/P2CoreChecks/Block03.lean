module

public import Salem.P2CoreChecks.Block02

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 384 through 391. -/
theorem p2CoreCheck048 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 48 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 48 ≤ p2CoreChunkBudget 48 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 392 through 399. -/
theorem p2CoreCheck049 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 49 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 49 ≤ p2CoreChunkBudget 49 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 400 through 407. -/
theorem p2CoreCheck050 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 50 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 50 ≤ p2CoreChunkBudget 50 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 408 through 415. -/
theorem p2CoreCheck051 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 51 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 51 ≤ p2CoreChunkBudget 51 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 416 through 423. -/
theorem p2CoreCheck052 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 52 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 52 ≤ p2CoreChunkBudget 52 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 424 through 431. -/
theorem p2CoreCheck053 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 53 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 53 ≤ p2CoreChunkBudget 53 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 432 through 439. -/
theorem p2CoreCheck054 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 54 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 54 ≤ p2CoreChunkBudget 54 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 440 through 447. -/
theorem p2CoreCheck055 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 55 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 55 ≤ p2CoreChunkBudget 55 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 448 through 455. -/
theorem p2CoreCheck056 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 56 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 56 ≤ p2CoreChunkBudget 56 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 456 through 463. -/
theorem p2CoreCheck057 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 57 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 57 ≤ p2CoreChunkBudget 57 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 464 through 471. -/
theorem p2CoreCheck058 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 58 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 58 ≤ p2CoreChunkBudget 58 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 472 through 479. -/
theorem p2CoreCheck059 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 59 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 59 ≤ p2CoreChunkBudget 59 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 480 through 487. -/
theorem p2CoreCheck060 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 60 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 60 ≤ p2CoreChunkBudget 60 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 488 through 495. -/
theorem p2CoreCheck061 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 61 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 61 ≤ p2CoreChunkBudget 61 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 496 through 503. -/
theorem p2CoreCheck062 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 62 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 62 ≤ p2CoreChunkBudget 62 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 504 through 511. -/
theorem p2CoreCheck063 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 63 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 63 ≤ p2CoreChunkBudget 63 := by decide +kernel

end Salem
