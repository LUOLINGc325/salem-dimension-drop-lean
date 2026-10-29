module

public import Salem.P2CoreChecks.Block09

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1280 through 1287. -/
theorem p2CoreCheck160 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 160 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 160 ≤ p2CoreChunkBudget 160 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1288 through 1295. -/
theorem p2CoreCheck161 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 161 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 161 ≤ p2CoreChunkBudget 161 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1296 through 1303. -/
theorem p2CoreCheck162 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 162 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 162 ≤ p2CoreChunkBudget 162 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1304 through 1311. -/
theorem p2CoreCheck163 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 163 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 163 ≤ p2CoreChunkBudget 163 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1312 through 1319. -/
theorem p2CoreCheck164 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 164 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 164 ≤ p2CoreChunkBudget 164 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1320 through 1327. -/
theorem p2CoreCheck165 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 165 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 165 ≤ p2CoreChunkBudget 165 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1328 through 1335. -/
theorem p2CoreCheck166 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 166 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 166 ≤ p2CoreChunkBudget 166 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1336 through 1343. -/
theorem p2CoreCheck167 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 167 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 167 ≤ p2CoreChunkBudget 167 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1344 through 1351. -/
theorem p2CoreCheck168 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 168 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 168 ≤ p2CoreChunkBudget 168 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1352 through 1359. -/
theorem p2CoreCheck169 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 169 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 169 ≤ p2CoreChunkBudget 169 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1360 through 1367. -/
theorem p2CoreCheck170 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 170 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 170 ≤ p2CoreChunkBudget 170 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1368 through 1375. -/
theorem p2CoreCheck171 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 171 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 171 ≤ p2CoreChunkBudget 171 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1376 through 1383. -/
theorem p2CoreCheck172 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 172 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 172 ≤ p2CoreChunkBudget 172 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1384 through 1391. -/
theorem p2CoreCheck173 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 173 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 173 ≤ p2CoreChunkBudget 173 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1392 through 1399. -/
theorem p2CoreCheck174 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 174 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 174 ≤ p2CoreChunkBudget 174 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1400 through 1407. -/
theorem p2CoreCheck175 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 175 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 175 ≤ p2CoreChunkBudget 175 := by decide +kernel

end Salem
