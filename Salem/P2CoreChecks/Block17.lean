module

public import Salem.P2CoreChecks.Block16

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2176 through 2183. -/
theorem p2CoreCheck272 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 272 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 272 ≤ p2CoreChunkBudget 272 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2184 through 2191. -/
theorem p2CoreCheck273 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 273 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 273 ≤ p2CoreChunkBudget 273 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2192 through 2199. -/
theorem p2CoreCheck274 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 274 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 274 ≤ p2CoreChunkBudget 274 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2200 through 2207. -/
theorem p2CoreCheck275 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 275 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 275 ≤ p2CoreChunkBudget 275 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2208 through 2215. -/
theorem p2CoreCheck276 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 276 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 276 ≤ p2CoreChunkBudget 276 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2216 through 2223. -/
theorem p2CoreCheck277 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 277 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 277 ≤ p2CoreChunkBudget 277 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2224 through 2231. -/
theorem p2CoreCheck278 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 278 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 278 ≤ p2CoreChunkBudget 278 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2232 through 2239. -/
theorem p2CoreCheck279 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 279 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 279 ≤ p2CoreChunkBudget 279 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2240 through 2247. -/
theorem p2CoreCheck280 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 280 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 280 ≤ p2CoreChunkBudget 280 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2248 through 2255. -/
theorem p2CoreCheck281 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 281 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 281 ≤ p2CoreChunkBudget 281 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2256 through 2263. -/
theorem p2CoreCheck282 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 282 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 282 ≤ p2CoreChunkBudget 282 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2264 through 2271. -/
theorem p2CoreCheck283 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 283 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 283 ≤ p2CoreChunkBudget 283 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2272 through 2279. -/
theorem p2CoreCheck284 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 284 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 284 ≤ p2CoreChunkBudget 284 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2280 through 2287. -/
theorem p2CoreCheck285 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 285 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 285 ≤ p2CoreChunkBudget 285 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2288 through 2295. -/
theorem p2CoreCheck286 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 286 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 286 ≤ p2CoreChunkBudget 286 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2296 through 2303. -/
theorem p2CoreCheck287 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 287 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 287 ≤ p2CoreChunkBudget 287 := by decide +kernel

end Salem
