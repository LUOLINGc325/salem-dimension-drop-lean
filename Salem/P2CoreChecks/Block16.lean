module

public import Salem.P2CoreChecks.Block15

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 2048 through 2055. -/
theorem p2CoreCheck256 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 256 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 256 ≤ p2CoreChunkBudget 256 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2056 through 2063. -/
theorem p2CoreCheck257 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 257 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 257 ≤ p2CoreChunkBudget 257 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2064 through 2071. -/
theorem p2CoreCheck258 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 258 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 258 ≤ p2CoreChunkBudget 258 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2072 through 2079. -/
theorem p2CoreCheck259 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 259 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 259 ≤ p2CoreChunkBudget 259 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2080 through 2087. -/
theorem p2CoreCheck260 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 260 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 260 ≤ p2CoreChunkBudget 260 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2088 through 2095. -/
theorem p2CoreCheck261 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 261 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 261 ≤ p2CoreChunkBudget 261 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2096 through 2103. -/
theorem p2CoreCheck262 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 262 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 262 ≤ p2CoreChunkBudget 262 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2104 through 2111. -/
theorem p2CoreCheck263 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 263 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 263 ≤ p2CoreChunkBudget 263 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2112 through 2119. -/
theorem p2CoreCheck264 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 264 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 264 ≤ p2CoreChunkBudget 264 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2120 through 2127. -/
theorem p2CoreCheck265 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 265 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 265 ≤ p2CoreChunkBudget 265 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2128 through 2135. -/
theorem p2CoreCheck266 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 266 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 266 ≤ p2CoreChunkBudget 266 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2136 through 2143. -/
theorem p2CoreCheck267 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 267 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 267 ≤ p2CoreChunkBudget 267 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2144 through 2151. -/
theorem p2CoreCheck268 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 268 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 268 ≤ p2CoreChunkBudget 268 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2152 through 2159. -/
theorem p2CoreCheck269 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 269 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 269 ≤ p2CoreChunkBudget 269 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2160 through 2167. -/
theorem p2CoreCheck270 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 270 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 270 ≤ p2CoreChunkBudget 270 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 2168 through 2175. -/
theorem p2CoreCheck271 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 271 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 271 ≤ p2CoreChunkBudget 271 := by decide +kernel

end Salem
