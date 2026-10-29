module

public import Salem.P2CoreChecks.Block00

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 128 through 135. -/
theorem p2CoreCheck016 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 16 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 16 ≤ p2CoreChunkBudget 16 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 136 through 143. -/
theorem p2CoreCheck017 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 17 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 17 ≤ p2CoreChunkBudget 17 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 144 through 151. -/
theorem p2CoreCheck018 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 18 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 18 ≤ p2CoreChunkBudget 18 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 152 through 159. -/
theorem p2CoreCheck019 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 19 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 19 ≤ p2CoreChunkBudget 19 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 160 through 167. -/
theorem p2CoreCheck020 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 20 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 20 ≤ p2CoreChunkBudget 20 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 168 through 175. -/
theorem p2CoreCheck021 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 21 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 21 ≤ p2CoreChunkBudget 21 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 176 through 183. -/
theorem p2CoreCheck022 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 22 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 22 ≤ p2CoreChunkBudget 22 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 184 through 191. -/
theorem p2CoreCheck023 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 23 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 23 ≤ p2CoreChunkBudget 23 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 192 through 199. -/
theorem p2CoreCheck024 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 24 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 24 ≤ p2CoreChunkBudget 24 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 200 through 207. -/
theorem p2CoreCheck025 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 25 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 25 ≤ p2CoreChunkBudget 25 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 208 through 215. -/
theorem p2CoreCheck026 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 26 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 26 ≤ p2CoreChunkBudget 26 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 216 through 223. -/
theorem p2CoreCheck027 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 27 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 27 ≤ p2CoreChunkBudget 27 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 224 through 231. -/
theorem p2CoreCheck028 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 28 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 28 ≤ p2CoreChunkBudget 28 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 232 through 239. -/
theorem p2CoreCheck029 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 29 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 29 ≤ p2CoreChunkBudget 29 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 240 through 247. -/
theorem p2CoreCheck030 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 30 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 30 ≤ p2CoreChunkBudget 30 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 248 through 255. -/
theorem p2CoreCheck031 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 31 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 31 ≤ p2CoreChunkBudget 31 := by decide +kernel

end Salem
