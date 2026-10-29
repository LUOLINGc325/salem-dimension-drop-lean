module

public import Salem.P2CoreChecks.Block08

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 1152 through 1159. -/
theorem p2CoreCheck144 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 144 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 144 ≤ p2CoreChunkBudget 144 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1160 through 1167. -/
theorem p2CoreCheck145 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 145 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 145 ≤ p2CoreChunkBudget 145 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1168 through 1175. -/
theorem p2CoreCheck146 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 146 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 146 ≤ p2CoreChunkBudget 146 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1176 through 1183. -/
theorem p2CoreCheck147 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 147 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 147 ≤ p2CoreChunkBudget 147 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1184 through 1191. -/
theorem p2CoreCheck148 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 148 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 148 ≤ p2CoreChunkBudget 148 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1192 through 1199. -/
theorem p2CoreCheck149 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 149 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 149 ≤ p2CoreChunkBudget 149 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1200 through 1207. -/
theorem p2CoreCheck150 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 150 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 150 ≤ p2CoreChunkBudget 150 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1208 through 1215. -/
theorem p2CoreCheck151 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 151 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 151 ≤ p2CoreChunkBudget 151 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1216 through 1223. -/
theorem p2CoreCheck152 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 152 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 152 ≤ p2CoreChunkBudget 152 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1224 through 1231. -/
theorem p2CoreCheck153 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 153 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 153 ≤ p2CoreChunkBudget 153 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1232 through 1239. -/
theorem p2CoreCheck154 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 154 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 154 ≤ p2CoreChunkBudget 154 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1240 through 1247. -/
theorem p2CoreCheck155 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 155 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 155 ≤ p2CoreChunkBudget 155 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1248 through 1255. -/
theorem p2CoreCheck156 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 156 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 156 ≤ p2CoreChunkBudget 156 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1256 through 1263. -/
theorem p2CoreCheck157 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 157 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 157 ≤ p2CoreChunkBudget 157 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1264 through 1271. -/
theorem p2CoreCheck158 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 158 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 158 ≤ p2CoreChunkBudget 158 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 1272 through 1279. -/
theorem p2CoreCheck159 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 159 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 159 ≤ p2CoreChunkBudget 159 := by decide +kernel

end Salem
