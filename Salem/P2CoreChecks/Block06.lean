module

public import Salem.P2CoreChecks.Block05

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Kernel-checked radii and total potential budget for cells 768 through 775. -/
theorem p2CoreCheck096 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 96 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 96 ≤ p2CoreChunkBudget 96 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 776 through 783. -/
theorem p2CoreCheck097 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 97 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 97 ≤ p2CoreChunkBudget 97 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 784 through 791. -/
theorem p2CoreCheck098 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 98 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 98 ≤ p2CoreChunkBudget 98 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 792 through 799. -/
theorem p2CoreCheck099 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 99 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 99 ≤ p2CoreChunkBudget 99 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 800 through 807. -/
theorem p2CoreCheck100 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 100 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 100 ≤ p2CoreChunkBudget 100 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 808 through 815. -/
theorem p2CoreCheck101 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 101 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 101 ≤ p2CoreChunkBudget 101 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 816 through 823. -/
theorem p2CoreCheck102 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 102 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 102 ≤ p2CoreChunkBudget 102 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 824 through 831. -/
theorem p2CoreCheck103 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 103 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 103 ≤ p2CoreChunkBudget 103 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 832 through 839. -/
theorem p2CoreCheck104 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 104 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 104 ≤ p2CoreChunkBudget 104 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 840 through 847. -/
theorem p2CoreCheck105 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 105 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 105 ≤ p2CoreChunkBudget 105 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 848 through 855. -/
theorem p2CoreCheck106 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 106 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 106 ≤ p2CoreChunkBudget 106 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 856 through 863. -/
theorem p2CoreCheck107 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 107 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 107 ≤ p2CoreChunkBudget 107 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 864 through 871. -/
theorem p2CoreCheck108 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 108 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 108 ≤ p2CoreChunkBudget 108 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 872 through 879. -/
theorem p2CoreCheck109 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 109 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 109 ≤ p2CoreChunkBudget 109 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 880 through 887. -/
theorem p2CoreCheck110 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 110 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 110 ≤ p2CoreChunkBudget 110 := by decide +kernel

/-- Kernel-checked radii and total potential budget for cells 888 through 895. -/
theorem p2CoreCheck111 :
    (∀ j : Fin 8, p2CoreRadiusAt (8 * 111 + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks 111 ≤ p2CoreChunkBudget 111 := by decide +kernel

end Salem
