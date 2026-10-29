module

public import Salem.P2CoreData

@[expose] public section

namespace Salem

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The explicit, common-denominator chunk budgets sum to less than 23.715. -/
theorem p2CoreChunkBudget_total :
    ((List.range 361).map p2CoreChunkBudget).sum = 23712521 := by decide +kernel

end Salem
