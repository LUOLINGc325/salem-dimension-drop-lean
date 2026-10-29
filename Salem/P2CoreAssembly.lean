module

public import Salem.P2FastEvaluation
public import Salem.RationalPotential
public import Salem.P2CoreBudgetTotal
@[expose] public section

namespace Salem
open scoped BigOperators
set_option maxHeartbeats 1000000

private lemma p2Core_list_range_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.sum_range_succ, Finset.sum_range_succ, ih]

private lemma p2Core_sum_range_blocks (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range (8*n), f i) =
      ∑ k ∈ Finset.range n, ((List.range 8).map fun j => f (8*k+j)).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    congr 1

lemma p2Core_ticks_total_of_checks (hchecks : ∀ k : Fin 361,
    (∀ j : Fin 8, p2CoreRadiusAt (8 * k.val + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks k.val ≤ p2CoreChunkBudget k.val) :
    ∑ j ∈ Finset.range 2885, p2CorePotentialTicks j ≤ 23712521 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (8*361), p2CorePotentialTicks j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by decide))
      intro i hi hni
      exact Nat.zero_le _
    _ = ∑ k ∈ Finset.range 361, p2CoreChunkTicks k := p2Core_sum_range_blocks _ _
    _ ≤ ∑ k ∈ Finset.range 361, p2CoreChunkBudget k := by
      apply Finset.sum_le_sum
      intro k hk
      exact (hchecks ⟨k, Finset.mem_range.1 hk⟩).2
    _ = _ := by rw [← p2Core_list_range_sum, p2CoreChunkBudget_total]

lemma p2Core_potential_le_ticks (i : Fin 2885)
    (hi : p2GreenFastCoreRadius i ≤ (2 / 5 : ℚ)) :
    cosinePotential (p2GreenSeedCoordinate (i.val : ℤ)) ≤
      (p2CorePotentialTicks i.val : ℝ) / 1000000 := by
  have hnonneg := p2GreenFastCoreRadius_nonneg i
  have ht := p2GreenFastCoreCoordinate_abs_le i
  have h := cosinePotential_le_radiusPotentialBound
    (show (0 : ℝ) ≤ p2GreenFastCoreRadius i by exact_mod_cast hnonneg)
    (show (p2GreenFastCoreRadius i : ℝ) ≤ 43/100 by
      have hh : (p2GreenFastCoreRadius i : ℝ) ≤ ((2/5:ℚ):ℝ) := Rat.cast_le.2 hi
      norm_num at hh
      linarith)
    ht (p2CorePotentialTerms i.val)
  rw [← rationalRadiusPotentialBound_cast] at h
  have hceil : rationalRadiusPotentialBound (p2GreenFastCoreRadius i) (p2CorePotentialTerms i.val) ≤
      (p2CorePotentialTicks i.val : ℚ) / 1000000 := by
    apply (le_div_iff₀ (by norm_num : (0:ℚ)<1000000)).2
    simpa [p2CorePotentialTicks, p2CoreRadiusAt, i.isLt] using
      (Nat.le_ceil (rationalRadiusPotentialBound (p2GreenFastCoreRadius i)
        (p2CorePotentialTerms i.val) * 1000000))
  have hc : (rationalRadiusPotentialBound (p2GreenFastCoreRadius i) (p2CorePotentialTerms i.val) : ℝ) ≤
      (((p2CorePotentialTicks i.val : ℚ) / 1000000 : ℚ) : ℝ) := Rat.cast_le.2 hceil
  push_cast at hc
  exact h.trans hc

lemma p2Core_radius_le_of_checks (hchecks : ∀ k : Fin 361,
    (∀ j : Fin 8, p2CoreRadiusAt (8 * k.val + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks k.val ≤ p2CoreChunkBudget k.val) :
    ∀ i : Fin 2885, p2GreenFastCoreRadius i ≤ (2 / 5 : ℚ) := by
  intro i
  have hk : i.val / 8 < 361 := by omega
  have hj : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
  have h := (hchecks ⟨i.val/8,hk⟩).1 ⟨i.val%8,hj⟩
  have heq : 8 * (i.val/8) + i.val%8 = i.val := by omega
  simpa only [heq, p2CoreRadiusAt, dite_eq_left i.isLt] using h

/-- Converting the integer block checks to the actual real action uses only the
proved interval enclosure and the cosine/logarithm majorant. -/
theorem p2Core_action_le_of_checks (hchecks : ∀ k : Fin 361,
    (∀ j : Fin 8, p2CoreRadiusAt (8 * k.val + j.val) ≤ (2 / 5 : ℚ)) ∧
      p2CoreChunkTicks k.val ≤ p2CoreChunkBudget k.val) :
    (∑ i : Fin 2885, cosinePotential (p2GreenSeedCoordinate (i.val : ℤ))) ≤
      (23712521 / 1000000 : ℝ) := by
  have hrad := p2Core_radius_le_of_checks hchecks
  have htotal := p2Core_ticks_total_of_checks hchecks
  calc
    _ ≤ ∑ i : Fin 2885, (p2CorePotentialTicks i.val : ℝ) / 1000000 := by
      apply Finset.sum_le_sum
      intro i hi
      exact p2Core_potential_le_ticks i (hrad i)
    _ = ((∑ i : Fin 2885, p2CorePotentialTicks i.val : ℕ) : ℝ) / 1000000 := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ = ((∑ i ∈ Finset.range 2885, p2CorePotentialTicks i : ℕ) : ℝ) / 1000000 := by
      rw [Fin.sum_univ_eq_sum_range]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast htotal

end Salem
