module

public import Mathlib

@[expose] public section

open scoped BigOperators

namespace Salem

/-- Shannon entropy in nats of an explicitly given finite probability vector.
Zero masses contribute zero. For a random variable, apply this to its merged atom masses. -/
noncomputable def finiteEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Nonnegativity of finite relative entropy, in the cross-entropy form used in
v2 Lemma `lem:entropy`. The source law may have zero masses; the comparison law
has positive masses on every indexed atom. -/
theorem finiteEntropy_le_crossEntropy {ι : Type*} [Fintype ι]
    {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    finiteEntropy p ≤ ∑ i, -p i * Real.log (q i) := by
  have hterm (i : ι) : Real.negMulLog (p i) ≤
      -p i * Real.log (q i) + q i - p i := by
    rcases (hp i).eq_or_lt with hzero | hpos
    · simp only [← hzero, Real.negMulLog_zero, neg_zero, zero_mul, zero_add, sub_zero]
      exact (hq i).le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (hq i) hpos)
      rw [Real.log_div (hq i).ne' hpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
      have hcancel : p i * (q i / p i - 1) = q i - p i := by field_simp
      rw [hcancel] at hmul
      dsimp [Real.negMulLog]
      nlinarith [hmul]
  calc
    finiteEntropy p ≤ ∑ i, (-p i * Real.log (q i) + q i - p i) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ∑ i, -p i * Real.log (q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp_sum, hq_sum]
      ring

/-- The finite Gibbs variational inequality (log-sum-exp), with actual Shannon
entropy on the left. No entropy upper bound is assumed. -/
theorem finiteEntropy_add_expectation_le_log_sum_exp {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (F : ι → ℝ) :
    finiteEntropy p + ∑ i, p i * F i ≤ Real.log (∑ i, Real.exp (F i)) := by
  classical
  have hι : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hp_sum
  let := hι
  let Z : ℝ := ∑ i, Real.exp (F i)
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos (F i)) Finset.univ_nonempty
  let q : ι → ℝ := fun i => Real.exp (F i) / Z
  have hq : ∀ i, 0 < q i := fun i => div_pos (Real.exp_pos _) hZ
  have hq_sum : ∑ i, q i = 1 := by
    change (∑ i, Real.exp (F i) / Z) = 1
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hlog (i : ι) : Real.log (q i) = F i - Real.log Z := by
    dsimp [q]
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hcross := finiteEntropy_le_crossEntropy hp hp_sum hq hq_sum
  have heq : (∑ i, -p i * Real.log (q i)) = Real.log Z - ∑ i, p i * F i := by
    calc
      _ = ∑ i, (p i * Real.log Z - p i * F i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hlog]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
  rw [heq] at hcross
  linarith [hcross]

/-- The mass of one output value after merging every input with that value.
The target may include unoccupied values, whose mass is zero. -/
noncomputable def atomMass {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (f : ι → κ) (y : κ) : ℝ :=
  ∑ i, if f i = y then p i else 0

/-- Merging equal atoms preserves nonnegative masses and total probability. -/
theorem atomMass_probability {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) (f : ι → κ) :
    (∀ y, 0 ≤ atomMass p f y) ∧ ∑ y, atomMass p f y = 1 := by
  constructor
  · intro y
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all
  · simp only [atomMass]
    rw [Finset.sum_comm]
    simpa using hp_sum

/-- Expectations use merged atom masses, rather than counting coincident words
as separate atoms. This identity applies to every test function, including cosine. -/
theorem atomMass_expectation {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (f : ι → κ) (F : κ → ℝ) :
    ∑ y, atomMass p f y * F y = ∑ i, p i * F (f i) := by
  simp only [atomMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

end Salem
