module

public import Mathlib

@[expose] public section

open scoped BigOperators
open Set

namespace Salem

/-- The logarithmic cosine potential used for the localized seed action. -/
noncomputable def cosinePotential (t : ℝ) : ℝ :=
  -Real.log (Real.cos (Real.pi * t) ^ 2)

/-- The finite positive logarithm series used to enclose a core potential. -/
noncomputable def potentialLogSum (z : ℝ) (n : ℕ) : ℝ :=
  4 * ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)

/-- A rigorous finite enclosure for `-2 log c`, with the rational transform
`z=(1-c)/(1+c)`.  The remainder here omits the optional improvement by the
factor `2*n+1`, so it follows directly from Mathlib's logarithm-series bound. -/
theorem neg_two_log_enclosure {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    let z := (1 - c) / (1 + c)
    potentialLogSum z n ≤ -2 * Real.log c ∧
      -2 * Real.log c ≤
        potentialLogSum z n + 4 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
  let z := (1 - c) / (1 + c)
  have hden : 0 < 1 + c := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hden.le
  have hz1 : z < 1 := (div_lt_one hden).mpr (by linarith)
  have hratio : (1 + z) / (1 - z) = c⁻¹ := by
    dsimp [z]
    field_simp [hc.ne']
    ring
  have hlog : (1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z)) =
      -(1 / 2 : ℝ) * Real.log c := by
    rw [hratio, Real.log_inv]
    ring
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  rw [hlog] at hlo hhi
  change potentialLogSum z n ≤ -2 * Real.log c ∧
    -2 * Real.log c ≤ potentialLogSum z n + 4 * z ^ (2 * n + 1) / (1 - z ^ 2)
  dsimp [potentialLogSum]
  constructor
  · linarith
  · convert mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring

/-- The finite logarithm enclosure applies to the actual cosine potential,
provided its cosine is positive.  This is an analytic statement about the
potential, independent of any action-bound certificate. -/
theorem cosinePotential_enclosure {t : ℝ}
    (ht : 0 < Real.cos (Real.pi * t)) (n : ℕ) :
    let z := (1 - Real.cos (Real.pi * t)) / (1 + Real.cos (Real.pi * t))
    potentialLogSum z n ≤ cosinePotential t ∧
      cosinePotential t ≤
        potentialLogSum z n + 4 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
  have h := neg_two_log_enclosure ht (Real.cos_le_one _) n
  simpa [cosinePotential, Real.log_pow] using h

/-- A lower bound for the cosine gives an upper bound for the actual
logarithmic potential. -/
theorem cosinePotential_le_neg_two_log {t c : ℝ} (hc : 0 < c)
    (hct : c ≤ Real.cos (Real.pi * t)) :
    cosinePotential t ≤ -2 * Real.log c := by
  have hlog := Real.log_le_log hc hct
  norm_num only [cosinePotential, Real.log_pow, Nat.cast_ofNat]
  linarith

/-- Rational lower cosine bounds can be inserted into the finite logarithm
series.  All quantities on the right are rational when `c` is rational. -/
theorem cosinePotential_le_logSum {t c : ℝ} (hc : 0 < c)
    (hct : c ≤ Real.cos (Real.pi * t)) (n : ℕ) :
    let z := (1 - c) / (1 + c)
    cosinePotential t ≤
      potentialLogSum z n + 4 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
  exact (cosinePotential_le_neg_two_log hc hct).trans
    (neg_two_log_enclosure hc (hct.trans (Real.cos_le_one _)) n).2

/-- The sixth-degree cosine Taylor polynomial is a lower bound on the
central half-period.  Its proof uses the nonnegative eighth derivative in
Taylor's Lagrange remainder. -/
theorem cos_lower_degree_six (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨y, hy, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.cos) (x₀ := 0)
      (n := 7) (Ne.symm hx0) Real.contDiff_cos.contDiffOn
  have hderiv (k : ℕ) : iteratedDerivWithin k Real.cos (uIcc 0 x) 0 =
      iteratedDeriv k Real.cos 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hx0))
      Real.contDiff_cos.contDiffAt (left_mem_uIcc)
  have hpoly : taylorWithinEval Real.cos 7 (uIcc 0 x) 0 x =
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
    rw [taylor_within_apply]
    simp_rw [hderiv]
    norm_num [Finset.sum_range_succ, Real.iteratedDeriv_add_one_cos,
      Real.iteratedDeriv_add_one_sin]
    ring
  have hyabs : |y| ≤ Real.pi / 2 := by
    have hy' := (uIoo_subset_uIcc_self hy)
    have hxb := abs_le.mp hx
    rcases le_total 0 x with hxpos | hxneg
    · rw [uIcc_of_le hxpos] at hy'
      exact abs_le.mpr ⟨by linarith [Real.pi_pos, hy'.1], by linarith [hy'.2]⟩
    · rw [uIcc_of_ge hxneg] at hy'
      exact abs_le.mpr ⟨by linarith [hy'.1], by linarith [Real.pi_pos, hy'.2]⟩
  have hcos : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc (abs_le.mp hyabs)
  rw [hpoly] at heq
  norm_num [Real.iteratedDeriv_add_one_cos, Real.iteratedDeriv_add_one_sin] at heq
  nlinarith [mul_nonneg hcos (sq_nonneg (x ^ 4))]

/-- A bounded argument can be replaced by a larger rational argument before
using the polynomial cosine bound. -/
theorem cos_lower_degree_six_of_abs_le {t x : ℝ}
    (ht : |Real.pi * t| ≤ x) (hx : x ≤ Real.pi / 2) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos (Real.pi * t) := by
  have hx0 : 0 ≤ x := (abs_nonneg _).trans ht
  have hcos : Real.cos x ≤ Real.cos |Real.pi * t| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [Real.pi_pos]) ht
  simpa only [Real.cos_abs] using
    (cos_lower_degree_six x (by rwa [abs_of_nonneg hx0])).trans hcos

noncomputable def cosineLowerPolynomial (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
noncomputable def radiusPotentialBound (a : ℝ) (n : ℕ) : ℝ :=
  let c := cosineLowerPolynomial ((3927 / 1250 : ℝ) * a)
  let z := (1 - c) / (1 + c)
  potentialLogSum z n + 4 * z ^ (2 * n + 1) / (1 - z ^ 2)
/-- The rational polynomial/logarithm expression is a proved upper bound
for every potential whose coordinate lies in the stated radius. -/
theorem cosinePotential_le_radiusPotentialBound {t a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 43 / 100) (ht : |t| ≤ a) (n : ℕ) :
    cosinePotential t ≤ radiusPotentialBound a n := by
  let x := (3927 / 1250 : ℝ) * a
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 7 / 5 := by dsimp [x]; linarith
  have hxpi : x ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have harg : |Real.pi * t| ≤ x := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      Real.pi * |t| ≤ Real.pi * a := mul_le_mul_of_nonneg_left ht Real.pi_pos.le
      _ ≤ x := by
        dsimp [x]
        exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d4]) ha0
  have hcpos : 0 < cosineLowerPolynomial x := by
    have hx2 := pow_le_pow_left₀ hx0 hx 2
    have hx6 := pow_le_pow_left₀ hx0 hx 6
    norm_num at hx2 hx6
    dsimp [cosineLowerPolynomial]
    nlinarith [pow_nonneg hx0 4]
  have hcos : cosineLowerPolynomial x ≤ Real.cos (Real.pi * t) :=
    cos_lower_degree_six_of_abs_le harg hxpi
  exact cosinePotential_le_logSum hcpos hcos n

/-- The magnitude of the P1 expanding seed at the left endpoint `t=-11`,
written directly with `U₁(b)=b+1+b⁻¹` and `P₁′(b)`. -/
noncomputable def p1SeedStartingCoefficient (b : ℝ) : ℝ :=
  (b + 1 + b⁻¹) ^ 3 / ((4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1) * b ^ 12)
/-- Outward rational enclosure of the actual algebraic starting
coefficient from a precise enclosure of the expanding root. -/
theorem p1SeedStartingCoefficient_bounds {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) :
    (7473517429 / 10 ^ 12 : ℝ) ≤ p1SeedStartingCoefficient b ∧
      p1SeedStartingCoefficient b ≤ (7473517431 / 10 ^ 12 : ℝ) := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hbl
  have hi : (10 ^ 15 / 1722083805739043 : ℝ) ≤ b⁻¹ ∧
      b⁻¹ ≤ (10 ^ 15 / 1722083805739042 : ℝ) := by
    constructor
    · simpa [one_div] using one_div_le_one_div_of_le hbpos hbu
    · simpa [one_div] using one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 1722083805739042 / 10 ^ 15) hbl
  have ha : (330277563773199 / 10 ^ 14 : ℝ) ≤ b + 1 + b⁻¹ ∧
      b + 1 + b⁻¹ ≤ (330277563773201 / 10 ^ 14 : ℝ) := by
    constructor <;> linarith [hi.1, hi.2]
  have hd : (7086972917494 / 10 ^ 12 : ℝ) ≤ 4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1 ∧
      4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1 ≤ (7086972917496 / 10 ^ 12 : ℝ) := by
    have hb2lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1722083805739042 / 10 ^ 15) hbl 2
    have hb2hi := pow_le_pow_left₀ hbpos.le hbu 2
    have hb3lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1722083805739042 / 10 ^ 15) hbl 3
    have hb3hi := pow_le_pow_left₀ hbpos.le hbu 3
    constructor <;> norm_num at * <;> linarith
  have hpowlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1722083805739042 / 10 ^ 15) hbl 12
  have hpowhi := pow_le_pow_left₀ hbpos.le hbu 12
  have hdenpos : 0 < (4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1) * b ^ 12 := by
    exact mul_pos (lt_of_lt_of_le (by norm_num) hd.1) (pow_pos hbpos _)
  unfold p1SeedStartingCoefficient
  constructor
  · apply (le_div_iff₀ hdenpos).mpr
    have ha3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 330277563773199 / 10 ^ 14) ha.1 3
    have hdenhi : (4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1) * b ^ 12 ≤
        (7086972917496 / 10 ^ 12 : ℝ) * (1722083805739043 / 10 ^ 15) ^ 12 := by
      exact mul_le_mul hd.2 hpowhi (pow_nonneg hbpos.le _) (by norm_num)
    norm_num at hdenhi ha3 ⊢
    linarith
  · apply (div_le_iff₀ hdenpos).mpr
    have ha3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ b + 1 + b⁻¹) ha.2 3
    have hdenlo : (7086972917494 / 10 ^ 12 : ℝ) * (1722083805739042 / 10 ^ 15) ^ 12 ≤
        (4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1) * b ^ 12 := by
      exact mul_le_mul hd.1 hpowlo (by positivity) (by linarith [hd.1])
    norm_num at hdenlo ha3 ⊢
    linarith

/-- Exact root isolation for the expanding real root of `P₁`.
The hypotheses are the quartic equation and the coarse root range, rather
than any action estimate. -/
theorem p1_expanding_root_interval {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (1722083805739042 / 10 ^ 15 : ℝ) < b ∧
      b < (1722083805739043 / 10 ^ 15 : ℝ) := by
  let f : ℝ → ℝ := fun x => x ^ 4 - x ^ 3 - x ^ 2 - x + 1
  have hd (x : ℝ) : HasDerivAt f (4 * x ^ 3 - 3 * x ^ 2 - 2 * x - 1) x := by
    dsimp [f]
    convert (((((hasDerivAt_id x).pow 4).sub ((hasDerivAt_id x).pow 3)).sub
      ((hasDerivAt_id x).pow 2)).sub (hasDerivAt_id x)).add_const 1 using 1
    · ext y
      simp [id]
    · simp [id]
  have hm : StrictMonoOn f (Ici (5 / 3)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _)
      (by fun_prop) (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    have hx' : 0 ≤ x - 5 / 3 := by
      have : (5 / 3 : ℝ) ≤ x := interior_subset hx
      linarith
    have hpos : 0 < 4 * (x - 5 / 3) ^ 3 + 17 * (x - 5 / 3) ^ 2 +
        (64 / 3 : ℝ) * (x - 5 / 3) + 158 / 27 := by positivity
    nlinarith [hpos]
  have hblmem : (1722083805739042 / 10 ^ 15 : ℝ) ∈ Ici (5 / 3) := by norm_num
  have hbumem : (1722083805739043 / 10 ^ 15 : ℝ) ∈ Ici (5 / 3) := by norm_num
  have hflo : f (1722083805739042 / 10 ^ 15) < f b := by
    dsimp [f]
    rw [hroot]
    norm_num
  have hfhi : f b < f (1722083805739043 / 10 ^ 15) := by
    dsimp [f]
    rw [hroot]
    norm_num
  exact ⟨(hm.lt_iff_lt hblmem hb).mp hflo, (hm.lt_iff_lt hb hbumem).mp hfhi⟩

/-- Exact centering integers for the P1 seed core, in increasing indices
`t=-11,...,15`. -/
noncomputable def p1SeedCentering : Fin 27 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -2, -3, -5, -9, -15,
    -26, -45, -77, -133, -228, -393, -677, -1166, -2008, -3458, -5955, -10255]
/-- Outward rational coordinate radii for the 27-point P1 seed core. -/
noncomputable def p1SeedCoreRadius : Fin 27 → ℝ := fun j =>
  (![748, 1288, 2217, 3817, 6573, 11319, 19492, 33567, 42196, 457,
      28578, 4797, 8366, 24552, 7597, 3794, 29115, 760, 41264, 32656,
      19747, 11899, 5564, 4553, 2268, 485, 1742] : Fin 27 → ℝ) j / 100000
/-- The centered expanding seed coordinate at `t=j-11`. -/
noncomputable def p1SeedCoreCoordinate (b : ℝ) (j : Fin 27) : ℝ :=
  -(p1SeedStartingCoefficient b * b ^ (j : ℕ)) - (p1SeedCentering j : ℝ)
/-- Every one of the 27 actual algebraic coordinates lies in its stated
rational interval.  The finite arithmetic is checked by `norm_num`. -/
theorem p1SeedCoreCoordinate_abs_le {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) (j : Fin 27) :
    |p1SeedCoreCoordinate b j| ≤ p1SeedCoreRadius j := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hbl
  have hh := p1SeedStartingCoefficient_bounds hbl hbu
  have hhpos : 0 ≤ p1SeedStartingCoefficient b := by linarith [hh.1]
  have hp : (7473517429 / 10 ^ 12 : ℝ) * (1722083805739042 / 10 ^ 15) ^ (j : ℕ) ≤
        p1SeedStartingCoefficient b * b ^ (j : ℕ) ∧
      p1SeedStartingCoefficient b * b ^ (j : ℕ) ≤
        (7473517431 / 10 ^ 12 : ℝ) * (1722083805739043 / 10 ^ 15) ^ (j : ℕ) := by
    constructor
    · apply mul_le_mul hh.1
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1722083805739042 / 10 ^ 15) hbl _)
        (by positivity) hhpos
    · apply mul_le_mul hh.2 (pow_le_pow_left₀ hbpos.le hbu _) (by positivity) (by norm_num)
  apply abs_le.mpr
  constructor <;> fin_cases j <;>
    norm_num [p1SeedCoreCoordinate, p1SeedCoreRadius, p1SeedCentering] at hp ⊢ <;>
    linarith [hp.1, hp.2]

/-- The certified radii retain the appendix's strict boundary margin. -/
theorem p1SeedCoreRadius_bounds (j : Fin 27) :
    0 ≤ p1SeedCoreRadius j ∧ p1SeedCoreRadius j < 1 / 2 - 39 / 500 := by
  fin_cases j <;> norm_num [p1SeedCoreRadius]
/-- The tabulated centering integer is the actual nearest-integer
centering of the expanding seed. -/
theorem p1SeedCoreCoordinate_floor {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) (j : Fin 27) :
    ⌊-(p1SeedStartingCoefficient b * b ^ (j : ℕ)) + 1 / 2⌋ = p1SeedCentering j := by
  have hrad := (p1SeedCoreRadius_bounds j).2
  have habs := p1SeedCoreCoordinate_abs_le hbl hbu j
  have hcoord := abs_le.mp habs
  apply Int.floor_eq_iff.mpr
  dsimp [p1SeedCoreCoordinate] at hcoord
  constructor <;> linarith [hcoord.1, hcoord.2]
/-- Every seed core cosine is strictly positive; the real-valued
potential never relies on the totalized logarithm at zero. -/
theorem p1SeedCoreCoordinate_cos_pos {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) (j : Fin 27) :
    0 < Real.cos (Real.pi * p1SeedCoreCoordinate b j) := by
  have hrad := (p1SeedCoreRadius_bounds j).2
  have habs := p1SeedCoreCoordinate_abs_le hbl hbu j
  have hcoord := abs_le.mp habs
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos,
    mul_pos Real.pi_pos (show 0 < 1 / 2 - p1SeedCoreCoordinate b j by linarith [hcoord.2]),
    mul_pos Real.pi_pos (show 0 < p1SeedCoreCoordinate b j + 1 / 2 by linarith [hcoord.1])]

/-- Rational potential budgets for each of the 27 core coordinates. -/
noncomputable def p1SeedPotentialBudget : Fin 27 → ℝ := fun j =>
  (![57, 165, 487, 1443, 4296, 12922, 40108, 141212, 283382, 22,
      94542, 2281, 6990, 66542, 5753, 1426, 98849, 59, 261267, 131449,
      41244, 14314, 3073, 2054, 510, 25, 301] : Fin 27 → ℝ) j / 100000
/-- The 27 scalar potential computations are kernel-checked rational
inequalities, using ten positive logarithm-series terms. -/
theorem p1SeedPotentialBudget_valid (j : Fin 27) :
    radiusPotentialBound (p1SeedCoreRadius j) 10 < p1SeedPotentialBudget j := by
  fin_cases j <;>
    norm_num [radiusPotentialBound, cosineLowerPolynomial, potentialLogSum,
      p1SeedCoreRadius, p1SeedPotentialBudget, Finset.sum_range_succ]

/-- Actual action of the 27 centered expanding seed coordinates.
No action estimate is assumed: the coordinate, cosine and logarithm bounds
above verify the entire sum. -/
theorem p1_seed_core_action {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) :
    (∑ j : Fin 27, cosinePotential (p1SeedCoreCoordinate b j)) < (243 / 20 : ℝ) := by
  have hrad (j : Fin 27) : 0 ≤ p1SeedCoreRadius j ∧ p1SeedCoreRadius j ≤ 43 / 100 := by
    have h := p1SeedCoreRadius_bounds j
    constructor
    · exact h.1
    · linarith [h.2]
  have hpoint (j : Fin 27) : cosinePotential (p1SeedCoreCoordinate b j) <
      p1SeedPotentialBudget j := by
    exact (cosinePotential_le_radiusPotentialBound (hrad j).1 (hrad j).2
      (p1SeedCoreCoordinate_abs_le hbl hbu j) 10).trans_lt (p1SeedPotentialBudget_valid j)
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hbudget : (∑ j : Fin 27, p1SeedPotentialBudget j) < (243 / 20 : ℝ) := by
    norm_num [p1SeedPotentialBudget, Fin.sum_univ_succ]
  exact hsum.trans hbudget

/-- The same actual core estimate using only the upstream quartic root
conditions, with no numerical enclosure left as an assumption. -/
theorem p1_seed_core_action_of_root {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (∑ j : Fin 27, cosinePotential (p1SeedCoreCoordinate b j)) < (243 / 20 : ℝ) := by
  have hi := p1_expanding_root_interval hb hroot
  exact p1_seed_core_action hi.1.le hi.2.le

/-- A direct quadratic bound for the actual potential on the P1 tail
interval, proved from the logarithm inequality and the sine square bound. -/
theorem cosinePotential_le_ten_sq {t : ℝ} (ht : |t| ≤ (1 / 100 : ℝ)) :
    cosinePotential t ≤ (10 : ℝ) * t ^ 2 := by
  let q : ℝ := Real.cos (Real.pi * t) ^ 2
  have ht2 : t ^ 2 ≤ (1 / 10000 : ℝ) := by
    have := abs_le.mp ht
    nlinarith
  have hpi : Real.pi ^ 2 ≤ (3927 / 1250 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hsin : Real.sin (Real.pi * t) ^ 2 ≤
      (3927 / 1250 : ℝ) ^ 2 * t ^ 2 := by
    have h := Real.sin_sq_le_sq (x := Real.pi * t)
    have hp := mul_le_mul_of_nonneg_right hpi (sq_nonneg t)
    nlinarith
  have htrig : Real.sin (Real.pi * t) ^ 2 + q = 1 := by
    exact Real.sin_sq_add_cos_sq _
  have hqbound : 1 - (3927 / 1250 : ℝ) ^ 2 / 10000 ≤ q := by
    have hm := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (3927 / 1250 : ℝ))
    nlinarith
  have hqpos : 0 < q := by linarith [hqbound]
  have hcoef : (3927 / 1250 : ℝ) ^ 2 ≤ (10 : ℝ) * q := by
    linarith [hqbound]
  have hquad : 1 - q ≤ (10 : ℝ) * t ^ 2 * q := by
    have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
    nlinarith
  have hdiv : (1 - q) / q ≤ (10 : ℝ) * t ^ 2 :=
    (div_le_iff₀ hqpos).mpr (by nlinarith [hquad])
  have hlog := Real.one_sub_inv_le_log_of_pos hqpos
  have hinv : q⁻¹ - 1 = (1 - q) / q := by field_simp
  change -Real.log q ≤ (10 : ℝ) * t ^ 2
  rw [← hinv] at hdiv
  linarith

/-- Each P1 geometric tail has finite actual potential action, with an
explicit rational majorant valid for the certified starting data. -/
theorem cosinePotential_p1_geometric_tail_bound {h r : ℝ} (hh : 0 ≤ h) (hhbound : h ≤ (1 / 100 : ℝ))
    (hr : 0 ≤ r) (hrbound : r ≤ (3 / 5 : ℝ)) :
    Summable (fun n : ℕ => cosinePotential (-h * r ^ (n + 1))) ∧
      (∑' n : ℕ, cosinePotential (-h * r ^ (n + 1))) ≤ (9 / 16000 : ℝ) := by
  have hr1 : r < 1 := by linarith
  have hrsq : r ^ 2 < 1 := by nlinarith
  have hgeom := (summable_geometric_of_lt_one (sq_nonneg r) hrsq).mul_left
    (10 * h ^ 2 * r ^ 2)
  have hmajor (n : ℕ) : cosinePotential (-h * r ^ (n + 1)) ≤
      (10 * h ^ 2 * r ^ 2) * (r ^ 2) ^ n := by
    have ht : |-h * r ^ (n + 1)| ≤ (1 / 100 : ℝ) := by
      rw [abs_mul, abs_neg, abs_of_nonneg hh, abs_of_nonneg (pow_nonneg hr _)]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1.le) hh).trans (by simpa using hhbound)
    calc
      cosinePotential (-h * r ^ (n + 1)) ≤ 10 * (-h * r ^ (n + 1)) ^ 2 :=
        cosinePotential_le_ten_sq ht
      _ = (10 * h ^ 2 * r ^ 2) * (r ^ 2) ^ n := by
        rw [pow_succ r n]
        simp only [mul_pow, neg_sq, ← pow_mul]
        rw [Nat.mul_comm n 2]
        ring
  have hnonneg (n : ℕ) : 0 ≤ cosinePotential (-h * r ^ (n + 1)) :=
    neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  have hsum := Summable.of_nonneg_of_le hnonneg hmajor hgeom
  refine ⟨hsum, ?_⟩
  have hs := Summable.tsum_le_tsum hmajor hsum hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg r) hrsq] at hs
  have hh2 : h ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hh hhbound 2
  have hr2 : r ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hr hrbound 2
  have hnum : 10 * h ^ 2 * r ^ 2 ≤ (10 : ℝ) * (1 / 100) ^ 2 * (3 / 5) ^ 2 := by
    gcongr
  have hden : (1 - (3 / 5 : ℝ) ^ 2) ≤ 1 - r ^ 2 := by linarith
  have hb : (10 * h ^ 2 * r ^ 2) / (1 - r ^ 2) ≤ (9 / 16000 : ℝ) := by
    apply (div_le_iff₀ (by nlinarith : 0 < 1 - r ^ 2)).mpr
    nlinarith [hnum]
  exact hs.trans hb

/-- The core's uncentered formula is exactly the appendix expanding
orbit at index `t=j-11`, using the original Laurent seed `U₁³`. -/
theorem p1SeedStartingCoefficient_orbit_identity {b : ℝ} (hb : b ≠ 0) (j : ℕ) :
    -(p1SeedStartingCoefficient b * b ^ j) =
      -(4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1)⁻¹ *
        b ^ ((j : ℤ) - 12) * (b + 1 + b⁻¹) ^ 3 := by
  rw [zpow_sub₀ hb, zpow_natCast]
  norm_num [p1SeedStartingCoefficient, div_eq_mul_inv, mul_inv_rev,
    mul_assoc, mul_left_comm, mul_comm]

/-- Either reflected real tail of the P1 localization, starting one
step outside the 27-point core. -/
noncomputable def p1SeedStableTail (b : ℝ) (n : ℕ) : ℝ :=
  -p1SeedStartingCoefficient b * b⁻¹ ^ (n + 1)
/-- The actual potential sum of the 27-point core and both localized
real tails.  This definition assumes no numerical action bound. -/
noncomputable def p1SeedLocalizedAction (b : ℝ) : ℝ :=
  (∑ j : Fin 27, cosinePotential (p1SeedCoreCoordinate b j)) +
    2 * ∑' n : ℕ, cosinePotential (p1SeedStableTail b n)
theorem p1_seed_stable_tail_action {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    Summable (fun n : ℕ => cosinePotential (p1SeedStableTail b n)) ∧
      (∑' n : ℕ, cosinePotential (p1SeedStableTail b n)) ≤ (9 / 16000 : ℝ) := by
  have hi := p1_expanding_root_interval hb hroot
  have hh := p1SeedStartingCoefficient_bounds hi.1.le hi.2.le
  have hr : 0 ≤ b⁻¹ := inv_nonneg.mpr (by linarith [hb])
  have hrbound : b⁻¹ ≤ (3 / 5 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 3) hb
    simpa [one_div] using h
  exact cosinePotential_p1_geometric_tail_bound (by linarith [hh.1])
    (by linarith [hh.2]) hr hrbound
/-- A proved full localized P1 seed-action bound.  This is the coarse
`E₀<61/5` bound, not the sharper six-decimal table entry. -/
theorem p1_seed_localized_action {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    p1SeedLocalizedAction b < (61 / 5 : ℝ) := by
  have hc := p1_seed_core_action_of_root hb hroot
  have ht := (p1_seed_stable_tail_action hb hroot).2
  dsimp [p1SeedLocalizedAction]
  linarith

/-- Reindex the core and its two one-sided tails by their actual
bilateral orbit indices. -/
noncomputable def p1SeedIndex : (Fin 27 ⊕ (ℕ ⊕ ℕ)) ≃ ℤ where
  toFun := fun q => match q with
    | .inl j => (j : ℕ) - (11 : ℤ)
    | .inr (.inl n) => -12 - (n : ℤ)
    | .inr (.inr n) => 16 + (n : ℤ)
  invFun := fun t => if h1 : t < -11 then .inr (.inl (-12 - t).toNat)
    else if h2 : t ≤ 15 then .inl ⟨(t + 11).toNat, by omega⟩
    else .inr (.inr (t - 16).toNat)
  left_inv := by
    rintro (j | (n | n))
    · simp only
      split_ifs with h1 h2
      · omega
      · congr 1
        apply Fin.ext
        dsimp only
        omega
      · omega
    · simp only
      split_ifs with h1 h2
      · congr 2
        omega
      · omega
      · omega
    · simp only
      split_ifs with h1 h2
      · omega
      · omega
      · congr 2
        omega
  right_inv := by
    intro t
    simp only
    split_ifs with h1 h2
    · simp only
      omega
    · simp only
      omega
    · simp only
      omega

/-- The exact P1 expanding orbit `ξ_t=-κ_b*b^(t-1)*U₁(b)^3`. -/
noncomputable def p1SeedExpandingOrbit (b : ℝ) (t : ℤ) : ℝ :=
  -(4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1)⁻¹ *
    b ^ (t - 1) * (b + 1 + b⁻¹) ^ 3
/-- The stable tail is exactly the reflected expanding orbit appearing
in the localization formula. -/
theorem p1SeedStableTail_eq_orbit {b : ℝ} (n : ℕ) :
    p1SeedStableTail b n = p1SeedExpandingOrbit b (-12 - (n : ℤ)) := by
  have he : (-12 - (n : ℤ)) - 1 = -((12 + (n + 1) : ℕ) : ℤ) := by omega
  dsimp [p1SeedExpandingOrbit]
  rw [he, zpow_neg, zpow_natCast, pow_add]
  simp [p1SeedStableTail, p1SeedStartingCoefficient, div_eq_mul_inv, mul_inv_rev,
    mul_assoc, mul_left_comm, mul_comm]
/-- The core coordinates are the actual centered P1 expanding orbit. -/
theorem p1SeedCoreCoordinate_eq_centered_orbit {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) (j : Fin 27) :
    p1SeedCoreCoordinate b j =
      p1SeedExpandingOrbit b ((j : ℕ) - (11 : ℤ)) -
        (⌊p1SeedExpandingOrbit b ((j : ℕ) - (11 : ℤ)) + 1 / 2⌋ : ℝ) := by
  have hb : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hbl)
  have hid := p1SeedStartingCoefficient_orbit_identity hb (j : ℕ)
  have horb : p1SeedExpandingOrbit b ((j : ℕ) - (11 : ℤ)) =
      -(p1SeedStartingCoefficient b * b ^ (j : ℕ)) := by
    dsimp [p1SeedExpandingOrbit]
    rw [show ((j : ℕ) - (11 : ℤ)) - 1 = (j : ℕ) - (12 : ℤ) by omega]
    exact hid.symm
  rw [horb, p1SeedCoreCoordinate_floor hbl hbu j]
  rfl

/-- The bilateral localized P1 seed: centered expanding core at
`[-11,15]` and the two reflected stable tails outside it. -/
noncomputable def p1SeedLocalizedSequence (b : ℝ) (t : ℤ) : ℝ :=
  Sum.elim (p1SeedCoreCoordinate b)
    (Sum.elim (p1SeedStableTail b) (p1SeedStableTail b)) (p1SeedIndex.symm t)
/-- The finite core and the two tails assemble to the actual bilateral
potential sum; its value is not an assumed action parameter. -/
theorem p1_seed_localized_hasSum {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    HasSum (fun t : ℤ => cosinePotential (p1SeedLocalizedSequence b t))
      (p1SeedLocalizedAction b) := by
  let T := ∑' n : ℕ, cosinePotential (p1SeedStableTail b n)
  have ht := (p1_seed_stable_tail_action hb hroot).1.hasSum
  have htail : HasSum (fun q : ℕ ⊕ ℕ => cosinePotential
      (Sum.elim (p1SeedStableTail b) (p1SeedStableTail b) q)) (T + T) :=
    HasSum.sum (f := fun q : ℕ ⊕ ℕ => cosinePotential
      (Sum.elim (p1SeedStableTail b) (p1SeedStableTail b) q)) ht ht
  have hcore := hasSum_fintype (fun j : Fin 27 => cosinePotential (p1SeedCoreCoordinate b j))
  have hfull : HasSum (fun q : Fin 27 ⊕ (ℕ ⊕ ℕ) => cosinePotential
      (Sum.elim (p1SeedCoreCoordinate b)
        (Sum.elim (p1SeedStableTail b) (p1SeedStableTail b)) q))
      ((∑ j : Fin 27, cosinePotential (p1SeedCoreCoordinate b j)) + (T + T)) :=
    HasSum.sum (f := fun q : Fin 27 ⊕ (ℕ ⊕ ℕ) => cosinePotential
      (Sum.elim (p1SeedCoreCoordinate b)
        (Sum.elim (p1SeedStableTail b) (p1SeedStableTail b)) q)) hcore htail
  apply (p1SeedIndex.hasSum_iff (f := fun t : ℤ => cosinePotential (p1SeedLocalizedSequence b t))).mp
  simpa [Function.comp_def, p1SeedLocalizedSequence, p1SeedLocalizedAction, T, two_mul] using hfull

/-- The four nonzero forcing values in the interior recurrence window. -/
noncomputable def p1SeedCoreForcing (j : Fin 23) : ℤ :=
  if (j : ℕ) = 4 ∨ (j : ℕ) = 18 then 1
  else if (j : ℕ) = 7 ∨ (j : ℕ) = 15 then -1 else 0
theorem p1SeedCentering_forcing (j : Fin 23) :
    -p1SeedCentering ⟨(j : ℕ) + 4, by omega⟩ +
      p1SeedCentering ⟨(j : ℕ) + 3, by omega⟩ +
      p1SeedCentering ⟨(j : ℕ) + 2, by omega⟩ +
      p1SeedCentering ⟨(j : ℕ) + 1, by omega⟩ -
      p1SeedCentering ⟨(j : ℕ), by omega⟩ = p1SeedCoreForcing j := by
  fin_cases j <;> norm_num [p1SeedCentering, p1SeedCoreForcing]
/-- The actual centered seed has forcing `1,-1,-1,1` at indices
`-7,-4,4,7`, and zero in all other interior windows.  This theorem covers only wholly-core windows.  The outgoing junction of
the localized sequence retains its neutral defect; no global integer forcing
for the localized sequence is asserted. -/
theorem p1SeedCoreCoordinate_forcing {b : ℝ} (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (j : Fin 23) :
    p1SeedCoreCoordinate b ⟨(j : ℕ) + 4, by omega⟩ -
      p1SeedCoreCoordinate b ⟨(j : ℕ) + 3, by omega⟩ -
      p1SeedCoreCoordinate b ⟨(j : ℕ) + 2, by omega⟩ -
      p1SeedCoreCoordinate b ⟨(j : ℕ) + 1, by omega⟩ +
      p1SeedCoreCoordinate b ⟨(j : ℕ), by omega⟩ = (p1SeedCoreForcing j : ℝ) := by
  have hf : -(p1SeedCentering ⟨(j : ℕ) + 4, by omega⟩ : ℝ) +
      (p1SeedCentering ⟨(j : ℕ) + 3, by omega⟩ : ℝ) +
      (p1SeedCentering ⟨(j : ℕ) + 2, by omega⟩ : ℝ) +
      (p1SeedCentering ⟨(j : ℕ) + 1, by omega⟩ : ℝ) -
      (p1SeedCentering ⟨(j : ℕ), by omega⟩ : ℝ) = (p1SeedCoreForcing j : ℝ) := by
    exact_mod_cast p1SeedCentering_forcing j
  dsimp only [p1SeedCoreCoordinate]
  simp only [pow_add]
  linear_combination -p1SeedStartingCoefficient b * b ^ (j : ℕ) * hroot + hf

theorem p1SeedStableTail_abs_le {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (n : ℕ) :
    |p1SeedStableTail b n| ≤ (1 / 100 : ℝ) := by
  have hi := p1_expanding_root_interval hb hroot
  have hh := p1SeedStartingCoefficient_bounds hi.1.le hi.2.le
  have hh0 : 0 ≤ p1SeedStartingCoefficient b := by linarith [hh.1]
  have hr0 : 0 ≤ b⁻¹ := inv_nonneg.mpr (by linarith [hb])
  have hr1 : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hb])
  rw [p1SeedStableTail, abs_mul, abs_neg, abs_of_nonneg hh0,
    abs_of_nonneg (pow_nonneg hr0 _)]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1) hh0).trans (by linarith [hh.2])
/-- The actual bilateral localization retains a strict global margin
from the half-integers, including both infinite tails. -/
theorem p1_seed_localized_margin {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    |p1SeedLocalizedSequence b t| < 1 / 2 - 39 / 500 := by
  have hi := p1_expanding_root_interval hb hroot
  obtain ⟨q, rfl⟩ := p1SeedIndex.surjective t
  rcases q with j | (n | n)
  · simpa only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl] using
      (p1SeedCoreCoordinate_abs_le hi.1.le hi.2.le j).trans_lt (p1SeedCoreRadius_bounds j).2
  · simpa only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using
      (p1SeedStableTail_abs_le hb hroot n).trans_lt (by norm_num : (1 / 100 : ℝ) < 1 / 2 - 39 / 500)
  · simpa only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using
      (p1SeedStableTail_abs_le hb hroot n).trans_lt (by norm_num : (1 / 100 : ℝ) < 1 / 2 - 39 / 500)
/-- Every cosine in the actual bilateral action is positive. -/
theorem p1_seed_localized_cos_pos {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    0 < Real.cos (Real.pi * p1SeedLocalizedSequence b t) := by
  have ht : |p1SeedLocalizedSequence b t| < (1 / 2 : ℝ) := by
    linarith [p1_seed_localized_margin hb hroot t]
  apply Real.cos_pos_of_mem_Ioo
  apply abs_lt.mp
  rw [abs_mul, abs_of_pos Real.pi_pos]
  nlinarith [mul_lt_mul_of_pos_left ht Real.pi_pos]

/-- The integer-indexed localized seed has finite action below `61/5`.
This is an actual cosine-potential sum, not a field assumed in a certificate. -/
theorem p1_seed_localized_tsum_bound {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    Summable (fun t : ℤ => cosinePotential (p1SeedLocalizedSequence b t)) ∧
      (∑' t : ℤ, cosinePotential (p1SeedLocalizedSequence b t)) < (61 / 5 : ℝ) := by
  have hs := p1_seed_localized_hasSum hb hroot
  exact ⟨hs.summable, hs.tsum_eq.trans_lt (p1_seed_localized_action hb hroot)⟩

/-- Retain the exact sum of the checked pointwise budgets, before
rounding it to the coarser displayed core bound. -/
theorem p1_seed_core_action_budget {b : ℝ}
    (hbl : (1722083805739042 / 10 ^ 15 : ℝ) ≤ b)
    (hbu : b ≤ (1722083805739043 / 10 ^ 15 : ℝ)) :
    (∑ j : Fin 27, cosinePotential (p1SeedCoreCoordinate b j)) < (1214773 / 100000 : ℝ) := by
  have hrad (j : Fin 27) : 0 ≤ p1SeedCoreRadius j ∧ p1SeedCoreRadius j ≤ 43 / 100 := by
    have h := p1SeedCoreRadius_bounds j
    constructor
    · exact h.1
    · linarith [h.2]
  have hpoint (j : Fin 27) : cosinePotential (p1SeedCoreCoordinate b j) <
      p1SeedPotentialBudget j := by
    exact (cosinePotential_le_radiusPotentialBound (hrad j).1 (hrad j).2
      (p1SeedCoreCoordinate_abs_le hbl hbu j) 10).trans_lt (p1SeedPotentialBudget_valid j)
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hbudget : (∑ j : Fin 27, p1SeedPotentialBudget j) = (1214773 / 100000 : ℝ) := by
    norm_num [p1SeedPotentialBudget, Fin.sum_univ_succ]
  rwa [hbudget] at hsum
/-- A stronger full seed-action bound that retains enough room for
subsequent mirror and Fourier estimates. -/
theorem p1_seed_localized_action_refined {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    p1SeedLocalizedAction b < (12148855 / 1000000 : ℝ) := by
  have hi := p1_expanding_root_interval hb hroot
  have hc := p1_seed_core_action_budget hi.1.le hi.2.le
  have ht := (p1_seed_stable_tail_action hb hroot).2
  dsimp [p1SeedLocalizedAction]
  linarith

/-- Strong actual bilateral action bound, with both infinite tails
included and with the checked core budget retained exactly. -/
theorem p1_seed_localized_tsum_refined {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) :
    (∑' t : ℤ, cosinePotential (p1SeedLocalizedSequence b t)) <
      (12148855 / 1000000 : ℝ) := by
  exact (p1_seed_localized_hasSum hb hroot).tsum_eq.trans_lt
    (p1_seed_localized_action_refined hb hroot)

/-- The localized sequence agrees exactly with the uncentered expanding
orbit through the first four core coordinates, covering the incoming junction. -/
theorem p1SeedLocalizedSequence_eq_orbit_of_le_neg8 {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : t ≤ -8) :
    p1SeedLocalizedSequence b t = p1SeedExpandingOrbit b t := by
  have hi := p1_expanding_root_interval hb hroot
  have hbnz : b ≠ 0 := ne_of_gt (by linarith [hb])
  obtain ⟨q, rfl⟩ := p1SeedIndex.surjective t
  rcases q with j | (n | n)
  · change (j : ℕ) - (11 : ℤ) ≤ -8 at ht
    have hj : (j : ℕ) < 4 := by omega
    have hc : p1SeedCentering j = 0 := by
      fin_cases j <;> norm_num [p1SeedCentering] at *
    simp only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl]
    change p1SeedCoreCoordinate b j = p1SeedExpandingOrbit b ((j : ℕ) - (11 : ℤ))
    have horb : p1SeedExpandingOrbit b ((j : ℕ) - (11 : ℤ)) =
        -(p1SeedStartingCoefficient b * b ^ (j : ℕ)) := by
      dsimp [p1SeedExpandingOrbit]
      rw [show ((j : ℕ) - (11 : ℤ)) - 1 = (j : ℕ) - (12 : ℤ) by omega]
      exact (p1SeedStartingCoefficient_orbit_identity hbnz (j : ℕ)).symm
    rw [horb]
    simp [p1SeedCoreCoordinate, hc]
  · simp only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl]
    change p1SeedStableTail b n = p1SeedExpandingOrbit b (-12 - (n : ℤ))
    exact p1SeedStableTail_eq_orbit (b := b) n
  · change 16 + (n : ℤ) ≤ -8 at ht
    omega
theorem p1SeedExpandingOrbit_recurrence {b : ℝ} (hb : b ≠ 0)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    p1SeedExpandingOrbit b (t + 4) - p1SeedExpandingOrbit b (t + 3) -
      p1SeedExpandingOrbit b (t + 2) - p1SeedExpandingOrbit b (t + 1) +
      p1SeedExpandingOrbit b t = 0 := by
  have hpow (k : ℕ) : b ^ ((t + (k : ℤ)) - 1) = b ^ (t - 1) * b ^ k := by
    rw [show (t + (k : ℤ)) - 1 = (t - 1) + (k : ℤ) by omega,
      zpow_add₀ hb, zpow_natCast]
  simp only [p1SeedExpandingOrbit]
  have h4 := hpow 4
  have h3 := hpow 3
  have h2 := hpow 2
  have h1 := hpow 1
  norm_num only [Nat.cast_ofNat] at h4 h3 h2 h1
  rw [h4, h3, h2, h1]
  linear_combination -(4 * b ^ 3 - 3 * b ^ 2 - 2 * b - 1)⁻¹ *
    b ^ (t - 1) * (b + 1 + b⁻¹) ^ 3 * hroot
/-- There is no forcing on the entire incoming half-line, including
its junction with the centered core.  No assertion is made here about the
localized outgoing junction, where the neutral residual must be restored. -/
theorem p1_seed_incoming_recurrence {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) {t : ℤ} (ht : t ≤ -12) :
    p1SeedLocalizedSequence b (t + 4) - p1SeedLocalizedSequence b (t + 3) -
      p1SeedLocalizedSequence b (t + 2) - p1SeedLocalizedSequence b (t + 1) +
      p1SeedLocalizedSequence b t = 0 := by
  rw [p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (t := t + 4) (by omega),
    p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (t := t + 3) (by omega),
    p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (t := t + 2) (by omega),
    p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (t := t + 1) (by omega),
    p1SeedLocalizedSequence_eq_orbit_of_le_neg8 hb hroot (t := t) (by omega)]
  exact p1SeedExpandingOrbit_recurrence (ne_of_gt (by linarith [hb])) hroot t

/-- The retained rational radii give the stronger initial mirror margin. -/
theorem p1SeedCoreRadius_max (j : Fin 27) :
    p1SeedCoreRadius j ≤ (1 / 2 - 1951 / 25000 : ℝ) := by
  fin_cases j <;> norm_num [p1SeedCoreRadius]

/-- The initial global boundary distance is at least `0.07804`, enough to
retain `0.078` after subtracting the first certified return amplitude. -/
theorem p1_seed_localized_margin_refined {b : ℝ} (hb : (5 / 3 : ℝ) ≤ b)
    (hroot : b ^ 4 - b ^ 3 - b ^ 2 - b + 1 = 0) (t : ℤ) :
    |p1SeedLocalizedSequence b t| ≤ 1 / 2 - 1951 / 25000 := by
  have hi := p1_expanding_root_interval hb hroot
  obtain ⟨q, rfl⟩ := p1SeedIndex.surjective t
  rcases q with j | (n | n)
  · simpa only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl] using
      (p1SeedCoreCoordinate_abs_le hi.1.le hi.2.le j).trans (p1SeedCoreRadius_max j)
  · simpa only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using
      (p1SeedStableTail_abs_le hb hroot n).trans (by norm_num : (1 / 100 : ℝ) ≤ 1 / 2 - 1951 / 25000)
  · simpa only [p1SeedLocalizedSequence, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using
      (p1SeedStableTail_abs_le hb hroot n).trans (by norm_num : (1 / 100 : ℝ) ≤ 1 / 2 - 1951 / 25000)

end Salem
