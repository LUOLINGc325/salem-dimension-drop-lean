module

public import Salem.P1Analytic

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The actual logarithmic cosine potential is nonnegative. -/
lemma cosinePotential_nonneg (t : ℝ) : 0 ≤ cosinePotential t := by
  dsimp [cosinePotential]
  exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))

/-- Strict centering supplies the nonvanishing cosine condition needed when
passing from the real-valued potential to an actual Fourier product. -/
lemma cosinePotential_cos_pos {t : ℝ} (ht : |t| < (1 / 2 : ℝ)) :
    0 < Real.cos (Real.pi * t) := by
  have hb := abs_lt.mp ht
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hm := mul_lt_mul_of_pos_left hb.1 Real.pi_pos
    nlinarith
  · have hm := mul_lt_mul_of_pos_left hb.2 Real.pi_pos
    nlinarith

/-- A rational quadratic majorant for the potential on a small interval.
It is strong enough for the localized P₂ tails with coefficient `10⁻²⁴`. -/
lemma cosinePotential_le_quadratic {t : ℝ} (ht : |t| ≤ (1 / 1000 : ℝ)) :
    cosinePotential t ≤ (987 / 100 : ℝ) * t ^ 2 := by
  let q : ℝ := Real.cos (Real.pi * t) ^ 2
  have ht2 : t ^ 2 ≤ (1 / 1000000 : ℝ) := by
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
  have hqbound : 1 - (3927 / 1250 : ℝ) ^ 2 / 1000000 ≤ q := by
    have hm := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (3927 / 1250 : ℝ))
    nlinarith
  have hqpos : 0 < q := by linarith [hqbound]
  have hcoef : (3927 / 1250 : ℝ) ^ 2 ≤ (987 / 100 : ℝ) * q := by
    linarith [hqbound]
  have hquad : 1 - q ≤ (987 / 100 : ℝ) * t ^ 2 * q := by
    have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
    nlinarith
  have hdiv : (1 - q) / q ≤ (987 / 100 : ℝ) * t ^ 2 :=
    (div_le_iff₀ hqpos).mpr (by nlinarith [hquad])
  have hlog := Real.one_sub_inv_le_log_of_pos hqpos
  have hinv : q⁻¹ - 1 = (1 - q) / q := by field_simp
  change -Real.log q ≤ (987 / 100 : ℝ) * t ^ 2
  rw [← hinv] at hdiv
  linarith

/-- A pointwise geometric bound gives a summable actual potential action.
This proves the stable-tail estimate, rather than assuming an action bound. -/
lemma cosinePotential_geometric_bound {f : ℕ → ℝ} {h r : ℝ}
    (hh : 0 ≤ h) (hsmall : h ≤ 1 / 1000)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ n, |f n| ≤ h * r ^ n) :
    Summable (fun n => cosinePotential (f n)) ∧
      (∑' n, cosinePotential (f n)) ≤ (987 / 100 : ℝ) * h ^ 2 / (1 - r ^ 2) := by
  have hrsq : r ^ 2 < 1 := by nlinarith
  have hgeom := summable_geometric_of_lt_one (sq_nonneg r) hrsq
  have hmajor : ∀ n, cosinePotential (f n) ≤
      ((987 / 100 : ℝ) * h ^ 2) * (r ^ 2) ^ n := by
    intro n
    have ht : |f n| ≤ (1 / 1000 : ℝ) := by
      calc
        |f n| ≤ h * r ^ n := hf n
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) hh
        _ ≤ 1 / 1000 := by simpa using hsmall
    have hs : (f n) ^ 2 ≤ (h * r ^ n) ^ 2 := by
      have hm := (sq_le_sq₀ (abs_nonneg (f n))
        (mul_nonneg hh (pow_nonneg hr0 n))).mpr (hf n)
      simpa only [sq_abs] using hm
    calc
      cosinePotential (f n) ≤ (987 / 100 : ℝ) * (f n) ^ 2 :=
        cosinePotential_le_quadratic ht
      _ ≤ (987 / 100 : ℝ) * (h * r ^ n) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = ((987 / 100 : ℝ) * h ^ 2) * (r ^ 2) ^ n := by
        simp only [mul_pow, ← pow_mul, Nat.mul_comm n 2]
        ring
  have hgeom' := hgeom.mul_left ((987 / 100 : ℝ) * h ^ 2)
  have hsum : Summable (fun n => cosinePotential (f n)) :=
    Summable.of_nonneg_of_le (fun n => cosinePotential_nonneg _) hmajor hgeom'
  refine ⟨hsum, ?_⟩
  calc
    (∑' n, cosinePotential (f n)) ≤
        ∑' n, ((987 / 100 : ℝ) * h ^ 2) * (r ^ 2) ^ n :=
      Summable.tsum_le_tsum hmajor hsum hgeom'
    _ = (987 / 100 : ℝ) * h ^ 2 / (1 - r ^ 2) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg r) hrsq]
      rfl

/-- Two small stable tails have total action below the exact
`2.75·10⁻⁴⁷` budget in the appendix.  The left tail starts at exponent one;
the first coefficient of the right tail occurs at exponent zero. -/
lemma small_stable_tail_action {r aMinus aPlus : ℝ}
    (hr0 : 0 ≤ r) (hrbound : r ≤ (1000 / 1883 : ℝ))
    (hMinus : |aMinus| ≤ (1 / 10 ^ 24 : ℝ))
    (hPlus : |aPlus| ≤ (1 / 10 ^ 24 : ℝ)) :
    Summable (fun n : ℕ => cosinePotential (aMinus * r ^ (n + 1))) ∧
    Summable (fun n : ℕ => cosinePotential (aPlus * r ^ n)) ∧
    ((∑' n : ℕ, cosinePotential (aMinus * r ^ (n + 1))) +
      ∑' n : ℕ, cosinePotential (aPlus * r ^ n)) < (275 / 10 ^ 49 : ℝ) := by
  have hr1 : r < 1 := by linarith
  have hleft : ∀ n : ℕ, |aMinus * r ^ (n + 1)| ≤ (1 / 10 ^ 24 : ℝ) * r ^ n := by
    intro n
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 _), pow_succ]
    calc
      |aMinus| * (r ^ n * r) ≤ (1 / 10 ^ 24 : ℝ) * (r ^ n * r) := by
        exact mul_le_mul_of_nonneg_right hMinus (mul_nonneg (pow_nonneg hr0 _) hr0)
      _ ≤ (1 / 10 ^ 24 : ℝ) * r ^ n := by
        nlinarith [pow_nonneg hr0 n]
  have hright : ∀ n : ℕ, |aPlus * r ^ n| ≤ (1 / 10 ^ 24 : ℝ) * r ^ n := by
    intro n
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 _)]
    exact mul_le_mul_of_nonneg_right hPlus (pow_nonneg hr0 _)
  have hl := cosinePotential_geometric_bound (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 24)
    (by norm_num : (1 / 10 ^ 24 : ℝ) ≤ 1 / 1000) hr0 hr1 hleft
  have hr := cosinePotential_geometric_bound (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 24)
    (by norm_num : (1 / 10 ^ 24 : ℝ) ≤ 1 / 1000) hr0 hr1 hright
  refine ⟨hl.1, hr.1, lt_of_le_of_lt (add_le_add hl.2 hr.2) ?_⟩
  have hr2 : r ^ 2 ≤ (1000 / 1883 : ℝ) ^ 2 := by nlinarith
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  have hnumeric :
      (2 * (987 / 100 : ℝ) * (1 / 10 ^ 24 : ℝ) ^ 2) <
        (275 / 10 ^ 49 : ℝ) * (1 - (1000 / 1883 : ℝ) ^ 2) := by norm_num
  have hnum :
      (2 * (987 / 100 : ℝ) * (1 / 10 ^ 24 : ℝ) ^ 2) <
        (275 / 10 ^ 49 : ℝ) * (1 - r ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hr2 1)
      (by norm_num : (0 : ℝ) ≤ 275 / 10 ^ 49)
    exact lt_of_lt_of_le hnumeric hm
  have hfrac := (div_lt_iff₀ hden).mpr hnum
  convert hfrac using 1
  ring

end Salem
