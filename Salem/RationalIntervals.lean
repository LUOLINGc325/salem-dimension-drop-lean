module

public import Mathlib
public import Salem.IntervalData

@[expose] public section

namespace Salem

namespace RationalInterval

def Contains (I : RationalInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

lemma add_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  dsimp [Contains, add] at *
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma neg_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  dsimp [Contains, neg] at *
  push_cast
  constructor <;> linarith [hx.1, hx.2]

lemma sub_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.sub J).Contains (x - y) := by
  dsimp [Contains, sub] at *
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Four corner bounds control a product for arbitrary signs of both intervals. -/
lemma mul_bounds_of_corners {a b c d x y lo hi : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d)
    (hlac : lo ≤ a * c) (hlad : lo ≤ a * d)
    (hlbc : lo ≤ b * c) (hlbd : lo ≤ b * d)
    (hacu : a * c ≤ hi) (hadu : a * d ≤ hi)
    (hbcu : b * c ≤ hi) (hbdu : b * d ≤ hi) :
    lo ≤ x * y ∧ x * y ≤ hi := by
  have hlxc : lo ≤ x * c := by
    by_cases hc : 0 ≤ c
    · exact hlac.trans (mul_le_mul_of_nonneg_right hax hc)
    · exact hlbc.trans (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hc))
  have hlxd : lo ≤ x * d := by
    by_cases hd : 0 ≤ d
    · exact hlad.trans (mul_le_mul_of_nonneg_right hax hd)
    · exact hlbd.trans (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hd))
  have hxcu : x * c ≤ hi := by
    by_cases hc : 0 ≤ c
    · exact (mul_le_mul_of_nonneg_right hxb hc).trans hbcu
    · exact (mul_le_mul_of_nonpos_right hax (le_of_not_ge hc)).trans hacu
  have hxdu : x * d ≤ hi := by
    by_cases hd : 0 ≤ d
    · exact (mul_le_mul_of_nonneg_right hxb hd).trans hbdu
    · exact (mul_le_mul_of_nonpos_right hax (le_of_not_ge hd)).trans hadu
  by_cases hx : 0 ≤ x
  · exact ⟨hlxc.trans (mul_le_mul_of_nonneg_left hcy hx),
      (mul_le_mul_of_nonneg_left hyd hx).trans hxdu⟩
  · exact ⟨hlxd.trans (mul_le_mul_of_nonpos_left hyd (le_of_not_ge hx)),
      (mul_le_mul_of_nonpos_left hcy (le_of_not_ge hx)).trans hxcu⟩

lemma mul_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x * y) := by
  apply mul_bounds_of_corners hx.1 hx.2 hy.1 hy.2
  · exact_mod_cast (min_le_left _ _).trans (min_le_left _ _)
  · exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)
  · exact_mod_cast (min_le_right _ _).trans (min_le_left _ _)
  · exact_mod_cast (min_le_right _ _).trans (min_le_right _ _)
  · exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)
  · exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)
  · exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
  · exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)

lemma contains_of_subset {I J : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) : J.Contains x := by
  have hlo' : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hhi
  exact ⟨hlo'.trans hx.1, hx.2.trans hhi'⟩

end RationalInterval

namespace ComplexRationalBox

def Contains (I : ComplexRationalBox) (z : ℂ) : Prop :=
  I.re.Contains z.re ∧ I.im.Contains z.im

lemma mul_contains {I J : ComplexRationalBox} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (I.mul J).Contains (z * w) := by
  constructor
  · simpa only [mul, Complex.mul_re] using
      RationalInterval.sub_contains (RationalInterval.mul_contains hz.1 hw.1)
        (RationalInterval.mul_contains hz.2 hw.2)
  · simpa only [mul, Complex.mul_im] using
      RationalInterval.add_contains (RationalInterval.mul_contains hz.1 hw.2)
        (RationalInterval.mul_contains hz.2 hw.1)

lemma square_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    I.square.Contains (z ^ 2) := by
  simpa only [square, pow_two] using mul_contains hz hz

lemma contains_of_subset {I J : ComplexRationalBox} {z : ℂ} (hz : I.Contains z)
    (hrelo : J.re.lo ≤ I.re.lo) (hrehi : I.re.hi ≤ J.re.hi)
    (himlo : J.im.lo ≤ I.im.lo) (himhi : I.im.hi ≤ J.im.hi) : J.Contains z :=
  ⟨RationalInterval.contains_of_subset hz.1 hrelo hrehi,
    RationalInterval.contains_of_subset hz.2 himlo himhi⟩

end ComplexRationalBox
end Salem

namespace Salem.RationalInterval

lemma round_contains {D : ℕ} (hD : 0 < D) {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : (I.round D).Contains x := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  apply contains_of_subset hx
  · exact (div_le_iff₀ hDq).mpr (Int.floor_le _)
  · exact (le_div_iff₀ hDq).mpr (Int.le_ceil _)

end Salem.RationalInterval

namespace Salem.ComplexRationalBox

lemma one_contains : one.Contains (1 : ℂ) := by
  constructor <;> norm_num [one, RationalInterval.Contains]

lemma round_contains {D : ℕ} (hD : 0 < D) {I : ComplexRationalBox} {z : ℂ}
    (hz : I.Contains z) : (I.round D).Contains z :=
  ⟨RationalInterval.round_contains hD hz.1, RationalInterval.round_contains hD hz.2⟩

lemma powRounded_contains {D : ℕ} (hD : 0 < D) {I : ComplexRationalBox} {z : ℂ}
    (hz : I.Contains z) (n : ℕ) : (I.powRounded D n).Contains (z ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [powRounded]
    split_ifs with hn hmod
    · subst n
      simpa only [pow_zero] using one_contains
    · have hhalf := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))
      have hs := round_contains hD (square_contains hhalf)
      convert hs using 1
      rw [← pow_mul]
      congr 1
      omega
    · have hhalf := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))
      have hs := round_contains hD (square_contains hhalf)
      have hm := round_contains hD (mul_contains hs hz)
      convert hm using 1
      rw [← pow_mul, ← pow_succ]
      congr 1
      omega

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

lemma point_contains (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

lemma inv_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x) (hlo : 0 < I.lo) :
    I.inv.Contains x⁻¹ := by
  have hloR : (0 : ℝ) < I.lo := by exact_mod_cast hlo
  have hx0 : 0 < x := hloR.trans_le hx.1
  constructor
  · simpa only [inv, Rat.cast_inv, one_div] using one_div_le_one_div_of_le hx0 hx.2
  · simpa only [inv, Rat.cast_inv, one_div] using one_div_le_one_div_of_le hloR hx.1

lemma sqrt_contains {D : ℕ} (hD : 0 < D) {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hlo : 0 ≤ I.lo) : (I.sqrt D).Contains (Real.sqrt x) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hloR : (0 : ℝ) ≤ I.lo := by exact_mod_cast hlo
  have hx0 : 0 ≤ x := hloR.trans hx.1
  let L : ℕ := ⌊I.lo * (D : ℚ) ^ 2⌋₊
  let U : ℕ := ⌈I.hi * (D : ℚ) ^ 2⌉₊
  have hL0 : (0 : ℝ) ≤ Nat.sqrt L := Nat.cast_nonneg _
  have hLsq : ((Nat.sqrt L : ℕ) : ℝ) ^ 2 ≤ (I.lo : ℝ) * (D : ℝ) ^ 2 := by
    have hs : ((Nat.sqrt L : ℕ) : ℚ) ^ 2 ≤ L := by exact_mod_cast Nat.sqrt_le' L
    have hf : (L : ℚ) ≤ I.lo * (D : ℚ) ^ 2 := Nat.floor_le (mul_nonneg hlo (sq_nonneg _))
    exact_mod_cast hs.trans hf
  have hUsq : (I.hi : ℝ) * (D : ℝ) ^ 2 < ((Nat.sqrt U + 1 : ℕ) : ℝ) ^ 2 := by
    have hc : I.hi * (D : ℚ) ^ 2 ≤ U := Nat.le_ceil _
    have hs : (U : ℚ) < ((Nat.sqrt U + 1 : ℕ) : ℚ) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' U
    exact_mod_cast hc.trans_lt hs
  have hsqrt := Real.sq_sqrt hx0
  have hprod0 : 0 ≤ Real.sqrt x * (D : ℝ) := mul_nonneg (Real.sqrt_nonneg _) hDr.le
  have hLo : (Nat.sqrt L : ℝ) ≤ Real.sqrt x * (D : ℝ) := by
    apply (sq_le_sq₀ hL0 hprod0).mp
    have hm := mul_le_mul_of_nonneg_right hx.1 (sq_nonneg (D : ℝ))
    nlinarith
  have hHi : Real.sqrt x * (D : ℝ) ≤ ((Nat.sqrt U + 1 : ℕ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hx.2 (sq_nonneg (D : ℝ))
    have hu0 : (0 : ℝ) ≤ ((Nat.sqrt U + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  constructor
  · dsimp only [sqrt]
    push_cast
    exact (div_le_iff₀ hDr).mpr hLo
  · dsimp only [sqrt]
    push_cast
    apply (le_div_iff₀ hDr).mpr
    simpa only [U, Nat.cast_add, Nat.cast_one] using hHi

end Salem.RationalInterval

namespace Salem.ComplexRationalBox

lemma add_contains {I J : ComplexRationalBox} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (I.add J).Contains (z + w) :=
  ⟨RationalInterval.add_contains hz.1 hw.1, RationalInterval.add_contains hz.2 hw.2⟩

lemma neg_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    I.neg.Contains (-z) := ⟨RationalInterval.neg_contains hz.1, RationalInterval.neg_contains hz.2⟩

lemma sub_contains {I J : ComplexRationalBox} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (I.sub J).Contains (z - w) :=
  ⟨RationalInterval.sub_contains hz.1 hw.1, RationalInterval.sub_contains hz.2 hw.2⟩

lemma conj_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    I.conj.Contains (star z) := ⟨hz.1, RationalInterval.neg_contains hz.2⟩

lemma ofRealInterval_contains {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    (ofRealInterval I).Contains (x : ℂ) := by
  constructor
  · exact hx
  · constructor <;> norm_num [ofRealInterval, RationalInterval.point]

lemma normSqInterval_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    I.normSqInterval.Contains (Complex.normSq z) := by
  exact RationalInterval.add_contains (RationalInterval.mul_contains hz.1 hz.1)
    (RationalInterval.mul_contains hz.2 hz.2)

lemma inv_contains {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z)
    (hlo : 0 < I.normSqInterval.lo) : I.inv.Contains z⁻¹ := by
  have hs := RationalInterval.inv_contains (normSqInterval_contains hz) hlo
  constructor
  · simpa only [inv, Complex.inv_re, div_eq_mul_inv] using RationalInterval.mul_contains hz.1 hs
  · simpa only [inv, Complex.inv_im, div_eq_mul_inv] using
      RationalInterval.mul_contains (RationalInterval.neg_contains hz.2) hs

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

lemma inv_contains_of_neg {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hhi : I.hi < 0) : I.inv.Contains x⁻¹ := by
  have hpos : 0 < I.neg.lo := by dsimp [neg]; linarith
  have h := neg_contains (inv_contains (neg_contains hx) hpos)
  simpa only [neg, inv, inv_neg, neg_neg] using h

end Salem.RationalInterval

namespace Salem.RationalInterval

lemma absUpper_nonneg (I : RationalInterval) : 0 ≤ I.absUpper :=
  (abs_nonneg I.lo).trans (le_max_left _ _)

lemma abs_le_absUpper {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.absUpper : ℝ) := by
  have hl : |(I.lo : ℝ)| ≤ (I.absUpper : ℝ) := by
    exact_mod_cast (show |I.lo| ≤ I.absUpper from le_max_left _ _)
  have hh : |(I.hi : ℝ)| ≤ (I.absUpper : ℝ) := by
    exact_mod_cast (show |I.hi| ≤ I.absUpper from le_max_right _ _)
  exact abs_le.mpr ⟨(abs_le.mp hl).1.trans hx.1, hx.2.trans (abs_le.mp hh).2⟩

end Salem.RationalInterval

namespace Salem.ComplexRationalBox

lemma norm_sq_le {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z) :
    ‖z‖ ^ 2 ≤ (I.normSqUpper : ℝ) := by
  have hxr : (0 : ℝ) ≤ I.re.absUpper := by exact_mod_cast I.re.absUpper_nonneg
  have hyr : (0 : ℝ) ≤ I.im.absUpper := by exact_mod_cast I.im.absUpper_nonneg
  have hx := (sq_le_sq₀ (abs_nonneg z.re) hxr).mpr (RationalInterval.abs_le_absUpper hz.1)
  have hy := (sq_le_sq₀ (abs_nonneg z.im) hyr).mpr (RationalInterval.abs_le_absUpper hz.2)
  simp only [sq_abs] at hx hy
  dsimp [normSqUpper]
  push_cast
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

lemma norm_lt {I : ComplexRationalBox} {z : ℂ} {ε : ℝ} (hz : I.Contains z)
    (hε : 0 < ε) (hbound : (I.normSqUpper : ℝ) < ε ^ 2) : ‖z‖ < ε := by
  have h := (norm_sq_le hz).trans_lt hbound
  nlinarith [norm_nonneg z]

lemma norm_pos {I : ComplexRationalBox} {z : ℂ} (hz : I.Contains z)
    (hzero : I.ExcludesZero) : 0 < ‖z‖ := by
  apply norm_pos_iff.mpr
  intro hz0
  subst z
  change I.re.Contains 0 ∧ I.im.Contains 0 at hz
  rcases hzero with h | h | h | h
  · have h' : (0 : ℝ) < I.re.lo := by exact_mod_cast h
    linarith [hz.1.1]
  · have h' : (I.re.hi : ℝ) < 0 := by exact_mod_cast h
    linarith [hz.1.2]
  · have h' : (0 : ℝ) < I.im.lo := by exact_mod_cast h
    linarith [hz.2.1]
  · have h' : (I.im.hi : ℝ) < 0 := by exact_mod_cast h
    linarith [hz.2.2]

end Salem.ComplexRationalBox

namespace Salem.RationalInterval

lemma powRounded_contains {D : ℕ} (hD : 0 < D) {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (n : ℕ) : (I.powRounded D n).Contains (x ^ n) := by
  have h := ComplexRationalBox.powRounded_contains hD
    (ComplexRationalBox.ofRealInterval_contains hx) n
  simpa only [powRounded, ← Complex.ofReal_pow, Complex.ofReal_re] using h.1

end Salem.RationalInterval
