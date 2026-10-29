module

public import Salem.MirrorAction

@[expose] public section

open scoped BigOperators
open Set Filter Topology

namespace Salem

/-- The paper's canonical representative in `[-1/2,1/2)`. -/
noncomputable def canonicalCenter (x : ℝ) : ℝ := x - (⌊x+1/2⌋ : ℤ)

/-- The canonical representative is unchanged by an actual integer translation. -/
theorem canonicalCenter_add_int (x : ℝ) (m : ℤ) : canonicalCenter (x+m) = canonicalCenter x := by
  unfold canonicalCenter
  rw [show x+(m : ℝ)+1/2 = (x+1/2)+m by ring, Int.floor_add_intCast]
  push_cast
  ring

/-- Integer-congruent actual coordinates have the same canonical representative. -/
theorem canonicalCenter_eq_of_int_congr (x y : ℝ) (h : ∃ m : ℤ, x-y = m) :
    canonicalCenter x = canonicalCenter y := by
  obtain ⟨m, hm⟩ := h
  have heq : x = y+m := by linarith
  rw [heq, canonicalCenter_add_int]

/-- Every strictly centered coordinate is its own canonical representative. -/
theorem canonicalCenter_eq_self_of_abs_lt_half (x : ℝ) (hx : |x| < (1/2 : ℝ)) :
    canonicalCenter x = x := by
  have hfloor : ⌊x+1/2⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr (by
    have h := abs_lt.mp hx
    constructor <;> linarith)
  unfold canonicalCenter
  rw [hfloor]
  simp

/-- Canonical representatives always lie in the paper's half-open centered interval. -/
theorem canonicalCenter_mem_Ico (x : ℝ) : canonicalCenter x ∈ Ico (-(1/2 : ℝ)) (1/2 : ℝ) := by
  have hlo := Int.floor_le (x+1/2)
  have hhi := Int.lt_floor_add_one (x+1/2)
  unfold canonicalCenter
  constructor <;> linarith

/-- Raw reciprocal trajectories preserve exact reciprocity under their true delayed
 difference. The reflection index increases by `L` and the sign flips, without parity. -/
theorem mirrorDifference_reciprocal (Y χ : ℤ → ℝ) (s L : ℤ) (σ : ℝ)
    (hY : ∀ j : ℤ, Y (s-j) = σ*(Y j-χ j)) :
    ∀ j : ℤ, mirrorDifference Y L (s+L-j) =
      (-σ)*(mirrorDifference Y L j-mirrorDifference χ L j) := by
  intro j
  have h0 := hY (j-L)
  have h1 := hY j
  unfold mirrorDifference
  rw [show s+L-j = s-(j-L) by ring,
    show s-(j-L)-L = s-j by ring, h0, h1]
  ring

/-- The outgoing neutral reflection flips at the new reflection index by exact
 difference algebra, preserving the actual oscillatory cancellation. -/
theorem mirrorDifference_neutral_reflection (χ : ℤ → ℝ) (s L : ℤ) (σ : ℝ)
    (hχ : ∀ j : ℤ, χ (s-j) = -σ*χ j) :
    ∀ j : ℤ, mirrorDifference χ L (s+L-j) = -(-σ)*mirrorDifference χ L j := by
  intro j
  have h0 := hχ (j-L)
  have h1 := hχ j
  unfold mirrorDifference
  rw [show s+L-j = s-(j-L) by ring,
    show s-(j-L)-L = s-j by ring, h0, h1]
  ring

/-- Translate raw reciprocal data to a core beginning at zero. -/
theorem reciprocal_affine_normalization (Y χ : ℤ → ℝ) (s a : ℤ) (σ : ℝ)
    (hY : ∀ j, Y (s-j) = σ*(Y j-χ j)) :
    ∀ j, Y (a+((s-2*a)-j)) = σ*(Y (a+j)-χ (a+j)) := by
  intro j
  rw [show a+((s-2*a)-j) = s-(a+j) by ring]
  exact hY (a+j)

/-- The normalized neutral coefficient has the exact physical phase shift. -/
theorem neutralMode_affine_normalization (z ζ : ℂ) (hζ : ζ ≠ 0) (a j : ℤ) :
    neutralMode z ζ (a+j) = neutralMode (z*ζ^a) ζ j := by
  unfold neutralMode
  rw [zpow_add₀ hζ, mul_assoc]

/-- The true mirror difference has the derived exact incoming exponential. -/
theorem mirrorDifference_incoming (Y : ℤ → ℝ) (b c : ℝ) (hb : b ≠ 0) (L : ℕ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j) (j : ℤ) (hj : j < 0) :
    mirrorDifference Y L j = (c*(1-b⁻¹^L))*b^j := by
  unfold mirrorDifference
  rw [hleft j hj, hleft (j-L) (by omega)]
  exact expanding_mirror_difference b c hb L j

/-- On the first core the true difference is exactly the old core minus its
 shifted incoming exponential. -/
theorem mirrorDifference_first_core (Y : ℤ → ℝ) (b c : ℝ) (ell L : ℕ) (hL : ell ≤ L)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j) (i : Fin ell) :
    mirrorDifference Y L i = Y i - c*b^((i : ℕ)-(L : ℤ)) := by
  unfold mirrorDifference
  rw [hleft (((i : ℕ) : ℤ)-(L : ℤ)) (by omega)]

/-- The bridge of the true delayed difference has its exact two stable pieces
 and full neutral wave. Its length is `L-ell`, independently of parity. -/
theorem mirrorDifference_bridge (Y : ℤ → ℝ) (b c σ : ℝ) (z ζ : ℂ) (ell L : ℕ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (j : ℤ) (hj0 : (ell : ℤ) ≤ j) (hjL : j < L) :
    mirrorDifference Y L j = σ*c*b^((ell : ℤ)-1-j) - c*b^(j-(L : ℤ)) + neutralMode z ζ j := by
  unfold mirrorDifference
  rw [hright j hj0, hleft (j-L) (by omega)]
  ring

/-- The raw second core is the reflected old core plus only the tiny shifted tail
 and the *new* neutral wave; the large old neutral terms cancel exactly. -/
theorem mirrorDifference_second_core (Y : ℤ → ℝ) (b c σ : ℝ) (z ζ : ℂ) (hζ : ζ ≠ 0)
    (ell L : ℕ) (hL : ell ≤ L)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (hrec : ∀ j : ℤ, Y ((ell : ℤ)-1-j) = σ*(Y j-neutralMode z ζ j))
    (hwrec : ∀ j : ℤ, neutralMode z ζ ((ell : ℤ)-1-j) = -σ*neutralMode z ζ j)
    (i : Fin ell) :
    mirrorDifference Y L ((L : ℤ)+(i : ℕ)) =
      σ*(-Y ((ell : ℤ)-1-(i : ℕ)) + c*b^((ell : ℤ)-1-(i : ℕ)-(L : ℤ)) +
        neutralMode (mirrorNeutralCoefficient z ζ L) ζ ((ell : ℤ)-1-(i : ℕ))) := by
  let t : ℤ := (ell : ℤ)-1-(i : ℕ)
  have hr := hrec t
  have hw := hwrec (t-(L : ℤ))
  have heq : (ell : ℤ)-1-t = (i : ℕ) := by dsimp [t]; ring
  have heq' : (ell : ℤ)-1-(t-(L : ℤ)) = (L : ℤ)+(i : ℕ) := by dsimp [t]; ring
  rw [heq] at hr
  rw [heq'] at hw
  unfold mirrorDifference
  rw [hright _ (by omega), show (L : ℤ)+(i : ℕ)-(L : ℤ) = (i : ℕ) by ring,
    hr, hw, ← neutralMode_mirror_difference z ζ hζ L]
  dsimp [t]
  ring

/-- Beyond the two actual cores, the true delayed difference has exactly the
 updated stable coefficient, opposite reciprocal sign, and new neutral mode. -/
theorem mirrorDifference_outgoing (Y : ℤ → ℝ) (b c σ : ℝ) (hb : b ≠ 0)
    (z ζ : ℂ) (hζ : ζ ≠ 0) (ell L : ℕ)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (j : ℤ) (hj : (ell : ℤ)+L ≤ j) :
    mirrorDifference Y L j =
      (-σ)*(c*(1-b⁻¹^L))*b^((ell : ℤ)-1+L-j) +
        neutralMode (mirrorNeutralCoefficient z ζ L) ζ j := by
  have hfactor : σ*c*b^((ell : ℤ)-1-j) - σ*c*b^((ell : ℤ)-1-(j-L)) =
      (-σ)*(c*(1-b⁻¹^L))*b^((ell : ℤ)-1+L-j) := by
    have heq := expanding_mirror_difference b c hb L ((ell : ℤ)-1+L-j)
    rw [show ((ell : ℤ)-1+L-j)-(L : ℤ) = (ell : ℤ)-1-j by ring] at heq
    calc
      _ = (-σ)*(c*b^((ell : ℤ)-1+L-j)-c*b^((ell : ℤ)-1-j)) := by
        rw [show (ell : ℤ)-1-(j-L) = (ell : ℤ)-1+L-j by ring]
        ring
      _ = _ := by rw [heq]; ring
  unfold mirrorDifference
  rw [hright j (by omega), hright (j-L) (by omega)]
  calc
    _ = (σ*c*b^((ell : ℤ)-1-j)-σ*c*b^((ell : ℤ)-1-(j-L))) +
        (neutralMode z ζ j-neutralMode z ζ (j-L)) := by ring
    _ = _ := by rw [hfactor, neutralMode_mirror_difference z ζ hζ L j]

/-- The actual incoming coefficient is multiplied by a strictly positive factor
 at every nonzero positive delay, and that factor is at most one. -/
theorem mirror_real_factor_bounds (b : ℝ) (hb : 1 < b) (L : ℕ) (hL : 0 < L) :
    0 < 1-b⁻¹^L ∧ 1-b⁻¹^L ≤ 1 := by
  have hr0 : 0 ≤ b⁻¹ := inv_nonneg.mpr (by linarith)
  have hr1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  have hp : b⁻¹^L < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  constructor
  · linarith
  · linarith [pow_nonneg hr0 L]

/-- The two actual exterior tails shrink under the derived incoming coefficient. -/
theorem mirror_real_tail_abs_le (b c : ℝ) (hb : 1 < b) (L : ℕ) (hL : 0 < L) (j : ℤ) :
    |(c*(1-b⁻¹^L))*b^j| ≤ |c*b^j| := by
  have hf := mirror_real_factor_bounds b hb L hL
  rw [mul_assoc, mul_comm (1-b⁻¹^L) (b^j), ← mul_assoc,
    abs_mul, abs_of_pos hf.1]
  exact (mul_le_mul_of_nonneg_left hf.2 (abs_nonneg _)).trans_eq (mul_one _)

/-- Localize a true reciprocal orbit by removing only its outgoing neutral term. -/
noncomputable def localizeReciprocalOrbit (b c σ : ℝ) (ell : ℕ) (Y : ℤ → ℝ) (j : ℤ) : ℝ :=
  if j < ell then Y j else σ*c*b^((ell : ℤ)-1-j)

/-- Exact core coordinates of the constructed bilateral profile. -/
theorem localizedProfile_core_apply (ell : ℕ) (Y : Fin ell → ℝ) (left right : ℕ → ℝ) (i : Fin ell) :
    localizedProfile ell Y left right i = Y i := by
  have heq : localizedProfileIndex ell (.inl i) = (i : ℕ) := rfl
  rw [← heq]
  unfold localizedProfile
  rw [Equiv.symm_apply_apply]
  rfl

/-- Exact incoming tail coordinates of the constructed bilateral profile. -/
theorem localizedProfile_left_apply (ell : ℕ) (Y : Fin ell → ℝ) (left right : ℕ → ℝ) (k : ℕ) :
    localizedProfile ell Y left right (-1-(k : ℤ)) = left k := by
  have heq : localizedProfileIndex ell (.inr (.inl k)) = -1-(k : ℤ) := rfl
  rw [← heq]
  unfold localizedProfile
  rw [Equiv.symm_apply_apply]
  rfl

/-- Exact outgoing tail coordinates of the constructed bilateral profile. -/
theorem localizedProfile_right_apply (ell : ℕ) (Y : Fin ell → ℝ) (left right : ℕ → ℝ) (k : ℕ) :
    localizedProfile ell Y left right ((ell : ℤ)+(k : ℤ)) = right k := by
  have heq : localizedProfileIndex ell (.inr (.inr k)) = (ell : ℤ)+(k : ℤ) := rfl
  rw [← heq]
  unfold localizedProfile
  rw [Equiv.symm_apply_apply]
  rfl

/-- The actual regional candidate, with the incoming and neutral coefficients
 derived from the old orbit and delay. Its second core is reflected and signed. -/
noncomputable def mirrorOrbitProfile (b c σ : ℝ) (z ζ : ℂ) (ell L : ℕ) (Y : ℤ → ℝ) : ℤ → ℝ :=
  mirrorReflectedLocalizedProfile ell (L-ell) (fun i => Y i)
    (fun i => -(c*b^((i : ℕ)-(L : ℤ))))
    (fun i => -(c*b^((i : ℕ)-(L : ℤ))) - neutralMode (mirrorNeutralCoefficient z ζ L) ζ i)
    (fun k => σ*c*b^(-1-(k : ℤ)))
    (fun k => -(c*b^((k : ℤ)-(L-ell : ℕ))))
    (z*ζ^(ell : ℤ)) ζ σ
    (fun k => (c*(1-b⁻¹^L))*b^(-1-(k : ℤ)))
    (fun k => (-σ)*(c*(1-b⁻¹^L))*b^(-1-(k : ℤ)))

/-- The actual candidate's first core has exactly the small shifted-tail correction. -/
theorem mirrorOrbitProfile_first_core (b c σ : ℝ) (z ζ : ℂ) (ell L : ℕ) (Y : ℤ → ℝ) (i : Fin ell) :
    mirrorOrbitProfile b c σ z ζ ell L Y i = Y i - c*b^((i : ℕ)-(L : ℤ)) := by
  unfold mirrorOrbitProfile mirrorReflectedLocalizedProfile
  change localizedProfile _ _ _ _ (((i.castAdd ((L-ell)+ell)) : Fin (ell+((L-ell)+ell))) : ℤ) = _
  rw [localizedProfile_core_apply]
  simp [mirrorCore, sub_eq_add_neg]

/-- Exact bridge coordinates of the actual reflected regional construction. -/
theorem mirrorOrbitProfile_gap (b c σ : ℝ) (z ζ : ℂ) (hζ : ζ ≠ 0)
    (ell L : ℕ) (Y : ℤ → ℝ) (k : Fin (L-ell)) :
    mirrorOrbitProfile b c σ z ζ ell L Y ((ell+(k : ℕ) : ℕ) : ℤ) =
      σ*c*b^(-1-(k : ℤ)) - c*b^((k : ℤ)-(L-ell : ℕ)) +
        neutralMode z ζ ((ell : ℤ)+(k : ℕ)) := by
  unfold mirrorOrbitProfile mirrorReflectedLocalizedProfile
  change localizedProfile _ _ _ _
    (((Fin.natAdd ell (k.castAdd ell)) : Fin (ell+((L-ell)+ell))) : ℤ) = _
  rw [localizedProfile_core_apply]
  simp only [mirrorCore, Fin.addCases_right, Fin.addCases_left]
  rw [neutralMode_affine_normalization z ζ hζ]
  simp only [neutralMode, zpow_natCast]
  ring

/-- Exact reflected second-core coordinates, with only the new small neutral mode. -/
theorem mirrorOrbitProfile_second_core (b c σ : ℝ) (z ζ : ℂ)
    (ell L : ℕ) (hL : ell ≤ L) (Y : ℤ → ℝ) (i : Fin ell) :
    mirrorOrbitProfile b c σ z ζ ell L Y ((L+(i : ℕ) : ℕ) : ℤ) =
      σ*(-Y i.rev + c*b^((i.rev : ℕ)-(L : ℤ)) +
        neutralMode (mirrorNeutralCoefficient z ζ L) ζ i.rev) := by
  have heq : L+(i : ℕ) = ell+((L-ell)+(i : ℕ)) := by omega
  rw [heq]
  unfold mirrorOrbitProfile mirrorReflectedLocalizedProfile
  change localizedProfile _ _ _ _
    (((Fin.natAdd ell (Fin.natAdd (L-ell) i)) : Fin (ell+((L-ell)+ell))) : ℤ) = _
  rw [localizedProfile_core_apply]
  simp only [mirrorCore, Fin.addCases_right]
  ring

/-- Exact incoming exterior of the actual mirror construction. -/
theorem mirrorOrbitProfile_left (b c σ : ℝ) (z ζ : ℂ) (ell L : ℕ)
    (Y : ℤ → ℝ) (k : ℕ) :
    mirrorOrbitProfile b c σ z ζ ell L Y (-1-(k : ℤ)) =
      (c*(1-b⁻¹^L))*b^(-1-(k : ℤ)) := by
  unfold mirrorOrbitProfile mirrorReflectedLocalizedProfile
  exact localizedProfile_left_apply _ _ _ _ k

/-- Exact outgoing localized exterior with the updated sign and coefficient. -/
theorem mirrorOrbitProfile_right (b c σ : ℝ) (z ζ : ℂ) (ell L : ℕ)
    (hL : ell ≤ L) (Y : ℤ → ℝ) (k : ℕ) :
    mirrorOrbitProfile b c σ z ζ ell L Y ((ell : ℤ)+L+k) =
      (-σ)*(c*(1-b⁻¹^L))*b^(-1-(k : ℤ)) := by
  have heq : (ell : ℤ)+L+k = (ell+((L-ell)+ell) : ℕ)+(k : ℤ) := by omega
  rw [heq]
  unfold mirrorOrbitProfile mirrorReflectedLocalizedProfile
  exact localizedProfile_right_apply _ _ _ _ k

/-- The explicitly constructed regional profile is exactly the localization of
 the true delayed-difference orbit. All arithmetic input is raw orbit data. -/
theorem mirrorOrbitProfile_eq_localized_difference (Y : ℤ → ℝ) (b c σ : ℝ)
    (hb : b ≠ 0) (z ζ : ℂ) (hζ : ζ ≠ 0) (ell L : ℕ) (hL : ell ≤ L)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (hrec : ∀ j : ℤ, Y ((ell : ℤ)-1-j) = σ*(Y j-neutralMode z ζ j))
    (hwrec : ∀ j : ℤ, neutralMode z ζ ((ell : ℤ)-1-j) = -σ*neutralMode z ζ j) :
    localizeReciprocalOrbit b (c*(1-b⁻¹^L)) (-σ) (ell+L) (mirrorDifference Y L) =
      mirrorOrbitProfile b c σ z ζ ell L Y := by
  funext j
  by_cases hj0 : j < 0
  · let k : ℕ := (-1-j).toNat
    have hk : j = -1-(k : ℤ) := by dsimp [k]; omega
    rw [hk, mirrorOrbitProfile_left]
    unfold localizeReciprocalOrbit
    rw [ite_eq_left (by omega)]
    exact mirrorDifference_incoming Y b c hb L hleft _ (by omega)
  by_cases hjell : j < ell
  · let i : Fin ell := ⟨j.toNat, by omega⟩
    have hi : (i : ℤ) = j := by dsimp [i]; omega
    unfold localizeReciprocalOrbit
    rw [ite_eq_left (by omega)]
    have hd := mirrorDifference_first_core Y b c ell L hL hleft i
    have hp := mirrorOrbitProfile_first_core b c σ z ζ ell L Y i
    rw [hi] at hd hp
    exact hd.trans hp.symm
  by_cases hjL : j < L
  · let k : Fin (L-ell) := ⟨(j-ell).toNat, by omega⟩
    have hk : (ell : ℤ)+(k : ℕ) = j := by dsimp [k]; omega
    unfold localizeReciprocalOrbit
    rw [ite_eq_left (by omega)]
    have hd := mirrorDifference_bridge Y b c σ z ζ ell L hleft hright j (by omega) hjL
    have hp := mirrorOrbitProfile_gap b c σ z ζ hζ ell L Y k
    simp only [Nat.cast_add] at hp
    rw [hk] at hp
    have he0 : (ell : ℤ)-1-j = -1-(k : ℤ) := by omega
    have he1 : j-(L : ℤ) = (k : ℤ)-(L-ell : ℕ) := by omega
    rw [he0, he1] at hd
    exact hd.trans hp.symm
  by_cases hjend : j < (ell : ℤ)+L
  · let i : Fin ell := ⟨(j-L).toNat, by omega⟩
    have hi : (L : ℤ)+(i : ℕ) = j := by dsimp [i]; omega
    have hrev : (i.rev : ℤ) = (ell : ℤ)-1-(i : ℕ) := by simp only [Fin.val_rev]; omega
    unfold localizeReciprocalOrbit
    rw [ite_eq_left (by omega)]
    have hd := mirrorDifference_second_core Y b c σ z ζ hζ ell L hL hright hrec hwrec i
    have hp := mirrorOrbitProfile_second_core b c σ z ζ ell L hL Y i
    simp only [Nat.cast_add] at hp
    rw [hi] at hd hp
    rw [hrev] at hp
    exact hd.trans hp.symm
  · let k : ℕ := (j-((ell : ℤ)+L)).toNat
    have hk : j = (ell : ℤ)+L+k := by dsimp [k]; omega
    rw [hk, mirrorOrbitProfile_right b c σ z ζ ell L hL]
    unfold localizeReciprocalOrbit
    rw [ite_eq_right (by omega)]
    congr 2
    push_cast
    ring

/-- The stable exponential's actual absolute value is its geometric envelope. -/
theorem reciprocalStableTail_abs (b c : ℝ) (hb : 0 < b) (k : ℕ) :
    |c*b^(-1-(k : ℤ))| = |c| * b⁻¹^(k+1) := by
  rw [show -1-(k : ℤ) = -((k+1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, abs_mul, abs_inv, abs_pow, abs_of_pos hb, inv_pow]

/-- Every actual exterior stable coordinate is bounded by the first tail radius. -/
theorem reciprocalStableTail_abs_le (b c h : ℝ) (hb : 1 < b) (hc : |c| ≤ h) (k : ℕ) :
    |c*b^(-1-(k : ℤ))| ≤ h*b⁻¹ := by
  have hr0 : 0 ≤ b⁻¹ := inv_nonneg.mpr (by linarith)
  have hr1 : b⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hb).le
  have hh : 0 ≤ h := (abs_nonneg c).trans hc
  rw [reciprocalStableTail_abs b c (by linarith)]
  apply (mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 _)).trans
  apply mul_le_mul_of_nonneg_left _ hh
  simpa only [pow_one] using (pow_le_pow_of_le_one hr0 hr1 (show 1 ≤ k+1 by omega))

/-- The actual mirror bridge stays inside the sum of the old neutral radius and
 the two first stable-tail radii. -/
theorem mirrorOrbitProfile_gap_bound (b c h σ : ℝ) (hb : 1 < b) (hc : |c| ≤ h)
    (hσ : σ = 1 ∨ σ = -1) (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (Δ : ℝ) (hz : ‖z‖ ≤ Δ)
    (ell L : ℕ) (k : Fin (L-ell)) :
    |σ*c*b^(-1-(k : ℤ)) - c*b^((k : ℤ)-(L-ell : ℕ)) +
      ((z*ζ^(ell : ℤ))*ζ^(k : ℕ)).re| ≤ Δ+2*h*b⁻¹ := by
  have hX : |σ*c*b^(-1-(k : ℤ))| ≤ h*b⁻¹ := by
    rcases hσ with rfl | rfl <;> simpa only [one_mul, neg_one_mul, neg_mul, abs_neg] using
      reciprocalStableTail_abs_le b c h hb hc k
  have he : (k : ℤ)-(L-ell : ℕ) = -1-((L-ell-1-(k : ℕ) : ℕ) : ℤ) := by omega
  have hZ : |c*b^((k : ℤ)-(L-ell : ℕ))| ≤ h*b⁻¹ := by
    rw [he]
    exact reciprocalStableTail_abs_le b c h hb hc _
  have hW : |((z*ζ^(ell : ℤ))*ζ^(k : ℕ)).re| ≤ Δ := by
    have h := (abs_neutralMode_le (z*ζ^(ell : ℤ)) ζ hζ (k : ℕ))
    simpa only [neutralMode, zpow_natCast, norm_mul, norm_zpow, hζ, one_zpow, mul_one] using h.trans (by simpa [norm_mul, norm_zpow, hζ] using hz)
  have ht := abs_add_le (σ*c*b^(-1-(k : ℤ))-c*b^((k : ℤ)-(L-ell : ℕ)))
    (((z*ζ^(ell : ℤ))*ζ^(k : ℕ)).re)
  have ht' : |σ*c*b^(-1-(k : ℤ))-c*b^((k : ℤ)-(L-ell : ℕ))| ≤
      |σ*c*b^(-1-(k : ℤ))|+|c*b^((k : ℤ)-(L-ell : ℕ))| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (σ*c*b^(-1-(k : ℤ))) (-(c*b^((k : ℤ)-(L-ell : ℕ))))
  linarith

/-- The exact updated incoming coefficient cannot increase in absolute value. -/
theorem mirror_coefficient_abs_le (b c : ℝ) (hb : 1 < b) (L : ℕ) (hL : 0 < L) :
    |c*(1-b⁻¹^L)| ≤ |c| := by
  simpa only [zpow_zero, mul_one] using mirror_real_tail_abs_le b c hb L hL 0

/-- A genuine nonzero incoming frequency stays nonzero after a positive mirror delay. -/
theorem mirror_coefficient_ne_zero (b c : ℝ) (hb : 1 < b) (hc : c ≠ 0)
    (L : ℕ) (hL : 0 < L) : c*(1-b⁻¹^L) ≠ 0 :=
  mul_ne_zero hc (ne_of_gt (mirror_real_factor_bounds b hb L hL).1)

/-- The constructed actual mirror profile has the source minimum strict margin,
 with all perturbation, bridge, and exterior bounds derived from the old orbit. -/
theorem mirrorOrbitProfile_margin (b c h σ : ℝ) (hb : 1 < b) (hc : |c| ≤ h)
    (hσ : σ = 1 ∨ σ = -1) (z ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (Δ Δplus θ : ℝ) (hz : ‖z‖ ≤ Δ) (hΔplus : 0 ≤ Δplus)
    (ell L : ℕ) (hzplus : ‖mirrorNeutralCoefficient z ζ L‖ ≤ Δplus)
     (hL : ell ≤ L) (hLpos : 0 < L) (Y : ℤ → ℝ)
    (hY : ∀ i : Fin ell, |Y i| ≤ (1/2 : ℝ)-θ) :
    ∀ j : ℤ, |mirrorOrbitProfile b c σ z ζ ell L Y j| ≤
      (1/2 : ℝ)-min (θ-Δplus-h*b⁻¹^(L-ell+1))
        (min ((1/2 : ℝ)-(Δ+2*h*b⁻¹)) ((1/2 : ℝ)-h*b⁻¹)) := by
  unfold mirrorOrbitProfile
  refine mirrorReflectedLocalizedProfile_margin ell (L-ell) _ _ _ _ _ _ _ σ hσ _ _
    θ (h*b⁻¹^(L-ell+1)) Δplus (Δ+2*h*b⁻¹) (h*b⁻¹) hΔplus hY ?_ ?_ ?_ ?_ ?_
  · intro i
    exact (mirror_core_perturbation_bounds b c h hb hc ell L hL z ζ hζ Δplus hzplus i).1
  · intro i
    exact (mirror_core_perturbation_bounds b c h hb hc ell L hL z ζ hζ Δplus hzplus i).2
  · intro i
    exact mirrorOrbitProfile_gap_bound b c h σ hb hc hσ z ζ hζ Δ hz ell L i
  · intro k
    exact (mirror_real_tail_abs_le b c hb L hLpos _).trans
      (reciprocalStableTail_abs_le b c h hb hc k)
  · intro k
    have ht := (mirror_real_tail_abs_le b c hb L hLpos (-1-(k : ℤ))).trans
      (reciprocalStableTail_abs_le b c h hb hc k)
    rcases hσ with rfl | rfl <;> simpa only [neg_mul, one_mul, neg_neg, abs_neg] using ht

/-- The true delayed orbit is strictly centered once its constructed localized
 profile and its actual outgoing stable-plus-neutral exterior are strictly centered. -/
theorem mirrorDifference_abs_lt_half (Y : ℤ → ℝ) (b c h σ : ℝ)
    (hb : 1 < b) (hc : |c| ≤ h) (hσ : σ = 1 ∨ σ = -1)
    (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (Δplus : ℝ) (ell L : ℕ)
    (hL : ell ≤ L) (hLpos : 0 < L)
    (hzplus : ‖mirrorNeutralCoefficient z ζ L‖ ≤ Δplus)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (hrec : ∀ j : ℤ, Y ((ell : ℤ)-1-j) = σ*(Y j-neutralMode z ζ j))
    (hwrec : ∀ j : ℤ, neutralMode z ζ ((ell : ℤ)-1-j) = -σ*neutralMode z ζ j)
    (hprofile : ∀ j : ℤ, |mirrorOrbitProfile b c σ z ζ ell L Y j| < (1/2 : ℝ))
    (hout : h*b⁻¹+Δplus < (1/2 : ℝ)) :
    ∀ j : ℤ, |mirrorDifference Y L j| < (1/2 : ℝ) := by
  have hb0 : b ≠ 0 := ne_of_gt (by linarith)
  have hζ0 : ζ ≠ 0 := by intro hz; simp [hz] at hζ
  have heq := mirrorOrbitProfile_eq_localized_difference Y b c σ hb0 z ζ hζ0 ell L hL
    hleft hright hrec hwrec
  intro j
  by_cases hj : j < (ell : ℤ)+L
  · have hid := congrFun heq j
    unfold localizeReciprocalOrbit at hid
    rw [ite_eq_left (by push_cast; exact hj)] at hid
    rw [hid]
    exact hprofile j
  · let k : ℕ := (j-((ell : ℤ)+L)).toNat
    have hk : (ell : ℤ)-1+L-j = -1-(k : ℤ) := by dsimp [k]; omega
    have ht : |(-σ)*(c*(1-b⁻¹^L))*b^((ell : ℤ)-1+L-j)| ≤ h*b⁻¹ := by
      have hcp := (mirror_coefficient_abs_le b c hb L hLpos).trans hc
      have hs := reciprocalStableTail_abs_le b (c*(1-b⁻¹^L)) h hb hcp k
      rw [hk]
      rcases hσ with rfl | rfl <;> simpa only [neg_mul, one_mul, neg_neg, abs_neg] using hs
    have hw := (abs_neutralMode_le (mirrorNeutralCoefficient z ζ L) ζ hζ j).trans hzplus
    rw [mirrorDifference_outgoing Y b c σ hb0 z ζ hζ0 ell L hright j (by omega)]
    exact (abs_add_le _ _).trans_lt (by linarith)

/-- Actual integer congruence plus proved strict centering identifies the true
 delayed difference with the canonical Fourier trajectory at the derived frequency. -/
theorem mirrorDifference_eq_canonical_expanding (b c : ℝ) (hb : b ≠ 0) (Y : ℤ → ℝ) (L : ℕ)
    (hY : ∀ j : ℤ, ∃ m : ℤ, Y j-c*b^j = m)
    (hcenter : ∀ j : ℤ, |mirrorDifference Y L j| < (1/2 : ℝ)) :
    ∀ j : ℤ, mirrorDifference Y L j = canonicalCenter ((c*(1-b⁻¹^L))*b^j) := by
  intro j
  calc
    _ = canonicalCenter (mirrorDifference Y L j) :=
      (canonicalCenter_eq_self_of_abs_lt_half _ (hcenter j)).symm
    _ = _ := canonicalCenter_eq_of_int_congr _ _
      (mirrorDifference_congruent_expanding b c hb Y L hY j)

/-- An actual incoming exponential and reciprocal stable exterior give the
 concrete localized profile; no forcing assertion is imposed on that localization. -/
theorem localizeReciprocalOrbit_eq_profile (Y : ℤ → ℝ) (b c σ : ℝ) (ell : ℕ)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j) :
    localizeReciprocalOrbit b c σ ell Y = localizedProfile ell (fun i => Y i)
      (fun k => c*b^(-1-(k : ℤ))) (fun k => σ*c*b^(-1-(k : ℤ))) := by
  funext j
  by_cases hj0 : j < 0
  · let k := (-1-j).toNat
    have hk : j = -1-(k : ℤ) := by dsimp [k]; omega
    rw [hk, localizedProfile_left_apply]
    unfold localizeReciprocalOrbit
    rw [ite_eq_left (by omega)]
    exact hleft _ (by omega)
  by_cases hjell : j < ell
  · let i : Fin ell := ⟨j.toNat, by omega⟩
    have hi : (i : ℤ) = j := by dsimp [i]; omega
    rw [← hi, localizedProfile_core_apply]
    exact ite_eq_left (by omega)
  · let k := (j-ell).toNat
    have hk : j = (ell : ℤ)+(k : ℤ) := by dsimp [k]; omega
    rw [hk, localizedProfile_right_apply]
    unfold localizeReciprocalOrbit
    rw [ite_eq_right (by omega)]
    congr 2
    ring

/-- The old actual localized action equals its finite core action plus twice the
 actual stable-tail action, with summability proved by explicit bilateral indexing. -/
theorem localizeReciprocalOrbit_action_hasSum (Y : ℤ → ℝ) (b c σ : ℝ) (ell : ℕ)
    (hσ : σ = 1 ∨ σ = -1) (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j)
    (htail : Summable (fun k : ℕ => cosinePotential (c*b^(-1-(k : ℤ))))) :
    HasSum (fun j : ℤ => cosinePotential (localizeReciprocalOrbit b c σ ell Y j))
      ((∑ i : Fin ell, cosinePotential (Y i))+
        2*(∑' k : ℕ, cosinePotential (c*b^(-1-(k : ℤ))))) := by
  rw [localizeReciprocalOrbit_eq_profile Y b c σ ell hleft]
  have hright : HasSum (fun k : ℕ => cosinePotential (σ*c*b^(-1-(k : ℤ))))
      (∑' k : ℕ, cosinePotential (c*b^(-1-(k : ℤ)))) := by
    rcases hσ with rfl | rfl <;> simpa [cosinePotential] using htail.hasSum
  have h := localizedProfile_action_hasSum ell (fun i => Y i)
    (fun k => c*b^(-1-(k : ℤ))) (fun k => σ*c*b^(-1-(k : ℤ)))
    _ _ htail.hasSum hright
  convert h using 1
  ring

/-- The actual constructed mirror localization has the source action bound.
 Its baseline is the actual old core plus its two actual stable tails. -/
theorem mirrorOrbitProfile_action_le (Y : ℤ → ℝ) (b c h σ : ℝ)
    (hb : 1 < b) (hc : |c| ≤ h) (hσ : σ = 1 ∨ σ = -1)
    (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (hne : 1-ζ^2 ≠ 0)
    (Δ Δplus Rcore Rgap : ℝ) (hz : ‖z‖ ≤ Δ) (hΔplus : 0 ≤ Δplus)
    (ell L : ℕ) (hzplus : ‖mirrorNeutralCoefficient z ζ L‖ ≤ Δplus)
    (hL : ell ≤ L) (hLpos : 0 < L)
    (htail : Summable (fun k : ℕ => cosinePotential (c*b^(-1-(k : ℤ)))))
    (htailRadius : h*b⁻¹ < (1/2 : ℝ))
    (hRc0 : 0 ≤ Rcore) (hRc : Rcore < (1/2 : ℝ))
    (hcore : ∀ i : Fin ell, |Y i|+h*b⁻¹^(L-ell+1)+Δplus ≤ Rcore)
    (hRg0 : 0 ≤ Rgap) (hRg : Rgap < (1/2 : ℝ)) (hU : Δ+2*h*b⁻¹ ≤ Rgap) :
    Summable (fun j : ℤ => cosinePotential (mirrorOrbitProfile b c σ z ζ ell L Y j)) ∧
    (∑' j : ℤ, cosinePotential (mirrorOrbitProfile b c σ z ζ ell L Y j)) ≤
      2*((∑ i : Fin ell, cosinePotential (Y i))+
        2*(∑' k : ℕ, cosinePotential (c*b^(-1-(k : ℤ))))) +
      (∑ i : Fin ell, |cosinePotentialSlope (Y i)|)*(Δplus+2*(h*b⁻¹^(L-ell+1))) +
      cosineCurvatureBound Rcore*(ell : ℝ)*(Δplus+h*b⁻¹^(L-ell+1))^2 +
      cosineCurvatureBound Rgap*(h^2*(L-ell : ℕ)*b⁻¹^((L-ell)+1) +
        2*Δ*h*b⁻¹/(1-b⁻¹) + Δ^2*((L-ell : ℕ)/4 + 1/(2*‖1-ζ^2‖))) := by
  let g := L-ell
  let r := b⁻¹
  let ρ := h*r^(g+1)
  let Y0 : Fin ell → ℝ := fun i => Y i
  let u : Fin ell → ℝ := fun i => -(c*b^((i : ℕ)-(L : ℤ)))
  let v : Fin ell → ℝ := fun i => -(c*b^((i : ℕ)-(L : ℤ))) -
    neutralMode (mirrorNeutralCoefficient z ζ L) ζ i
  let old : ℕ → ℝ := fun k => c*b^(-1-(k : ℤ))
  let left : ℕ → ℝ := fun k => (c*(1-b⁻¹^L))*b^(-1-(k : ℤ))
  let right : ℕ → ℝ := fun k => (-σ)*(c*(1-b⁻¹^L))*b^(-1-(k : ℤ))
  let X : ℕ → ℝ := fun k => σ*c*b^(-1-(k : ℤ))
  let Z : ℕ → ℝ := fun k => -(c*b^((k : ℤ)-(L-ell : ℕ)))
  let a : ℂ := z*ζ^(ell : ℤ)
  have hh : 0 ≤ h := (abs_nonneg c).trans hc
  have hr0 : 0 ≤ r := inv_nonneg.mpr (by linarith)
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hb
  have hρ : 0 ≤ ρ := mul_nonneg hh (pow_nonneg hr0 _)
  have holdCenter (k : ℕ) : |old k| < (1/2 : ℝ) :=
    (reciprocalStableTail_abs_le b c h hb hc k).trans_lt htailRadius
  have hleft (k : ℕ) : |left k| ≤ |old k| := mirror_real_tail_abs_le b c hb L hLpos _
  have hright (k : ℕ) : |right k| ≤ |old k| := by
    have ht := hleft k
    rcases hσ with rfl | rfl <;> simpa only [right, left, neg_mul, one_mul, neg_neg, abs_neg] using ht
  have holdBound (k : ℕ) : |old k| ≤ h*r^(k+1) := by
    rw [reciprocalStableTail_abs b c (by linarith)]
    exact mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 _)
  have hX (k : ℕ) (_hk : k < g) : |X k| = |old k| := by
    rcases hσ with rfl | rfl <;> simp [X, old]
  have hZ (k : ℕ) (hk : k < g) : |Z k| = |old (g-1-k)| := by
    have he : (k : ℤ)-(L-ell : ℕ) = -1-((g-1-k : ℕ) : ℤ) := by dsimp [g] at *; omega
    dsimp [Z, old]
    rw [abs_neg, he]
  have ha : ‖a‖ ≤ Δ := by simpa [a, norm_mul, norm_zpow, hζ] using hz
  have hu (i : Fin ell) : |u i| ≤ ρ :=
    (mirror_core_perturbation_bounds b c h hb hc ell L hL z ζ hζ Δplus hzplus i).1
  have hv (i : Fin ell) : |v i| ≤ ρ+Δplus :=
    (mirror_core_perturbation_bounds b c h hb hc ell L hL z ζ hζ Δplus hzplus i).2
  have hY (i : Fin ell) : |Y0 i| ≤ Rcore := by
    have hi := hcore i
    change |Y i|+ρ+Δplus ≤ Rcore at hi
    exact le_trans (by linarith) hi
  have hYu (i : Fin ell) : |Y0 i+u i| ≤ Rcore := by
    have hi := hcore i
    change |Y0 i|+ρ+Δplus ≤ Rcore at hi
    exact (abs_add_le _ _).trans (by linarith [hu i])
  have hYv (i : Fin ell) : |Y0 i+v i| ≤ Rcore := by
    have hi := hcore i
    change |Y0 i|+ρ+Δplus ≤ Rcore at hi
    exact (abs_add_le _ _).trans (by linarith [hv i])
  have hanalytic := mirrorLocalizedProfile_action_le ell g Y0 u v old left right X Z a ζ
    h r Δ ρ Δplus Rcore Rgap htail holdCenter hleft hright hh hr0 hr1 holdBound hX hZ
    ha hζ hne hρ hΔplus hRc0 hRc hY hYu hYv hu hv hRg0 hRg hU
  have hleftSum := (tail_action_mono_abs old left htail holdCenter hleft).1
  have hrightSum := (tail_action_mono_abs old right htail holdCenter hright).1
  have hreflected := mirrorReflectedLocalizedProfile_action_eq ell g Y0 u v X Z a ζ σ hσ
    left right hleftSum hrightSum
  exact ⟨hreflected.1, hreflected.2.trans_le hanalytic.2⟩

/-- The source action bound now applies to the localization of the TRUE delayed
 difference, with its baseline equal to the TRUE old localized action. -/
theorem mirrorDifference_localized_action_le (Y : ℤ → ℝ) (b c h σ : ℝ)
    (hb : 1 < b) (hc : |c| ≤ h) (hσ : σ = 1 ∨ σ = -1)
    (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (hne : 1-ζ^2 ≠ 0)
    (Δ Δplus Rcore Rgap : ℝ) (hz : ‖z‖ ≤ Δ) (hΔplus : 0 ≤ Δplus)
    (ell L : ℕ) (hzplus : ‖mirrorNeutralCoefficient z ζ L‖ ≤ Δplus)
    (hL : ell ≤ L) (hLpos : 0 < L)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (hrec : ∀ j : ℤ, Y ((ell : ℤ)-1-j) = σ*(Y j-neutralMode z ζ j))
    (hwrec : ∀ j : ℤ, neutralMode z ζ ((ell : ℤ)-1-j) = -σ*neutralMode z ζ j)
    (htail : Summable (fun k : ℕ => cosinePotential (c*b^(-1-(k : ℤ)))))
    (htailRadius : h*b⁻¹ < (1/2 : ℝ))
    (hRc0 : 0 ≤ Rcore) (hRc : Rcore < (1/2 : ℝ))
    (hcore : ∀ i : Fin ell, |Y i|+h*b⁻¹^(L-ell+1)+Δplus ≤ Rcore)
    (hRg0 : 0 ≤ Rgap) (hRg : Rgap < (1/2 : ℝ)) (hU : Δ+2*h*b⁻¹ ≤ Rgap) :
    Summable (fun j : ℤ => cosinePotential (localizeReciprocalOrbit b (c*(1-b⁻¹^L)) (-σ) (ell+L) (mirrorDifference Y L) j)) ∧
    (∑' j : ℤ, cosinePotential (localizeReciprocalOrbit b (c*(1-b⁻¹^L)) (-σ) (ell+L) (mirrorDifference Y L) j)) ≤
      2*(∑' j : ℤ, cosinePotential (localizeReciprocalOrbit b c σ ell Y j)) +
      (∑ i : Fin ell, |cosinePotentialSlope (Y i)|)*(Δplus+2*(h*b⁻¹^(L-ell+1))) +
      cosineCurvatureBound Rcore*(ell : ℝ)*(Δplus+h*b⁻¹^(L-ell+1))^2 +
      cosineCurvatureBound Rgap*(h^2*(L-ell : ℕ)*b⁻¹^((L-ell)+1) +
        2*Δ*h*b⁻¹/(1-b⁻¹) + Δ^2*((L-ell : ℕ)/4 + 1/(2*‖1-ζ^2‖))) := by
  have hb0 : b ≠ 0 := ne_of_gt (by linarith)
  have hζ0 : ζ ≠ 0 := by intro hz; simp [hz] at hζ
  have hid := mirrorOrbitProfile_eq_localized_difference Y b c σ hb0 z ζ hζ0 ell L hL
    hleft hright hrec hwrec
  have hold := localizeReciprocalOrbit_action_hasSum Y b c σ ell hσ hleft htail
  have hnew := mirrorOrbitProfile_action_le Y b c h σ hb hc hσ z ζ hζ hne
    Δ Δplus Rcore Rgap hz hΔplus ell L hzplus hL hLpos htail htailRadius
    hRc0 hRc hcore hRg0 hRg hU
  rw [← hid, ← hold.tsum_eq] at hnew
  exact hnew

/-- The new raw orbit has exactly the normalized reciprocity required for the
 next mirror, with reflection index `ell+L-1` and opposite sign. -/
theorem mirrorDifference_reciprocal_mode (Y : ℤ → ℝ) (z ζ : ℂ) (hζ : ζ ≠ 0)
    (ell L : ℕ) (σ : ℝ)
    (hrec : ∀ j : ℤ, Y ((ell : ℤ)-1-j) = σ*(Y j-neutralMode z ζ j)) :
    ∀ j : ℤ, mirrorDifference Y L ((ell+L : ℕ)-1-j) =
      (-σ)*(mirrorDifference Y L j-neutralMode (mirrorNeutralCoefficient z ζ L) ζ j) := by
  intro j
  have h := mirrorDifference_reciprocal Y (neutralMode z ζ) ((ell : ℤ)-1) L σ hrec j
  simp only [mirrorDifference, neutralMode_mirror_difference z ζ hζ] at h
  have he : ((ell+L : ℕ) : ℤ)-1-j = (ell : ℤ)-1+(L : ℤ)-j := by omega
  rw [he]
  exact h

/-- The derived neutral coefficient satisfies the exact normalized reflection
 needed at the next mirror, without an independently assumed wave phase. -/
theorem mirrorNeutralCoefficient_reflection (z ζ : ℂ) (hζ : ζ ≠ 0)
    (ell L : ℕ) (σ : ℝ)
    (hwrec : ∀ j : ℤ, neutralMode z ζ ((ell : ℤ)-1-j) = -σ*neutralMode z ζ j) :
    ∀ j : ℤ, neutralMode (mirrorNeutralCoefficient z ζ L) ζ ((ell+L : ℕ)-1-j) =
      -(-σ)*neutralMode (mirrorNeutralCoefficient z ζ L) ζ j := by
  intro j
  have h := mirrorDifference_neutral_reflection (neutralMode z ζ) ((ell : ℤ)-1) L σ hwrec j
  simp only [mirrorDifference, neutralMode_mirror_difference z ζ hζ] at h
  have he : ((ell+L : ℕ) : ℤ)-1-j = (ell : ℤ)-1+(L : ℤ)-j := by omega
  rw [he]
  exact h

/-- The actual stable tail after a mirror remains summable in action, so the
 next mirror inherits the old tail input rather than assuming a fresh certificate. -/
theorem mirrorStableTail_action_mono (b c h : ℝ) (hb : 1 < b) (hc : |c| ≤ h)
    (L : ℕ) (hL : 0 < L) (hsmall : h*b⁻¹ < (1/2 : ℝ))
    (htail : Summable (fun k : ℕ => cosinePotential (c*b^(-1-(k : ℤ))))) :
    Summable (fun k : ℕ => cosinePotential ((c*(1-b⁻¹^L))*b^(-1-(k : ℤ)))) ∧
    (∑' k : ℕ, cosinePotential ((c*(1-b⁻¹^L))*b^(-1-(k : ℤ)))) ≤
      ∑' k : ℕ, cosinePotential (c*b^(-1-(k : ℤ))) := by
  exact tail_action_mono_abs _ _ htail
    (fun k => (reciprocalStableTail_abs_le b c h hb hc k).trans_lt hsmall)
    (fun k => mirror_real_tail_abs_le b c hb L hL (-1-(k : ℤ)))

/-- The actual seed data and scalar safety margins construct the canonical
 Fourier mirror orbit, its strict centering, and the exact localized boundary margin.
 No desired new action or canonical-orbit identity is assumed. -/
theorem mirrorDifference_canonical_of_seed_data (Y : ℤ → ℝ) (b c h σ : ℝ)
    (hb : 1 < b) (hc : |c| ≤ h) (hσ : σ = 1 ∨ σ = -1)
    (z ζ : ℂ) (hζ : ‖ζ‖ = 1) (Δ Δplus θ : ℝ)
    (hz : ‖z‖ ≤ Δ) (hΔplus : 0 ≤ Δplus) (ell L : ℕ)
    (hzplus : ‖mirrorNeutralCoefficient z ζ L‖ ≤ Δplus)
    (hL : ell ≤ L) (hLpos : 0 < L)
    (hleft : ∀ j : ℤ, j < 0 → Y j = c*b^j)
    (hright : ∀ j : ℤ, (ell : ℤ) ≤ j →
      Y j = σ*c*b^((ell : ℤ)-1-j)+neutralMode z ζ j)
    (hrec : ∀ j : ℤ, Y ((ell : ℤ)-1-j) = σ*(Y j-neutralMode z ζ j))
    (hwrec : ∀ j : ℤ, neutralMode z ζ ((ell : ℤ)-1-j) = -σ*neutralMode z ζ j)
    (hcongr : ∀ j : ℤ, ∃ m : ℤ, Y j-c*b^j = m)
    (hcore : ∀ i : Fin ell, |Y i| ≤ (1/2 : ℝ)-θ)
    (hmargin : 0 < min (θ-Δplus-h*b⁻¹^(L-ell+1))
      (min ((1/2 : ℝ)-(Δ+2*h*b⁻¹)) ((1/2 : ℝ)-h*b⁻¹)))
    (hout : h*b⁻¹+Δplus < (1/2 : ℝ)) :
    (∀ j : ℤ, mirrorDifference Y L j = canonicalCenter ((c*(1-b⁻¹^L))*b^j)) ∧
    (∀ j : ℤ, |mirrorDifference Y L j| < (1/2 : ℝ)) ∧
    (∀ j : ℤ, |localizeReciprocalOrbit b (c*(1-b⁻¹^L)) (-σ) (ell+L)
      (mirrorDifference Y L) j| ≤
      (1/2 : ℝ)-min (θ-Δplus-h*b⁻¹^(L-ell+1))
        (min ((1/2 : ℝ)-(Δ+2*h*b⁻¹)) ((1/2 : ℝ)-h*b⁻¹))) := by
  have hb0 : b ≠ 0 := ne_of_gt (by linarith)
  have hζ0 : ζ ≠ 0 := by intro hz; simp [hz] at hζ
  have hm := mirrorOrbitProfile_margin b c h σ hb hc hσ z ζ hζ Δ Δplus θ hz hΔplus
    ell L hzplus hL hLpos Y hcore
  have hprofile (j : ℤ) : |mirrorOrbitProfile b c σ z ζ ell L Y j| < (1/2 : ℝ) :=
    (hm j).trans_lt (by linarith)
  have hcenter := mirrorDifference_abs_lt_half Y b c h σ hb hc hσ z ζ hζ Δplus ell L
    hL hLpos hzplus hleft hright hrec hwrec hprofile hout
  refine ⟨mirrorDifference_eq_canonical_expanding b c hb0 Y L hcongr hcenter, hcenter, ?_⟩
  rw [mirrorOrbitProfile_eq_localized_difference Y b c σ hb0 z ζ hζ0 ell L hL
    hleft hright hrec hwrec]
  exact hm

end Salem
