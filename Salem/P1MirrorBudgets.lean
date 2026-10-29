module

public import Salem.MirrorAction

@[expose] public section

open scoped BigOperators

namespace Salem

/-- The first reflected core may use the relaxed freshly certified action
24.367 while retaining its source derivative bound. -/
theorem mirror_second_core_slope_sum_lt_relaxed (Y : Fin 151 → ℝ)
    (hY : ∀ i, |Y i| ≤ (211/500 : ℝ))
    (hE : (∑ i, cosinePotential (Y i)) ≤ (24367/1000 : ℝ)) :
    (∑ i, |cosinePotentialSlope (Y i)|) < 1600 := by
  have hsq := core_slope_sum_sq_le Finset.univ Y (211/500) (by norm_num) (by norm_num)
    (fun i _ => hY i)
  have hC := mirror_old_core_curvature_le (211/500) (by norm_num) le_rfl
  have hEnonneg : 0 ≤ ∑ i, cosinePotential (Y i) := by
    apply Finset.sum_nonneg
    intro i hi
    unfold cosinePotential
    exact neg_nonneg.mpr (Real.log_nonpos (sq_nonneg _) (Real.cos_sq_le_one _))
  norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hsq
  have hm := mul_le_mul_of_nonneg_right hC hEnonneg
  nlinarith

/-- Exactly the scalar right-hand side of the actual mirror action theorem,
with the common source tail coefficient h=1/100 and gap g=L−ell. -/
noncomputable def p1MirrorActionBudget
    (E W Ccore Cgap Δ Δplus r d : ℝ) (ell g : ℕ) : ℝ :=
  let ρ := (1/100 : ℝ)*r^(g+1)
  2*E + W*(Δplus+2*ρ) + Ccore*(ell : ℝ)*(Δplus+ρ)^2 +
    Cgap*((1/100 : ℝ)^2*(g : ℝ)*r^(g+1) +
      2*Δ*(1/100 : ℝ)*r/(1-r) + Δ^2*((g : ℝ)/4+1/(2*d)))

/-- A gap-power enclosure bounds every term in the exact mirror budget. -/
theorem p1MirrorActionBudget_le_coarse
    (E W Ccore Cgap Δ Δplus r d q : ℝ) (ell g : ℕ)
    (hW : 0 ≤ W) (hC : 0 ≤ Ccore) (hG : 0 ≤ Cgap)
    (hΔ : 0 ≤ Δ) (hΔplus : 0 ≤ Δplus)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 3/2 ≤ d)
    (hq : r^(g+1) ≤ q) :
    p1MirrorActionBudget E W Ccore Cgap Δ Δplus r d ell g ≤
      2*E + W*(Δplus+q/50) + Ccore*(ell : ℝ)*(Δplus+q/100)^2 +
        Cgap*((g : ℝ)*q/10000 + 3*Δ/100 + Δ^2*((g : ℝ)/4+1/3)) := by
  have hq0 : 0 ≤ q := (pow_nonneg hr0 _).trans hq
  have hratio : r/(1-r) ≤ (3/2 : ℝ) :=
    (div_le_iff₀ (by linarith : 0 < 1-r)).2 (by linarith)
  have hdinv : 1/(2*d) ≤ (1/3 : ℝ) :=
    (div_le_iff₀ (by linarith : 0 < 2*d)).2 (by linarith)
  have hmixed : 2*Δ*(1/100 : ℝ)*r/(1-r) ≤ 3*Δ/100 := by
    calc
      _ = (2*Δ/100)*(r/(1-r)) := by ring
      _ ≤ (2*Δ/100)*(3/2) := by gcongr
      _ = _ := by ring
  unfold p1MirrorActionBudget
  dsimp only
  calc
    _ ≤ 2*E + W*(Δplus+2*(q/100)) + Ccore*(ell : ℝ)*(Δplus+q/100)^2 +
        Cgap*((1/100 : ℝ)^2*(g : ℝ)*q + 3*Δ/100 + Δ^2*((g : ℝ)/4+1/3)) := by
      gcongr
      · nlinarith
      · nlinarith
    _ = _ := by ring

/-- The first exact bridge has g=124−27=97 and exponent98. -/
theorem p1Mirror_first_gap_power_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    r^(97+1) ≤ (1/10^21 : ℝ) := by
  calc
    _ ≤ (3/5 : ℝ)^98 := pow_le_pow_left₀ hr0 hr _
    _ ≤ _ := by norm_num

/-- All long bridge powers reduce to the small fixed exponent100. -/
theorem p1Mirror_long_gap_power_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5)
    (n : ℕ) (hn : 100 ≤ n) : r^n ≤ (1/10^22 : ℝ) := by
  calc
    _ ≤ (3/5 : ℝ)^n := pow_le_pow_left₀ hr0 hr _
    _ ≤ (3/5 : ℝ)^100 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ ≤ _ := by norm_num

/-- The first source mirror, with the exact 97-site bridge, has fresh action
strictly below24.367. This is scalar propagation of its actual action formula. -/
theorem p1Mirror_first_budget_lt
    (E W Ccore Cgap Δ Δplus r d : ℝ)
    (hE : E ≤ 2429771/200000)
    (hW0 : 0 ≤ W) (hW : W ≤ 473)
    (hC0 : 0 ≤ Ccore) (hC : Ccore ≤ 1350)
    (hG0 : 0 ≤ Cgap) (hG : Cgap ≤ 496/25)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1014602/10^8)
    (hΔplus0 : 0 ≤ Δplus) (hΔplus : Δplus ≤ 2542925/10^11)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 3/2 ≤ d) :
    p1MirrorActionBudget E W Ccore Cgap Δ Δplus r d 27 97 < 24367/1000 := by
  have h := p1MirrorActionBudget_le_coarse E W Ccore Cgap Δ Δplus r d (1/10^21)
    27 97 hW0 hC0 hG0 hΔ0 hΔplus0 hr0 hr hd (p1Mirror_first_gap_power_bound r hr0 hr)
  apply h.trans_lt
  calc
    _ ≤ 2*(2429771/200000 : ℝ) + 473*(2542925/10^11+(1/10^21)/50) +
        1350*27*(2542925/10^11+(1/10^21)/100)^2 +
        (496/25 : ℝ)*(97*(1/10^21)/10000 + 3*(1014602/10^8)/100 +
          (1014602/10^8)^2*(97/4+1/3)) := by gcongr <;> norm_num
    _ < _ := by norm_num

/-- The second exact gap is489637838−151=489637687. Even with the relaxed
first action24.367, its source mirror budget remains strictly below50.3. -/
theorem p1Mirror_second_budget_lt
    (E W Ccore Cgap Δ Δplus r d : ℝ)
    (hE : E ≤ 24367/1000)
    (hW0 : 0 ≤ W) (hW : W ≤ 1600)
    (hC0 : 0 ≤ Ccore) (hC : Ccore ≤ 1350)
    (hG0 : 0 ≤ Cgap) (hG : Cgap ≤ 1977/100)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 2542925/10^11)
    (hΔplus0 : 0 ≤ Δplus) (hΔplus : Δplus ≤ 9498/10^17)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) (hd : 3/2 ≤ d) :
    p1MirrorActionBudget E W Ccore Cgap Δ Δplus r d 151 489637687 < 503/10 := by
  have hp : r^(489637687+1) ≤ (1/10^22 : ℝ) :=
    p1Mirror_long_gap_power_bound r hr0 hr _ (by norm_num)
  have h := p1MirrorActionBudget_le_coarse E W Ccore Cgap Δ Δplus r d (1/10^22)
    151 489637687 hW0 hC0 hG0 hΔ0 hΔplus0 hr0 hr hd hp
  apply h.trans_lt
  calc
    _ ≤ 2*(24367/1000 : ℝ) + 1600*(9498/10^17+(1/10^22)/50) +
        1350*151*(9498/10^17+(1/10^22)/100)^2 +
        (1977/100 : ℝ)*(489637687*(1/10^22)/10000 + 3*(2542925/10^11)/100 +
          (2542925/10^11)^2*(489637687/4+1/3)) := by gcongr <;> norm_num
    _ < _ := by norm_num

end Salem
