module

public import Mathlib

@[expose] public section

open scoped BigOperators
open Polynomial

namespace Salem.QuarticCore

/-!
The classification proof lives in this Mathlib-only core. Its polynomial, radical,
and root-pattern definitions literally match the frozen declarations, so the
frozen-facing algebra and classification modules instantiate it without a cycle.
-/

noncomputable def P1 : Polynomial ℤ :=
  Polynomial.X ^ 4 - Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X + 1

noncomputable def P2 : Polynomial ℤ :=
  Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 + Polynomial.X ^ 2 -
    2 * Polynomial.X + 1

noncomputable def beta1 : ℝ :=
  let u : ℝ := (1 + Real.sqrt 13) / 2
  (u + Real.sqrt (u ^ 2 - 4)) / 2

noncomputable def beta2 : ℝ :=
  let u : ℝ := 1 + Real.sqrt 2
  (u + Real.sqrt (u ^ 2 - 4)) / 2

noncomputable def IsQuarticSalemNumber (β : ℝ) : Prop :=
  ∃ P : Polynomial ℤ, ∃ ζ : ℂ,
    P.Monic ∧
    P.natDegree = 4 ∧
    Irreducible (P.map (algebraMap ℤ ℚ)) ∧
    1 < β ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ) ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ) ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot ζ ∧
    (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ) ∧
    ‖ζ‖ = 1 ∧
    ζ.im ≠ 0 ∧
    ∀ z : ℂ, (P.map (algebraMap ℤ ℂ)).IsRoot z →
      z = (β : ℂ) ∨ z = (β⁻¹ : ℂ) ∨ z = ζ ∨ z = star ζ

/-- Real evaluation of the first quartic polynomial from v2, (1.1). -/
lemma P1_eval_real (x : ℝ) :
    (P1.map (algebraMap ℤ ℝ)).eval x =
      x ^ 4 - x ^ 3 - x ^ 2 - x + 1 := by
  simp [P1]

/-- Real evaluation of the second quartic polynomial from v2, (1.1). -/
lemma P2_eval_real (x : ℝ) :
    (P2.map (algebraMap ℤ ℝ)).eval x =
      x ^ 4 - 2 * x ^ 3 + x ^ 2 - 2 * x + 1 := by
  simp [P2]

/-- The radical formula for `β₁` lies in the overlapping range and satisfies `β₁ > 3/2`.
This is the elementary part of v2 Lemma `lem:roots`. -/
lemma beta1_gt_three_halves : (3 / 2 : ℝ) < beta1 := by
  dsimp [beta1]
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have h13 : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
  have hslo : (7 / 2 : ℝ) < Real.sqrt 13 := by nlinarith
  have hu : (9 / 4 : ℝ) < (1 + Real.sqrt 13) / 2 := by nlinarith
  have hrad : 0 ≤ ((1 + Real.sqrt 13) / 2) ^ 2 - 4 := by nlinarith
  have hsq : 0 ≤ Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4) := Real.sqrt_nonneg _
  have hsq2 :
      (Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4)) ^ 2 =
        ((1 + Real.sqrt 13) / 2) ^ 2 - 4 := by
    exact Real.sq_sqrt hrad
  have hsqlo : (1 : ℝ) < Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4) := by
    nlinarith
  nlinarith

/-- The radical formula for `β₂` lies in the overlapping range and satisfies `β₂ > 3/2`.
This is the elementary part of v2 Lemma `lem:roots`. -/
lemma beta2_gt_three_halves : (3 / 2 : ℝ) < beta2 := by
  dsimp [beta2]
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have h2 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hslo : (5 / 4 : ℝ) < Real.sqrt 2 := by nlinarith
  have hu : (9 / 8 : ℝ) < 1 + Real.sqrt 2 := by nlinarith
  have hrad : 0 ≤ (1 + Real.sqrt 2) ^ 2 - 4 := by nlinarith
  have hsq : 0 ≤ Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4) := Real.sqrt_nonneg _
  have hsq2 :
      (Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4)) ^ 2 =
        (1 + Real.sqrt 2) ^ 2 - 4 := by
    exact Real.sq_sqrt hrad
  have hsqlo : (1 : ℝ) < Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4) := by
    nlinarith
  nlinarith

lemma one_lt_beta1 : 1 < beta1 := by
  exact lt_trans (by norm_num) beta1_gt_three_halves

lemma one_lt_beta2 : 1 < beta2 := by
  exact lt_trans (by norm_num) beta2_gt_three_halves

lemma beta1_sq_gt_two : 2 < beta1 ^ 2 := by
  nlinarith [beta1_gt_three_halves]

lemma beta2_sq_gt_two : 2 < beta2 ^ 2 := by
  nlinarith [beta2_gt_three_halves]

private lemma beta1_quadratic :
    beta1 ^ 2 - ((1 + Real.sqrt 13) / 2) * beta1 + 1 = 0 := by
  dsimp [beta1]
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have hu : 0 ≤ ((1 + Real.sqrt 13) / 2 : ℝ) ^ 2 - 4 := by
    have h13 : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hv := Real.sq_sqrt hu
  nlinarith

private lemma beta2_quadratic :
    beta2 ^ 2 - (1 + Real.sqrt 2) * beta2 + 1 = 0 := by
  dsimp [beta2]
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have hu : 0 ≤ ((1 + Real.sqrt 2 : ℝ) ^ 2 - 4) := by
    have h2 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hv := Real.sq_sqrt hu
  nlinarith

lemma beta1_gt_five_thirds : (5 / 3 : ℝ) < beta1 := by
  dsimp [beta1]
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have h13 : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
  have hslo : (18 / 5 : ℝ) < Real.sqrt 13 := by nlinarith
  have hu : (23 / 10 : ℝ) < (1 + Real.sqrt 13) / 2 := by nlinarith
  have hrad : 0 ≤ ((1 + Real.sqrt 13) / 2) ^ 2 - 4 := by nlinarith
  have hv : 0 ≤ Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlo : (9 / 8 : ℝ) < Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4) := by
    nlinarith
  nlinarith

lemma beta1_lt_two : beta1 < 2 := by
  dsimp [beta1]
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  have h13 : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
  have hslt : (Real.sqrt 13 : ℝ) < 4 := by nlinarith
  have hu : ((1 + Real.sqrt 13) / 2 : ℝ) < 5 / 2 := by nlinarith
  have hupos : 0 ≤ ((1 + Real.sqrt 13) / 2 : ℝ) := by nlinarith
  have hrad : 0 ≤ ((1 + Real.sqrt 13) / 2) ^ 2 - 4 := by nlinarith
  have hv : 0 ≤ Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlt : Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2 - 4) < 3 / 2 := by
    nlinarith
  nlinarith

lemma beta2_gt_five_thirds : (5 / 3 : ℝ) < beta2 := by
  dsimp [beta2]
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have h2 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hslo : (7 / 5 : ℝ) < Real.sqrt 2 := by nlinarith
  have hu : (12 / 5 : ℝ) < 1 + Real.sqrt 2 := by nlinarith
  have hrad : 0 ≤ (1 + Real.sqrt 2) ^ 2 - 4 := by nlinarith
  have hv : 0 ≤ Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlo : (4 / 3 : ℝ) < Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4) := by
    nlinarith
  nlinarith

lemma beta2_lt_two : beta2 < 2 := by
  dsimp [beta2]
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  have h2 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
  have hslt : (Real.sqrt 2 : ℝ) < 3 / 2 := by nlinarith
  have hu : (1 + Real.sqrt 2 : ℝ) < 5 / 2 := by nlinarith
  have hupos : 0 ≤ (1 + Real.sqrt 2 : ℝ) := by nlinarith
  have hrad : 0 ≤ (1 + Real.sqrt 2) ^ 2 - 4 := by nlinarith
  have hv : 0 ≤ Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4) := Real.sqrt_nonneg _
  have hv_sq := Real.sq_sqrt hrad
  have hvlt : Real.sqrt ((1 + Real.sqrt 2) ^ 2 - 4) < 3 / 2 := by
    nlinarith
  nlinarith

lemma beta1_inv_bounds :
    (1 / 2 : ℝ) < beta1⁻¹ ∧ beta1⁻¹ < 3 / 5 := by
  have hb : (5 / 3 : ℝ) < beta1 ∧ beta1 < 2 := ⟨beta1_gt_five_thirds, beta1_lt_two⟩
  constructor
  · simpa [one_div] using one_div_lt_one_div_of_lt (show (0 : ℝ) < beta1 by nlinarith [hb.1]) hb.2
  · simpa [one_div] using one_div_lt_one_div_of_lt (show (0 : ℝ) < (5 / 3 : ℝ) by norm_num) hb.1

lemma beta2_inv_bounds :
    (1 / 2 : ℝ) < beta2⁻¹ ∧ beta2⁻¹ < 3 / 5 := by
  have hb : (5 / 3 : ℝ) < beta2 ∧ beta2 < 2 := ⟨beta2_gt_five_thirds, beta2_lt_two⟩
  constructor
  · simpa [one_div] using one_div_lt_one_div_of_lt (show (0 : ℝ) < beta2 by nlinarith [hb.1]) hb.2
  · simpa [one_div] using one_div_lt_one_div_of_lt (show (0 : ℝ) < (5 / 3 : ℝ) by norm_num) hb.1

lemma beta1_P1_root :
    (P1.map (algebraMap ℤ ℝ)).eval beta1 = 0 := by
  let u : ℝ := (1 + Real.sqrt 13) / 2
  have hu : u ^ 2 - u - 3 = 0 := by
    dsimp [u]
    have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
    nlinarith
  have hq : beta1 ^ 2 - u * beta1 + 1 = 0 := by
    simpa [u] using beta1_quadratic
  rw [P1_eval_real]
  dsimp [u] at hu hq ⊢
  calc
    beta1 ^ 4 - beta1 ^ 3 - beta1 ^ 2 - beta1 + 1 =
        (beta1 ^ 2 - ((1 + Real.sqrt 13) / 2) * beta1 + 1) *
            (beta1 ^ 2 + (((1 + Real.sqrt 13) / 2) - 1) * beta1 +
              (((1 + Real.sqrt 13) / 2) ^ 2 - (1 + Real.sqrt 13) / 2 - 2)) +
          (((1 + Real.sqrt 13) / 2) ^ 2 - (1 + Real.sqrt 13) / 2 - 3) *
            (((1 + Real.sqrt 13) / 2) * beta1 - 1) := by ring
    _ = 0 := by rw [hq, hu]; ring

lemma beta2_P2_root :
    (P2.map (algebraMap ℤ ℝ)).eval beta2 = 0 := by
  let u : ℝ := 1 + Real.sqrt 2
  have hu : u ^ 2 - 2 * u - 1 = 0 := by
    dsimp [u]
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    nlinarith
  have hq : beta2 ^ 2 - u * beta2 + 1 = 0 := by
    simpa [u] using beta2_quadratic
  rw [P2_eval_real]
  dsimp [u] at hu hq ⊢
  calc
    beta2 ^ 4 - 2 * beta2 ^ 3 + beta2 ^ 2 - 2 * beta2 + 1 =
        (beta2 ^ 2 - (1 + Real.sqrt 2) * beta2 + 1) *
            (beta2 ^ 2 + ((1 + Real.sqrt 2) - 2) * beta2 +
              ((1 + Real.sqrt 2) ^ 2 - 2 * (1 + Real.sqrt 2))) +
          ((1 + Real.sqrt 2) ^ 2 - 2 * (1 + Real.sqrt 2) - 1) *
            ((1 + Real.sqrt 2) * beta2 - 1) := by ring
    _ = 0 := by rw [hq, hu]; ring

private lemma p1_trace_facts :
    let u : ℝ := (1 + Real.sqrt 13) / 2
    let v : ℝ := (1 - Real.sqrt 13) / 2
    u + v = 1 ∧ u * v = -3 := by
  dsimp
  have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
  constructor <;> nlinarith

private lemma p2_trace_facts :
    let u : ℝ := 1 + Real.sqrt 2
    let v : ℝ := 1 - Real.sqrt 2
    u + v = 2 ∧ u * v = -1 := by
  dsimp
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
  constructor <;> nlinarith

lemma p1_root_unique_in_one_two {x : ℝ}
    (hx1 : 1 < x) (hx2 : x < 2)
    (hroot : (P1.map (algebraMap ℤ ℝ)).eval x = 0) :
    x = beta1 := by
  rw [P1_eval_real] at hroot
  let u : ℝ := (1 + Real.sqrt 13) / 2
  let v : ℝ := (1 - Real.sqrt 13) / 2
  have huv : u + v = 1 ∧ u * v = -3 := by
    simpa [u, v] using p1_trace_facts
  have hvneg : v < 0 := by
    dsimp [v]
    have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
    have hsn : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hsecond : 0 < x ^ 2 - v * x + 1 := by
    nlinarith [sq_nonneg x]
  have hfirst : x ^ 2 - u * x + 1 = 0 := by
    have hfac :
        x ^ 4 - x ^ 3 - x ^ 2 - x + 1 =
          (x ^ 2 - u * x + 1) * (x ^ 2 - v * x + 1) := by
      linear_combination x ^ 3 * huv.1 - x ^ 2 * huv.2 + x * huv.1
    rw [hfac] at hroot
    nlinarith
  have hbeta : beta1 ^ 2 - u * beta1 + 1 = 0 := by
    dsimp [u]
    have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
    have hu : 0 ≤ ((1 + Real.sqrt 13) / 2 : ℝ) ^ 2 - 4 := by
      have hsn : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hv := Real.sq_sqrt hu
    dsimp [beta1]
    nlinarith
  have hsum_ne : x + beta1 - u ≠ 0 := by
    have hu_lt : u < 5 / 2 := by
      dsimp [u]
      have hs : (Real.sqrt 13 : ℝ) ^ 2 = 13 := by norm_num
      have hsn : 0 ≤ (Real.sqrt 13 : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hb : (3 / 2 : ℝ) < beta1 := beta1_gt_three_halves
    nlinarith
  have hprod : (x - beta1) * (x + beta1 - u) = 0 := by
    nlinarith [hfirst, hbeta]
  rcases mul_eq_zero.mp hprod with h | h
  · nlinarith
  · exact False.elim (hsum_ne h)

lemma p2_root_unique_in_one_two {x : ℝ}
    (hx1 : 1 < x) (hx2 : x < 2)
    (hroot : (P2.map (algebraMap ℤ ℝ)).eval x = 0) :
    x = beta2 := by
  rw [P2_eval_real] at hroot
  let u : ℝ := 1 + Real.sqrt 2
  let v : ℝ := 1 - Real.sqrt 2
  have huv : u + v = 2 ∧ u * v = -1 := by
    simpa [u, v] using p2_trace_facts
  have hvneg : v < 0 := by
    dsimp [v]
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hsecond : 0 < x ^ 2 - v * x + 1 := by
    nlinarith [sq_nonneg x]
  have hfirst : x ^ 2 - u * x + 1 = 0 := by
    have hfac :
        x ^ 4 - 2 * x ^ 3 + x ^ 2 - 2 * x + 1 =
          (x ^ 2 - u * x + 1) * (x ^ 2 - v * x + 1) := by
      linear_combination x ^ 3 * huv.1 - x ^ 2 * huv.2 + x * huv.1
    rw [hfac] at hroot
    nlinarith
  have hbeta : beta2 ^ 2 - u * beta2 + 1 = 0 := by
    dsimp [u]
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
    have hu : 0 ≤ ((1 + Real.sqrt 2 : ℝ) ^ 2 - 4) := by
      have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hv := Real.sq_sqrt hu
    dsimp [beta2]
    nlinarith
  have hsum_ne : x + beta2 - u ≠ 0 := by
    have hu_lt : u < 5 / 2 := by
      dsimp [u]
      have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by norm_num
      have hsn : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hb : (3 / 2 : ℝ) < beta2 := beta2_gt_three_halves
    nlinarith
  have hprod : (x - beta2) * (x + beta2 - u) = 0 := by
    nlinarith [hfirst, hbeta]
  rcases mul_eq_zero.mp hprod with h | h
  · nlinarith
  · exact False.elim (hsum_ne h)

/-- Conditional form of the paper's quartic classification: once the coefficient
case has been reduced to `P₁` or `P₂`, the root in `(1,2)` is exactly `β₁` or `β₂`. -/
theorem quartic_root_cases
    {β : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2)
    (hcase : (P1.map (algebraMap ℤ ℝ)).eval β = 0 ∨
      (P2.map (algebraMap ℤ ℝ)).eval β = 0) :
    β = beta1 ∨ β = beta2 := by
  rcases hcase with h | h
  · exact Or.inl (p1_root_unique_in_one_two hβ1 hβ2 h)
  · exact Or.inr (p2_root_unique_in_one_two hβ1 hβ2 h)






lemma quartic_prod_of_roots
    {P : Polynomial ℤ} {β : ℝ} {ζ : ℂ}
    (hmonic : P.Monic) (hdeg : P.natDegree = 4)
    (hrootβ : (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ))
    (hrootinv : (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ))
    (hrootζ : (P.map (algebraMap ℤ ℂ)).IsRoot ζ)
    (hrootstar : (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ))
    (hβ : 1 < β) (hζim : ζ.im ≠ 0) :
    P.map (algebraMap ℤ ℂ) =
      (Polynomial.X - Polynomial.C (β : ℂ)) *
      (Polynomial.X - Polynomial.C (β⁻¹ : ℂ)) *
      (Polynomial.X - Polynomial.C ζ) *
      (Polynomial.X - Polynomial.C (star ζ)) := by
  let p : Polynomial ℂ := P.map (algebraMap ℤ ℂ)
  let s : Multiset ℂ := {((β : ℂ)), ((β⁻¹ : ℂ)), ζ, star ζ}
  have hp0 : p ≠ 0 := by
    exact (hmonic.map (algebraMap ℤ ℂ)).ne_zero
  have hpmonic : p.Monic := hmonic.map (algebraMap ℤ ℂ)
  have hpdeg : p.natDegree = 4 := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hdeg]
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = 4 := by
    rw [← hsplit.natDegree_eq_card_roots, hpdeg]
  have hbr : (β : ℂ) ≠ (β⁻¹ : ℂ) := by
    intro h
    have hh := congrArg (fun z : ℂ => z * (β : ℂ)) h
    have hbpos : 0 < β := by linarith
    have hb0 : (β : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hbpos)
    simp [hb0] at hh
    have hr := congrArg Complex.re hh
    simp at hr
    nlinarith
  have hbz : (β : ℂ) ≠ ζ := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hζim (by linarith)
  have hbsz : (β : ℂ) ≠ star ζ := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hζim (by linarith)
  have hrz : (β⁻¹ : ℂ) ≠ ζ := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hζim (by linarith)
  have hrsz : (β⁻¹ : ℂ) ≠ star ζ := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hζim (by linarith)
  have hzz : ζ ≠ star ζ := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hζim (by linarith)
  have hlast : ({ζ, star ζ} : Multiset ℂ).Nodup := by
    apply Multiset.nodup_cons.mpr
    constructor
    · intro h
      exact hzz (by simpa using h)
    · exact Multiset.nodup_singleton _
  have hmid : ({(β⁻¹ : ℂ), ζ, star ζ} : Multiset ℂ).Nodup := by
    apply Multiset.nodup_cons.mpr
    constructor
    · intro h
      have h' : (β⁻¹ : ℂ) = ζ ∨ (β⁻¹ : ℂ) = star ζ := by simpa using h
      rcases h' with h | h
      · exact hrz h
      · exact hrsz h
    · exact hlast
  have hsnd : s.Nodup := by
    dsimp [s]
    apply Multiset.nodup_cons.mpr
    constructor
    · intro h
      have h' : (β : ℂ) = (β⁻¹ : ℂ) ∨ (β : ℂ) = ζ ∨ (β : ℂ) = star ζ := by
        simpa using h
      rcases h' with h | h | h
      · exact hbr h
      · exact hbz h
      · exact hbsz h
    · exact hmid
  have hs_card : s.card = 4 := by simp [s]
  have hs_subset : s ⊆ p.roots := by
    dsimp [s]
    apply Multiset.cons_subset.mpr
    constructor
    · exact (Polynomial.mem_roots hp0).2 hrootβ
    · apply Multiset.cons_subset.mpr
      constructor
      · exact (Polynomial.mem_roots hp0).2 hrootinv
      · apply Multiset.cons_subset.mpr
        constructor
        · exact (Polynomial.mem_roots hp0).2 hrootζ
        · exact Multiset.singleton_subset.mpr ((Polynomial.mem_roots hp0).2 hrootstar)
  have hs_le : s ≤ p.roots := (Multiset.le_iff_subset hsnd).2 hs_subset
  have hs_eq : s = p.roots := by
    apply Multiset.eq_of_le_of_card_le hs_le
    rw [hcard, hs_card]
  have hp_prod : p = (s.map (fun z => Polynomial.X - Polynomial.C z)).prod := by
    rw [hs_eq]
    exact hsplit.eq_prod_roots_of_monic hpmonic
  dsimp [p, s] at hp_prod ⊢
  simpa [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, mul_assoc] using hp_prod



lemma quartic_coeff
    {P : Polynomial ℤ} {β : ℝ} {ζ : ℂ}
    (hmonic : P.Monic) (hdeg : P.natDegree = 4)
    (hrootβ : (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ))
    (hrootinv : (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ))
    (hrootζ : (P.map (algebraMap ℤ ℂ)).IsRoot ζ)
    (hrootstar : (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ))
    (hβ : 1 < β) (hζim : ζ.im ≠ 0) (hζnorm : ‖ζ‖ = 1) :
    let A : ℤ := -P.coeff 3
    let B : ℤ := P.coeff 2
    ((A : ℂ) = (β : ℂ) + (β⁻¹ : ℂ) + ζ + star ζ) ∧
      ((B : ℂ) = (β : ℂ) * (β⁻¹ : ℂ) + (β : ℂ) * ζ +
        (β : ℂ) * star ζ + (β⁻¹ : ℂ) * ζ + (β⁻¹ : ℂ) * star ζ + ζ * star ζ) := by
  let A : ℤ := -P.coeff 3
  let B : ℤ := P.coeff 2
  let p : Polynomial ℂ := P.map (algebraMap ℤ ℂ)
  let s : Multiset ℂ := {((β : ℂ)), ((β⁻¹ : ℂ)), ζ, star ζ}
  have hpmonic : p.Monic := hmonic.map (algebraMap ℤ ℂ)
  have hpdeg : p.natDegree = 4 := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hdeg]
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hs_eq : s = p.roots := by
    -- recover the root multiset from the product theorem
    have hprod := quartic_prod_of_roots hmonic hdeg hrootβ hrootinv hrootζ hrootstar hβ hζim
    have hp0 : p ≠ 0 := hpmonic.ne_zero
    have hcard : p.roots.card = 4 := by rw [← hsplit.natDegree_eq_card_roots, hpdeg]
    have hbr : (β : ℂ) ≠ (β⁻¹ : ℂ) := by
      intro h
      have hh := congrArg (fun z : ℂ => z * (β : ℂ)) h
      have hbpos : 0 < β := by linarith
      have hb0 : (β : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hbpos)
      simp [hb0] at hh
      have hr := congrArg Complex.re hh
      simp at hr
      nlinarith
    have hbz : (β : ℂ) ≠ ζ := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact hζim (by linarith)
    have hbsz : (β : ℂ) ≠ star ζ := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact hζim (by linarith)
    have hrz : (β⁻¹ : ℂ) ≠ ζ := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact hζim (by linarith)
    have hrsz : (β⁻¹ : ℂ) ≠ star ζ := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact hζim (by linarith)
    have hzz : ζ ≠ star ζ := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact hζim (by linarith)
    have hlast : ({ζ, star ζ} : Multiset ℂ).Nodup := by
      apply Multiset.nodup_cons.mpr
      constructor
      · intro h
        exact hzz (by simpa using h)
      · exact Multiset.nodup_singleton _
    have hmid : ({(β⁻¹ : ℂ), ζ, star ζ} : Multiset ℂ).Nodup := by
      apply Multiset.nodup_cons.mpr
      constructor
      · intro h
        have h' : (β⁻¹ : ℂ) = ζ ∨ (β⁻¹ : ℂ) = star ζ := by simpa using h
        rcases h' with h | h
        · exact hrz h
        · exact hrsz h
      · exact hlast
    have hsnd : s.Nodup := by
      dsimp [s]
      apply Multiset.nodup_cons.mpr
      constructor
      · intro h
        have h' : (β : ℂ) = (β⁻¹ : ℂ) ∨ (β : ℂ) = ζ ∨ (β : ℂ) = star ζ := by
          simpa using h
        rcases h' with h | h | h
        · exact hbr h
        · exact hbz h
        · exact hbsz h
      · exact hmid
    have hs_card : s.card = 4 := by simp [s]
    have hs_subset : s ⊆ p.roots := by
      dsimp [s]
      apply Multiset.cons_subset.mpr
      constructor
      · exact (Polynomial.mem_roots hp0).2 hrootβ
      · apply Multiset.cons_subset.mpr
        constructor
        · exact (Polynomial.mem_roots hp0).2 hrootinv
        · apply Multiset.cons_subset.mpr
          constructor
          · exact (Polynomial.mem_roots hp0).2 hrootζ
          · exact Multiset.singleton_subset.mpr ((Polynomial.mem_roots hp0).2 hrootstar)
    have hs_le : s ≤ p.roots := (Multiset.le_iff_subset hsnd).2 hs_subset
    apply Multiset.eq_of_le_of_card_le hs_le
    rw [hcard, hs_card]
  have hrootscard : p.roots.card = p.natDegree := (hsplit.natDegree_eq_card_roots).symm
  have hc3 := Polynomial.coeff_eq_esymm_roots_of_card hrootscard (k := 3) (by omega : 3 ≤ p.natDegree)
  have hc2 := Polynomial.coeff_eq_esymm_roots_of_card hrootscard (k := 2) (by omega : 2 ≤ p.natDegree)
  have es1 : s.esymm 1 = (β : ℂ) + (β⁻¹ : ℂ) + ζ + star ζ := by
    change (Multiset.map Multiset.prod (Multiset.powersetCard 1
      (↑[(β : ℂ), (β⁻¹ : ℂ), ζ, star ζ] : Multiset ℂ))).sum = _
    rw [Multiset.powersetCard_coe]
    simp [List.sublistsLen, List.sublistsLenAux]
    ring
  have es2 : s.esymm 2 = (β : ℂ) * (β⁻¹ : ℂ) + (β : ℂ) * ζ +
        (β : ℂ) * star ζ + (β⁻¹ : ℂ) * ζ + (β⁻¹ : ℂ) * star ζ + ζ * star ζ := by
    change (Multiset.map Multiset.prod (Multiset.powersetCard 2
      (↑[(β : ℂ), (β⁻¹ : ℂ), ζ, star ζ] : Multiset ℂ))).sum = _
    rw [Multiset.powersetCard_coe]
    simp [List.sublistsLen, List.sublistsLenAux]
    ring
  have hsum : (A : ℂ) = (β : ℂ) + (β⁻¹ : ℂ) + ζ + star ζ := by
    rw [← hs_eq] at hc3
    rw [hpdeg, hpmonic.leadingCoeff, es1] at hc3
    change (P.map (algebraMap ℤ ℂ)).coeff 3 = _ at hc3
    rw [Polynomial.coeff_map] at hc3
    norm_num at hc3
    dsimp [A]
    norm_num [map_neg] at hc3 ⊢
    linear_combination -hc3
  have hpair : (B : ℂ) = (β : ℂ) * (β⁻¹ : ℂ) + (β : ℂ) * ζ +
        (β : ℂ) * star ζ + (β⁻¹ : ℂ) * ζ + (β⁻¹ : ℂ) * star ζ + ζ * star ζ := by
    rw [← hs_eq] at hc2
    rw [hpdeg, hpmonic.leadingCoeff, es2] at hc2
    change (P.map (algebraMap ℤ ℂ)).coeff 2 = _ at hc2
    rw [Polynomial.coeff_map] at hc2
    norm_num at hc2
    dsimp [B]
    norm_num [map_neg] at hc2 ⊢
    linear_combination hc2
  exact ⟨hsum, hpair⟩




lemma quartic_coeff_case
    {P : Polynomial ℤ} {β : ℝ} {ζ : ℂ}
    (hmonic : P.Monic) (hdeg : P.natDegree = 4)
    (hrootβ : (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ))
    (hrootinv : (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ))
    (hrootζ : (P.map (algebraMap ℤ ℂ)).IsRoot ζ)
    (hrootstar : (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ))
    (hβ : 1 < β) (hβ2 : β < 2) (hζim : ζ.im ≠ 0) (hζnorm : ‖ζ‖ = 1) :
    (-P.coeff 3 = 1 ∧ P.coeff 2 = -1) ∨
      (-P.coeff 3 = 2 ∧ P.coeff 2 = 1) := by
  have hcoeff := quartic_coeff hmonic hdeg hrootβ hrootinv hrootζ hrootstar hβ hζim hζnorm
  dsimp at hcoeff
  rcases hcoeff with ⟨hA, hB⟩
  let u : ℝ := β + β⁻¹
  let v : ℝ := 2 * ζ.re
  have hAreal : ((-P.coeff 3 : ℤ) : ℝ) = u + v := by
    have h := congrArg Complex.re hA
    convert h using 1 <;> simp [u, v, Complex.add_re, Complex.star_def] <;> ring
  have hBreal : ((P.coeff 2 : ℤ) : ℝ) =
      (β : ℝ) * β⁻¹ + β * ζ.re + β * ζ.re + β⁻¹ * ζ.re + β⁻¹ * ζ.re + ζ.re * ζ.re + ζ.im * ζ.im := by
    have h := congrArg Complex.re hB
    -- retain this raw identity; it is simplified below using normSq
    convert h using 1 <;> simp [Complex.mul_re, Complex.star_def] <;> ring
  have hβpos : 0 < β := by linarith
  have hβinv : β * β⁻¹ = 1 := by field_simp
  have hβinvpos : 0 < β⁻¹ := inv_pos.mpr hβpos
  have hu_lower : 2 < u := by
    dsimp [u]
    have hs : 0 < (β - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hβ))
    nlinarith [hβinv]
  have hu_upper : u < 5 / 2 := by
    dsimp [u]
    apply lt_of_mul_lt_mul_right _ (le_of_lt hβpos)
    have hquad : (β - 1) * (β - 2) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hβ) (sub_neg.mpr hβ2)
    nlinarith [hβinv, hquad]
  have hnormsq : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq ζ
    rw [hζnorm] at h
    simpa [Complex.normSq_apply, pow_two] using h
  have hv_lower : -2 < v := by
    dsimp [v]
    have himsq : 0 < ζ.im ^ 2 := sq_pos_of_ne_zero hζim
    nlinarith [hnormsq]
  have hv_upper : v < 2 := by
    dsimp [v]
    have himsq : 0 < ζ.im ^ 2 := sq_pos_of_ne_zero hζim
    nlinarith [hnormsq]
  have hApos : (0 : ℝ) < ((-P.coeff 3 : ℤ) : ℝ) := by nlinarith [hAreal]
  have hAlt : ((-P.coeff 3 : ℤ) : ℝ) < 9 / 2 := by nlinarith [hAreal]
  have hAint : 0 < -P.coeff 3 ∧ -P.coeff 3 < 5 := by
    constructor
    · exact_mod_cast hApos
    · have h' : ((-P.coeff 3 : ℤ) : ℝ) < (5 : ℝ) := lt_trans hAlt (by norm_num)
      exact_mod_cast h'
  have hA_cases : -P.coeff 3 = 1 ∨ -P.coeff 3 = 2 ∨ -P.coeff 3 = 3 ∨ -P.coeff 3 = 4 := by
    omega
  have hrel : ((P.coeff 2 : ℤ) : ℝ) =
      ((-P.coeff 3 : ℤ) : ℝ) * u - u ^ 2 + 2 := by
    have hnormsq' : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by nlinarith [hnormsq]
    rw [hBreal, hAreal]
    dsimp [u, v]
    nlinarith [hβinv, hnormsq']
  rcases hA_cases with hA1 | hA2 | hA3 | hA4
  · left
    constructor
    · exact hA1
    · have hBlow : (-2 : ℝ) < ((P.coeff 2 : ℤ) : ℝ) := by
        rw [hrel, hA1]
        norm_num
        have hp : (u - 5/2) * (u + 3/2) < 0 :=
          mul_neg_of_neg_of_pos (sub_neg.mpr hu_upper) (by linarith)
        nlinarith [hp]
      have hBup : ((P.coeff 2 : ℤ) : ℝ) < 0 := by
        rw [hrel, hA1]
        norm_num
        have hp : 0 < (u - 2) * (u + 1) :=
          mul_pos (sub_pos.mpr hu_lower) (by linarith)
        nlinarith [hp]
      have hBint : (-2 : ℤ) < P.coeff 2 ∧ P.coeff 2 < 0 := by
        constructor
        · exact_mod_cast hBlow
        · exact_mod_cast hBup
      omega
  · right
    constructor
    · exact hA2
    · have hBlow : (0 : ℝ) < ((P.coeff 2 : ℤ) : ℝ) := by
        rw [hrel, hA2]
        norm_num
        have hp : 0 < (3/2-(u-1)) * (3/2+(u-1)) :=
          mul_pos (by linarith) (by linarith)
        nlinarith [hp]
      have hBup : ((P.coeff 2 : ℤ) : ℝ) < 2 := by
        rw [hrel, hA2]
        norm_num
        have hp : 0 < u * (u - 2) :=
          mul_pos (by linarith) (sub_pos.mpr hu_lower)
        nlinarith [hp]
      have hBint : (0 : ℤ) < P.coeff 2 ∧ P.coeff 2 < 2 := by
        constructor
        · exact_mod_cast hBlow
        · exact_mod_cast hBup
      omega
  · exfalso
    have hBlow : (13 / 4 : ℝ) < ((P.coeff 2 : ℤ) : ℝ) := by
      rw [hrel, hA3]
      norm_num
      have hp : 0 < (5/2-u) * (u-1/2) :=
        mul_pos (sub_pos.mpr hu_upper) (by linarith)
      nlinarith [hp]
    have hBup : ((P.coeff 2 : ℤ) : ℝ) < 4 := by
      rw [hrel, hA3]
      norm_num
      have hp : 0 < (u-1) * (u-2) :=
        mul_pos (by linarith) (sub_pos.mpr hu_lower)
      nlinarith [hp]
    have hBint : (3 : ℤ) < P.coeff 2 ∧ P.coeff 2 < 4 := by
      constructor
      · have h' : (3 : ℝ) < ((P.coeff 2 : ℤ) : ℝ) := lt_trans (by norm_num) hBlow
        exact_mod_cast h'
      · exact_mod_cast hBup
    omega
  · exfalso
    have hBlow : (23 / 4 : ℝ) < ((P.coeff 2 : ℤ) : ℝ) := by
      rw [hrel, hA4]
      norm_num
      have hp : 0 < (5/2-u) * (u-3/2) :=
        mul_pos (sub_pos.mpr hu_upper) (by linarith)
      nlinarith [hp]
    have hBup : ((P.coeff 2 : ℤ) : ℝ) < 6 := by
      rw [hrel, hA4]
      norm_num
      have hp : 0 < (u-2)^2 := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hu_lower))
      nlinarith [hp]
    have hBint : (5 : ℤ) < P.coeff 2 ∧ P.coeff 2 < 6 := by
      constructor
      · have h' : (5 : ℝ) < ((P.coeff 2 : ℤ) : ℝ) := lt_trans (by norm_num) hBlow
        exact_mod_cast h'
      · exact_mod_cast hBup
    omega



lemma quartic_polynomial_eq_case
    {P : Polynomial ℤ} {β : ℝ} {ζ : ℂ}
    (hmonic : P.Monic) (hdeg : P.natDegree = 4)
    (hrootβ : (P.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ))
    (hrootinv : (P.map (algebraMap ℤ ℂ)).IsRoot (β⁻¹ : ℂ))
    (hrootζ : (P.map (algebraMap ℤ ℂ)).IsRoot ζ)
    (hrootstar : (P.map (algebraMap ℤ ℂ)).IsRoot (star ζ))
    (hβ : 1 < β) (hζim : ζ.im ≠ 0) (hζnorm : ‖ζ‖ = 1)
    (hcase : (-P.coeff 3 = 1 ∧ P.coeff 2 = -1) ∨
      (-P.coeff 3 = 2 ∧ P.coeff 2 = 1)) :
    P = P1 ∨ P = P2 := by
  let A : ℤ := -P.coeff 3
  let B : ℤ := P.coeff 2
  have hcoeff := quartic_coeff hmonic hdeg hrootβ hrootinv hrootζ hrootstar hβ hζim hζnorm
  dsimp [A, B] at hcoeff
  rcases hcoeff with ⟨hsum, hpair⟩
  have hbr : (β : ℂ) * (β⁻¹ : ℂ) = 1 := by
    have hbpos : 0 < β := by linarith
    have hb0 : β ≠ 0 := ne_of_gt hbpos
    rw [← Complex.ofReal_inv]
    norm_num [hb0]
  have hzz : ζ * star ζ = 1 := by
    calc
      ζ * star ζ = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, hζnorm]; norm_num
  have htriple :
      (β : ℂ) * (β⁻¹ : ℂ) * ζ + (β : ℂ) * (β⁻¹ : ℂ) * star ζ +
          (β : ℂ) * ζ * star ζ + (β⁻¹ : ℂ) * ζ * star ζ =
        (β : ℂ) + (β⁻¹ : ℂ) + ζ + star ζ := by
    rw [hbr]
    have hz1 : (β : ℂ) * ζ * star ζ = (β : ℂ) := by
      calc
        (β : ℂ) * ζ * star ζ = (β : ℂ) * (ζ * star ζ) := by ring
        _ = β := by rw [hzz]; ring
    have hz2' : (β : ℂ)⁻¹ * ζ * star ζ = (β : ℂ)⁻¹ := by
      calc
        (β : ℂ)⁻¹ * ζ * star ζ = (β : ℂ)⁻¹ * (ζ * star ζ) := by ring
        _ = (β : ℂ)⁻¹ := by rw [hzz]; ring
    have hz2 : (β⁻¹ : ℂ) * ζ * star ζ = (β⁻¹ : ℂ) := by
      simpa only [Complex.ofReal_inv] using hz2'
    rw [hz1, hz2]
    ring
  have hquad : (β : ℂ) * (β⁻¹ : ℂ) * ζ * star ζ = 1 := by
    calc
      (β : ℂ) * (β⁻¹ : ℂ) * ζ * star ζ =
          ((β : ℂ) * (β⁻¹ : ℂ)) * (ζ * star ζ) := by ring
      _ = 1 := by rw [hbr, hzz]; ring
  have hexpand :
      (Polynomial.X - Polynomial.C (β : ℂ)) *
      (Polynomial.X - Polynomial.C (β⁻¹ : ℂ)) *
      (Polynomial.X - Polynomial.C ζ) *
      (Polynomial.X - Polynomial.C (star ζ)) =
      Polynomial.X ^ 4 - Polynomial.C ((β : ℂ) + (β⁻¹ : ℂ) + ζ + star ζ) * Polynomial.X ^ 3 +
        Polynomial.C ((β : ℂ) * (β⁻¹ : ℂ) + (β : ℂ) * ζ +
          (β : ℂ) * star ζ + (β⁻¹ : ℂ) * ζ +
          (β⁻¹ : ℂ) * star ζ + ζ * star ζ) * Polynomial.X ^ 2 -
        Polynomial.C ((β : ℂ) * (β⁻¹ : ℂ) * ζ + (β : ℂ) * (β⁻¹ : ℂ) * star ζ +
          (β : ℂ) * ζ * star ζ + (β⁻¹ : ℂ) * ζ * star ζ) * Polynomial.X +
        Polynomial.C ((β : ℂ) * (β⁻¹ : ℂ) * ζ * star ζ) := by
    calc
      _ = Polynomial.X ^ 4 -
          (Polynomial.C (β : ℂ) + Polynomial.C (β⁻¹ : ℂ) + Polynomial.C ζ + Polynomial.C (star ζ)) * Polynomial.X ^ 3 +
          (Polynomial.C (β : ℂ) * Polynomial.C (β⁻¹ : ℂ) +
            Polynomial.C (β : ℂ) * Polynomial.C ζ + Polynomial.C (β : ℂ) * Polynomial.C (star ζ) +
            Polynomial.C (β⁻¹ : ℂ) * Polynomial.C ζ + Polynomial.C (β⁻¹ : ℂ) * Polynomial.C (star ζ) +
            Polynomial.C ζ * Polynomial.C (star ζ)) * Polynomial.X ^ 2 -
          (Polynomial.C (β : ℂ) * Polynomial.C (β⁻¹ : ℂ) * Polynomial.C ζ +
            Polynomial.C (β : ℂ) * Polynomial.C (β⁻¹ : ℂ) * Polynomial.C (star ζ) +
            Polynomial.C (β : ℂ) * Polynomial.C ζ * Polynomial.C (star ζ) +
            Polynomial.C (β⁻¹ : ℂ) * Polynomial.C ζ * Polynomial.C (star ζ)) * Polynomial.X +
          Polynomial.C (β : ℂ) * Polynomial.C (β⁻¹ : ℂ) * Polynomial.C ζ * Polynomial.C (star ζ) := by ring
      _ = _ := by
        simp only [Polynomial.C_add, Polynomial.C_mul]
  have hp_prod := quartic_prod_of_roots hmonic hdeg hrootβ hrootinv hrootζ hrootstar hβ hζim
  have hpmap : P.map (algebraMap ℤ ℂ) =
      Polynomial.X ^ 4 - Polynomial.C (A : ℂ) * Polynomial.X ^ 3 +
        Polynomial.C (B : ℂ) * Polynomial.X ^ 2 -
          Polynomial.C (A : ℂ) * Polynomial.X + 1 := by
    rw [hp_prod, hexpand]
    have hsum' : (β : ℂ) + (β⁻¹ : ℂ) + ζ + star ζ = (A : ℂ) := by
      simpa only [A, starRingEnd_apply] using hsum.symm
    have hpair' :
        (β : ℂ) * (β⁻¹ : ℂ) + (β : ℂ) * ζ +
            (β : ℂ) * star ζ + (β⁻¹ : ℂ) * ζ +
            (β⁻¹ : ℂ) * star ζ + ζ * star ζ = (B : ℂ) := by
      simpa only [B, starRingEnd_apply] using hpair.symm
    have htripleA :
        (β : ℂ) * (β⁻¹ : ℂ) * ζ + (β : ℂ) * (β⁻¹ : ℂ) * star ζ +
            (β : ℂ) * ζ * star ζ + (β⁻¹ : ℂ) * ζ * star ζ = (A : ℂ) :=
      htriple.trans hsum'
    rw [hsum', hpair', htripleA, hquad]
    simp only [Polynomial.C_1]
  have hmap_inj := Polynomial.map_injective (algebraMap ℤ ℂ) Int.cast_injective
  rcases hcase with h1 | h2
  · left
    apply hmap_inj
    rcases h1 with ⟨hA, hB⟩
    convert hpmap using 1 <;> norm_num [A, B, P1, hA, hB, map_neg,
      Polynomial.C_ofNat, Polynomial.C_neg] <;> ring
  · right
    apply hmap_inj
    rcases h2 with ⟨hA, hB⟩
    convert hpmap using 1 <;> norm_num [A, B, P2, hA, hB, map_neg,
      Polynomial.C_ofNat, Polynomial.C_neg] <;> ring



theorem quartic_classification_in_one_two {β : ℝ}
    (hquartic : IsQuarticSalemNumber β) (hβ2 : β < 2) :
    β = beta1 ∨ β = beta2 := by
  rcases hquartic with ⟨P, ζ, hmonic, hdeg, hirr, hβ, hrootβ, hrootinv,
    hrootζ, hrootstar, hnorm, him, hall⟩
  have hcase := quartic_coeff_case hmonic hdeg hrootβ hrootinv hrootζ hrootstar
    hβ hβ2 him hnorm
  have hpoly := quartic_polynomial_eq_case hmonic hdeg hrootβ hrootinv hrootζ hrootstar
    hβ him hnorm hcase
  rcases hpoly with hP1 | hP2
  · left
    rw [hP1] at hrootβ
    apply p1_root_unique_in_one_two hβ hβ2
    rw [Polynomial.IsRoot.def] at hrootβ
    have hm : (algebraMap ℝ ℂ) ((P1.map (algebraMap ℤ ℝ)).eval β) = 0 := by
      simpa [Polynomial.eval_map] using hrootβ
    exact (map_eq_zero_iff (algebraMap ℝ ℂ) Complex.ofReal_injective).mp hm
  · right
    rw [hP2] at hrootβ
    apply p2_root_unique_in_one_two hβ hβ2
    change (P2.map (algebraMap ℤ ℝ)).eval β = 0
    rw [Polynomial.IsRoot.def] at hrootβ
    have hm : (algebraMap ℝ ℂ) ((P2.map (algebraMap ℤ ℝ)).eval β) = 0 := by
      simpa [Polynomial.eval_map] using hrootβ
    exact (map_eq_zero_iff (algebraMap ℝ ℂ) Complex.ofReal_injective).mp hm



lemma quartic_ne_two {β : ℝ} (hquartic : IsQuarticSalemNumber β) : β ≠ 2 := by
  intro hβeq
  rcases hquartic with ⟨P, ζ, hmonic, hdeg, hirr, hβ, hrootβ, hrootinv,
    hrootζ, hrootstar, hnorm, him, hall⟩
  subst β
  let q : Polynomial ℚ := P.map (algebraMap ℤ ℚ)
  have hmap : q.map (algebraMap ℚ ℂ) = P.map (algebraMap ℤ ℂ) := by
    dsimp [q]
    rw [Polynomial.map_map]
    congr 1
  have hrootC : (q.map (algebraMap ℚ ℂ)).IsRoot (2 : ℂ) := by
    rw [hmap]
    exact hrootβ
  have hrootQ : q.IsRoot (2 : ℚ) := by
    rw [Polynomial.IsRoot.def] at hrootC ⊢
    have hm : (algebraMap ℚ ℂ) (q.eval (2 : ℚ)) = 0 := by
      simpa [Polynomial.eval_map] using hrootC
    exact (map_eq_zero_iff (algebraMap ℚ ℂ) Rat.cast_injective).mp hm
  have hqmonic : q.Monic := hmonic.map (algebraMap ℤ ℚ)
  have hdegq : q.degree = 4 := by
    rw [Polynomial.degree_eq_natDegree hqmonic.ne_zero,
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hdeg]
    norm_num
  have hdeg_one : q.degree = 1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hrootQ
  rw [hdegq] at hdeg_one
  norm_num at hdeg_one

end Salem.QuarticCore
