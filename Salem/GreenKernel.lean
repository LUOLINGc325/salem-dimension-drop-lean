module

public import Mathlib

@[expose] public section

open scoped BigOperators
open Polynomial
namespace Salem
theorem four_nodal_residue_moment {F : Type*} [Field F]
    (r : Fin 4 → F) (hr : Function.Injective r) (m : ℕ) (hm : m < 4) :
    (∑ i : Fin 4, ((Lagrange.nodal Finset.univ r).derivative.eval (r i))⁻¹ * r i ^ m) =
      if m = 3 then 1 else 0 := by
  have hdeg : (Polynomial.X ^ m : Polynomial F).degree <
      (Finset.univ : Finset (Fin 4)).card := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hm
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := r) hr.injOn hdeg
  have hden (i : Fin 4) :
      ((Lagrange.nodal Finset.univ r).derivative.eval (r i)) =
        ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, (r i - r j) := by
    rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.reduceSub, Polynomial.coeff_X_pow,
    Polynomial.eval_pow, Polynomial.eval_X] at h
  simpa [hden, div_eq_mul_inv, mul_comm, eq_comm] using h.symm

/-- Lagrange's coefficient identity, in the derivative-residue convention
used by the bilateral Green sequence. -/
theorem four_root_residue_moment {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (hr : Function.Injective r)
    (hP : P = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (r i)))
    (m : ℕ) (hm : m < 4) :
    (∑ i : Fin 4, (P.derivative.eval (r i))⁻¹ * r i ^ m) =
      if m = 3 then 1 else 0 := by
  have hn : P = Lagrange.nodal Finset.univ r := by simpa [Lagrange.nodal] using hP
  rw [hn]
  exact four_nodal_residue_moment r hr m hm

/-- Every derivative denominator of a distinct four-root factorization is nonzero. -/
theorem four_root_derivative_ne_zero {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (hr : Function.Injective r)
    (hP : P = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (r i))) (i : Fin 4) :
    P.derivative.eval (r i) ≠ 0 := by
  have hn : P = Lagrange.nodal Finset.univ r := by simpa [Lagrange.nodal] using hP
  rw [hn]
  have hw := Lagrange.nodalWeight_ne_zero (s := Finset.univ) (v := r) hr.injOn (Finset.mem_univ i)
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i)] at hw
  exact fun h => hw (by rw [h, inv_zero])

/-- The exact spectral trace `T_m=∑λ λ^m/P′(λ)` for four labeled roots. -/
noncomputable def quarticResidueTrace {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (m : ℤ) : F :=
  ∑ i : Fin 4, (P.derivative.eval (r i))⁻¹ * r i ^ m

/-- The four initial trace values come from interpolation, not an assumed
residue identity.  Negative-index integrality is a separate recurrence step. -/
theorem quarticResidueTrace_initial {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (hr : Function.Injective r)
    (hP : P = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (r i))) :
    quarticResidueTrace P r 0 = 0 ∧ quarticResidueTrace P r 1 = 0 ∧
      quarticResidueTrace P r 2 = 0 ∧ quarticResidueTrace P r 3 = 1 := by
  have h0 := four_root_residue_moment P r hr hP 0 (by decide)
  have h1 := four_root_residue_moment P r hr hP 1 (by decide)
  have h2 := four_root_residue_moment P r hr hP 2 (by decide)
  have h3 := four_root_residue_moment P r hr hP 3 (by decide)
  simpa [quarticResidueTrace] using And.intro h0 (And.intro h1 (And.intro h2 h3))

/-- The forward-shift reciprocal quartic recurrence from the source. -/
noncomputable def reciprocalQuarticOperator {F : Type*} [Field F]
    (A B : F) (f : ℤ → F) (t : ℤ) : F :=
  f (t + 4) - A * f (t + 3) + B * f (t + 2) - A * f (t + 1) + f t
theorem reciprocalQuarticOperator_add {F : Type*} [Field F]
    (A B : F) (f g : ℤ → F) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => f i + g i) t =
      reciprocalQuarticOperator A B f t + reciprocalQuarticOperator A B g t := by
  dsimp [reciprocalQuarticOperator]
  ring
theorem reciprocalQuarticOperator_mode {F : Type*} [Field F]
    {A B z : F} (hz : z ≠ 0)
    (hroot : z ^ 4 - A * z ^ 3 + B * z ^ 2 - A * z + 1 = 0)
    (c : F) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => c * z ^ (i - 1)) t = 0 := by
  have hp (k : ℤ) : z ^ (t + k - 1) = z ^ (t - 1) * z ^ k := by
    rw [show t + k - 1 = (t - 1) + k by omega, zpow_add₀ hz]
  have h4 := hp 4
  have h3 := hp 3
  have h2 := hp 2
  have h1 := hp 1
  norm_num only [zpow_ofNat] at h4 h3 h2 h1
  dsimp [reciprocalQuarticOperator]
  rw [h4, h3, h2, h1]
  linear_combination c * z ^ (t - 1) * hroot
theorem quarticResidueTrace_shift_recurrence {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) {A B : F}
    (hr0 : ∀ i, r i ≠ 0)
    (hroot : ∀ i, r i ^ 4 - A * r i ^ 3 + B * r i ^ 2 - A * r i + 1 = 0) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => quarticResidueTrace P r (i - 1)) t = 0 := by
  have hsum : (∑ j : Fin 4, reciprocalQuarticOperator A B
      (fun i => (P.derivative.eval (r j))⁻¹ * r j ^ (i - 1)) t) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact reciprocalQuarticOperator_mode (hr0 j) (hroot j) _ t
  simpa only [reciprocalQuarticOperator, quarticResidueTrace, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum] using hsum
theorem reciprocalQuarticOperator_cutoff {F : Type*} [Field F]
    (A B : F) (T : ℤ → F) (hT0 : T 0 = 0) (hT1 : T 1 = 0)
    (hT2 : T 2 = 0) (hT3 : T 3 = 1)
    (hrec : ∀ t, reciprocalQuarticOperator A B (fun i => T (i - 1)) t = 0) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => if i ≤ 0 then 0 else T (i - 1)) t =
      if t = 0 then 1 else 0 := by
  by_cases hlo : t ≤ -4
  · have h4 : t + 4 ≤ 0 := by omega
    have h3 : t + 3 ≤ 0 := by omega
    have h2 : t + 2 ≤ 0 := by omega
    have h1 : t + 1 ≤ 0 := by omega
    have h0 : t ≤ 0 := by omega
    have hn : t ≠ 0 := by omega
    simp [reciprocalQuarticOperator, h4, h3, h2, h1, h0, hn]
  · by_cases hhi : 1 ≤ t
    · have h4 : ¬t + 4 ≤ 0 := by omega
      have h3 : ¬t + 3 ≤ 0 := by omega
      have h2 : ¬t + 2 ≤ 0 := by omega
      have h1 : ¬t + 1 ≤ 0 := by omega
      have h0 : ¬t ≤ 0 := by omega
      have hn : t ≠ 0 := by omega
      simpa [reciprocalQuarticOperator, h4, h3, h2, h1, h0, hn] using hrec t
    · have ht : t = -3 ∨ t = -2 ∨ t = -1 ∨ t = 0 := by omega
      rcases ht with rfl | rfl | rfl | rfl <;>
        norm_num [reciprocalQuarticOperator, hT0, hT1, hT2, hT3]
/-- Bilateral Green sequence with one expanding root singled out.
Its right branch is the sum over the remaining three roots. -/
noncomputable def quarticSpectralGreen {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) (i : ℤ) : F :=
  -(P.derivative.eval (r e))⁻¹ * r e ^ (i - 1) +
    if i ≤ 0 then 0 else quarticResidueTrace P r (i - 1)
/-- The actual spectral Green sequence has exactly one unit impulse.
The four junction cancellations follow from the proved Lagrange residues. -/
theorem quarticSpectralGreen_forcing {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) (hr : Function.Injective r)
    (hP : P = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (r i)))
    {A B : F} (hr0 : ∀ i, r i ≠ 0)
    (hroot : ∀ i, r i ^ 4 - A * r i ^ 3 + B * r i ^ 2 - A * r i + 1 = 0) (t : ℤ) :
    reciprocalQuarticOperator A B (quarticSpectralGreen P r e) t =
      if t = 0 then 1 else 0 := by
  obtain ⟨hT0, hT1, hT2, hT3⟩ := quarticResidueTrace_initial P r hr hP
  have hrec := quarticResidueTrace_shift_recurrence P r hr0 hroot
  have hcut := reciprocalQuarticOperator_cutoff A B (quarticResidueTrace P r)
    hT0 hT1 hT2 hT3 hrec t
  change reciprocalQuarticOperator A B
    (fun i => (-(P.derivative.eval (r e))⁻¹ * r e ^ (i - 1)) +
      (if i ≤ 0 then 0 else quarticResidueTrace P r (i - 1))) t = _
  rw [reciprocalQuarticOperator_add, reciprocalQuarticOperator_mode (hr0 e) (hroot e), zero_add]
  exact hcut

/-- The expanding left branch, with the exact source index `i-1`. -/
theorem quarticSpectralGreen_left {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) {i : ℤ} (hi : i ≤ 0) :
    quarticSpectralGreen P r e i = -(P.derivative.eval (r e))⁻¹ * r e ^ (i - 1) := by
  simp [quarticSpectralGreen, hi]

/-- The right branch is exactly the other three derivative-weighted modes. -/
theorem quarticSpectralGreen_right {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) {i : ℤ} (hi : 0 < i) :
    quarticSpectralGreen P r e i =
      ∑ j ∈ (Finset.univ : Finset (Fin 4)).erase e,
        (P.derivative.eval (r j))⁻¹ * r j ^ (i - 1) := by
  have hs := Finset.add_sum_erase (Finset.univ : Finset (Fin 4))
    (fun j => (P.derivative.eval (r j))⁻¹ * r j ^ (i - 1)) (Finset.mem_univ e)
  dsimp [quarticSpectralGreen, quarticResidueTrace]
  rw [ite_eq_right (by omega : ¬i ≤ 0), ← hs]
  ring

theorem reciprocalQuarticOperator_const_mul {F : Type*} [Field F]
    (A B c : F) (g : ℤ → F) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => c * g i) t = c * reciprocalQuarticOperator A B g t := by
  dsimp [reciprocalQuarticOperator]
  ring
theorem reciprocalQuarticOperator_sum {F ι : Type*} [Field F]
    (A B : F) (s : Finset ι) (f : ι → ℤ → F) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => ∑ j ∈ s, f j i) t =
      ∑ j ∈ s, reciprocalQuarticOperator A B (f j) t := by
  simp only [reciprocalQuarticOperator, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
theorem reciprocalQuarticOperator_translate {F : Type*} [Field F]
    (A B : F) (g : ℤ → F) (a t : ℤ) :
    reciprocalQuarticOperator A B (fun i => g (i - a)) t =
      reciprocalQuarticOperator A B g (t - a) := by
  dsimp [reciprocalQuarticOperator]
  rw [show t + 4 - a = t - a + 4 by omega,
    show t + 3 - a = t - a + 3 by omega,
    show t + 2 - a = t - a + 2 by omega,
    show t + 1 - a = t - a + 1 by omega]
/-- A finite weighted sum of integer translates of a Green sequence. -/
noncomputable def finiteGreenConvolution {F ι : Type*} [Field F]
    (s : Finset ι) (shift : ι → ℤ) (k : ι → F) (g : ℤ → F) (i : ℤ) : F :=
  ∑ j ∈ s, k j * g (i - shift j)
theorem finiteGreenConvolution_operator {F ι : Type*} [Field F]
    (A B : F) (s : Finset ι) (shift : ι → ℤ) (k : ι → F) (g : ℤ → F) (t : ℤ) :
    reciprocalQuarticOperator A B (finiteGreenConvolution s shift k g) t =
      ∑ j ∈ s, k j * reciprocalQuarticOperator A B g (t - shift j) := by
  change reciprocalQuarticOperator A B (fun i => ∑ j ∈ s, k j * g (i - shift j)) t = _
  rw [reciprocalQuarticOperator_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [reciprocalQuarticOperator_const_mul, reciprocalQuarticOperator_translate]
/-- Exact propagation of a Green impulse through an arbitrary finite
weighted convolution, with no support or coefficient cancellation assumed. -/
theorem finiteGreenConvolution_forcing {F ι : Type*} [Field F]
    (A B : F) (s : Finset ι) (shift : ι → ℤ) (k : ι → F) (g : ℤ → F)
    (hg : ∀ t, reciprocalQuarticOperator A B g t = if t = 0 then 1 else 0) (t : ℤ) :
    reciprocalQuarticOperator A B (finiteGreenConvolution s shift k g) t =
      ∑ j ∈ s, if t = shift j then k j else 0 := by
  rw [finiteGreenConvolution_operator]
  simp_rw [hg, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- Exact expanding coefficient of a finite Green convolution to the
left of all its forcing shifts. -/
theorem finiteGreenConvolution_left {F ι : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) (hr : r e ≠ 0)
    (s : Finset ι) (shift : ι → ℤ) (k : ι → F) (t : ℤ)
    (ht : ∀ j ∈ s, t ≤ shift j) :
    finiteGreenConvolution s shift k (quarticSpectralGreen P r e) t =
      -(P.derivative.eval (r e))⁻¹ * r e ^ (t - 1) * ∑ j ∈ s, k j * r e ^ (-shift j) := by
  rw [finiteGreenConvolution, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quarticSpectralGreen_left P r e (show t - shift j ≤ 0 by have := ht j hj; omega)]
  have hp : r e ^ (t - shift j - 1) = r e ^ (t - 1) * r e ^ (-shift j) := by
    rw [show t - shift j - 1 = (t - 1) + (-shift j) by omega, zpow_add₀ hr]
  rw [hp]
  ring
/-- Exact stable and neutral spectral coefficients to the right of all
forcing shifts.  The Laurent polynomial is evaluated at the inverse roots. -/
theorem finiteGreenConvolution_right {F ι : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) (hr : ∀ a, r a ≠ 0)
    (s : Finset ι) (shift : ι → ℤ) (k : ι → F) (t : ℤ)
    (ht : ∀ j ∈ s, shift j < t) :
    finiteGreenConvolution s shift k (quarticSpectralGreen P r e) t =
      ∑ a ∈ (Finset.univ : Finset (Fin 4)).erase e,
        (P.derivative.eval (r a))⁻¹ * r a ^ (t - 1) * ∑ j ∈ s, k j * r a ^ (-shift j) := by
  calc
    _ = ∑ j ∈ s, k j * ∑ a ∈ (Finset.univ : Finset (Fin 4)).erase e,
        (P.derivative.eval (r a))⁻¹ * r a ^ (t - shift j - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [quarticSpectralGreen_right P r e (show 0 < t - shift j by have := ht j hj; omega)]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro j hj
      rw [show t - shift j - 1 = (t - 1) + (-shift j) by omega, zpow_add₀ (hr a)]
      ring

/-- Four initial values and matching quartic recurrence values determine
a finite orbit window.  This is used to identify a Green construction with
the independently centered seed core. -/
theorem finite_reciprocalQuartic_agreement {F : Type*} [Field F] {A B : F} {f g : ℕ → F} {N : ℕ}
    (hbase : ∀ n < 4, f n = g n)
    (hrec : ∀ n, n + 4 < N →
      f (n + 4) - A * f (n + 3) + B * f (n + 2) - A * f (n + 1) + f n =
      g (n + 4) - A * g (n + 3) + B * g (n + 2) - A * g (n + 1) + g n) :
    ∀ n < N, f n = g n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn4 : n < 4
    · exact hbase n hn4
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (m := 4) (n := n) (by omega)
      have hi0 := ih k (by omega) (by omega)
      have hi1 := ih (k + 1) (by omega) (by omega)
      have hi2 := ih (k + 2) (by omega) (by omega)
      have hi3 := ih (k + 3) (by omega) (by omega)
      have hs := hrec k (by omega)
      rw [hi0, hi1, hi2, hi3] at hs
      have hnval : n = k + 4 := by omega
      rw [hnval]
      linear_combination hs

noncomputable def reciprocalQuarticDerivativeValue {F : Type*} [Field F] (A B x : F) : F :=
  4 * x ^ 3 - 3 * A * x ^ 2 + 2 * B * x - A
theorem reciprocalQuarticDerivative_inv {F : Type*} [Field F] {A B x : F} (hx : x ≠ 0)
    (hroot : x ^ 4 - A * x ^ 3 + B * x ^ 2 - A * x + 1 = 0) :
    reciprocalQuarticDerivativeValue A B x⁻¹ =
      -(x⁻¹) ^ 2 * reciprocalQuarticDerivativeValue A B x := by
  dsimp [reciprocalQuarticDerivativeValue]
  field_simp [hx]
  linear_combination 4 * hroot
theorem reciprocalQuartic_inverse_derivative_inv {F : Type*} [Field F] {A B x : F} (hx : x ≠ 0)
    (hroot : x ^ 4 - A * x ^ 3 + B * x ^ 2 - A * x + 1 = 0) :
    (reciprocalQuarticDerivativeValue A B x⁻¹)⁻¹ =
      -x ^ 2 * (reciprocalQuarticDerivativeValue A B x)⁻¹ := by
  rw [reciprocalQuarticDerivative_inv hx hroot]
  simp [mul_inv_rev]
  ring

/-- The stable derivative-weighted mode is the reflected expanding mode,
with the source reflection index four. -/
theorem reciprocalQuarticStableMode_reflection {F : Type*} [Field F] {A B x : F} (hx : x ≠ 0)
    (hroot : x ^ 4 - A * x ^ 3 + B * x ^ 2 - A * x + 1 = 0) (Q : F) (t : ℤ) :
    (reciprocalQuarticDerivativeValue A B x⁻¹)⁻¹ * (x⁻¹) ^ (t - 1) * Q =
      -(reciprocalQuarticDerivativeValue A B x)⁻¹ * x ^ ((4 - t) - 1) * Q := by
  rw [reciprocalQuartic_inverse_derivative_inv hx hroot]
  have hp : x ^ 2 * (x⁻¹) ^ (t - 1) = x ^ ((4 - t) - 1) := by
    rw [inv_zpow', show x ^ 2 = x ^ (2 : ℤ) by norm_num, ← zpow_add₀ hx]
    congr 1
    omega
  calc
    (-x ^ 2 * (reciprocalQuarticDerivativeValue A B x)⁻¹) * (x⁻¹) ^ (t - 1) * Q =
      -(reciprocalQuarticDerivativeValue A B x)⁻¹ * (x ^ 2 * (x⁻¹) ^ (t - 1)) * Q := by ring
    _ = _ := by rw [hp]

/-- The first three trace residues vanish, so the expanding Green branch
actually extends through indices one, two and three. -/
theorem quarticSpectralGreen_left_extended {F : Type*} [Field F]
    (P : Polynomial F) (r : Fin 4 → F) (e : Fin 4) (hr : Function.Injective r)
    (hP : P = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (r i))) {i : ℤ} (hi : i ≤ 3) :
    quarticSpectralGreen P r e i = -(P.derivative.eval (r e))⁻¹ * r e ^ (i - 1) := by
  by_cases hi0 : i ≤ 0
  · exact quarticSpectralGreen_left P r e hi0
  · obtain ⟨hT0, hT1, hT2, hT3⟩ := quarticResidueTrace_initial P r hr hP
    have hc : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl <;>
      norm_num [quarticSpectralGreen, hT0, hT1, hT2]

theorem reciprocalQuarticOperator_sub {F : Type*} [Field F]
    (A B : F) (f g : ℤ → F) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => f i - g i) t =
      reciprocalQuarticOperator A B f t - reciprocalQuarticOperator A B g t := by
  dsimp [reciprocalQuarticOperator]
  ring
theorem reciprocalQuarticOperator_reflection {F : Type*} [Field F]
    (A B : F) (f : ℤ → F) (k t : ℤ) :
    reciprocalQuarticOperator A B (fun i => f (k - i)) t =
      reciprocalQuarticOperator A B f (k - t - 4) := by
  dsimp [reciprocalQuarticOperator]
  rw [show k - t - 4 + 4 = k - t by omega,
    show k - t - 4 + 3 = k - (t + 1) by omega,
    show k - t - 4 + 2 = k - (t + 2) by omega,
    show k - t - 4 + 1 = k - (t + 3) by omega,
    show k - t - 4 = k - (t + 4) by omega]
  ring
/-- Matching reciprocal quartic recurrences and exact agreement on an
incoming half-line determine the entire bilateral sequence. -/
theorem reciprocalQuartic_eq_of_left {F : Type*} [Field F] {A B : F} {f g : ℤ → F} {a : ℤ}
    (hleft : ∀ t ≤ a, f t = g t)
    (hrec : ∀ t, reciprocalQuarticOperator A B f t = reciprocalQuarticOperator A B g t) :
    ∀ t, f t = g t := by
  intro t
  by_cases ht : t ≤ a
  · exact hleft t ht
  · let n : ℕ := (t - (a - 3)).toNat
    have hn : a - 3 + (n : ℤ) = t := by dsimp [n]; omega
    let fN : ℕ → F := fun k => f (a - 3 + (k : ℤ))
    let gN : ℕ → F := fun k => g (a - 3 + (k : ℤ))
    have heq : ∀ k < n + 1, fN k = gN k := by
      apply finite_reciprocalQuartic_agreement (A := A) (B := B)
      · intro k hk
        exact hleft _ (by omega)
      · intro k hk
        have hs := hrec (a - 3 + (k : ℤ))
        have h4 : a - 3 + ((k + 4 : ℕ) : ℤ) = a - 3 + (k : ℤ) + 4 := by omega
        have h3 : a - 3 + ((k + 3 : ℕ) : ℤ) = a - 3 + (k : ℤ) + 3 := by omega
        have h2 : a - 3 + ((k + 2 : ℕ) : ℤ) = a - 3 + (k : ℤ) + 2 := by omega
        have h1 : a - 3 + ((k + 1 : ℕ) : ℤ) = a - 3 + (k : ℤ) + 1 := by omega
        dsimp only [fN, gN]
        rw [h4, h3, h2, h1]
        exact hs
    have h := heq n (by omega)
    change f (a - 3 + (n : ℤ)) = g (a - 3 + (n : ℤ)) at h
    rwa [hn] at h

theorem reciprocalQuarticOperator_re (A B : ℝ) (f : ℤ → ℂ) (t : ℤ) :
    reciprocalQuarticOperator A B (fun i => (f i).re) t =
      (reciprocalQuarticOperator (A : ℂ) (B : ℂ) f t).re := by
  simp [reciprocalQuarticOperator, Complex.mul_re]

end Salem
