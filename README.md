# salem-dimension-drop-lean

A Lean 4 formalization of the main results of the paper
**"Strict Hausdorff-dimension drop for Quartic Salem Bernoulli convolutions"**
by Guozheng Cheng, Xiang Fang, Xueqing Ma and Hongli Zhang
([arXiv:2610.12072v2](https://arxiv.org/abs/2610.12072)),
relying only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

[![build](https://github.com/LUOLINGc325/salem-dimension-drop-lean/actions/workflows/build.yml/badge.svg)](https://github.com/LUOLINGc325/salem-dimension-drop-lean/actions/workflows/build.yml)
Reproduce: see [`.github/workflows/build.yml`](.github/workflows/build.yml).

> **Attribution.** The mathematics (theorems and proofs) is the work of the paper's authors. This repository is an
> *independent* Lean 4 formalization of the paper's two main theorems (version v2), carried out by the repository
> owner (LUOLINGc325) with AI coding agents. It is not affiliated with or endorsed by the paper's authors.

## What is formalized

For `β > 1` let `ν_{β⁻¹}` be the law of `W = Σ_{k≥0} ε_k β^{-k}` with independent fair signs `ε_k = ±1`.
The paper proves that this Bernoulli convolution has Hausdorff dimension strictly below one for every quartic Salem
number `β`, with explicit deficits for the two quartic Salem numbers in `(1, 2)`.

| Lean name | Paper |
|---|---|
| `Salem.main` | Theorem `thm:main`: `dimH ν_{β⁻¹} < 1` for every quartic Salem number `β` |
| `Salem.main_quantitative` | Theorem `thm:quantitative`: `dimH ν_{β₁⁻¹} < 1 - 1.4·10⁻²³`, `dimH ν_{β₂⁻¹} < 1 - 7.8·10⁻²²` |

Both statements and all definitions they use are in [`spec/STATEMENT.lean`](spec/STATEMENT.lean); the proofs are
assembled from the modules under [`Salem/`](Salem). The statements:

```lean
theorem main (β : ℝ) (hβ : IsQuarticSalemNumber β) :
    measureHausdorffDim (bernoulliConvolution β) < 1

theorem main_quantitative :
    measureHausdorffDim (bernoulliConvolution beta1) <
        (1 : ℝ≥0∞) - (14 : ℝ≥0∞) / 10 ^ 24 ∧
      measureHausdorffDim (bernoulliConvolution beta2) <
        (1 : ℝ≥0∞) - (78 : ℝ≥0∞) / 10 ^ 23
```

Reading notes (the Lean kernel certifies that the proofs prove *these* statements; whether the definitions
match the paper is for the reader to judge):
- `bernoulliConvolution β` is the push-forward of the infinite product of the fair sign law on `{1, -1}`
  (Mathlib's `Measure.infinitePi`) under `ω ↦ Σ' k, ω k * β⁻¹ ^ k`. The theorem
  `bernoulliConvolution_isBernoulliConvolution` proves that for `1 < β` it is a probability measure satisfying the
  self-similarity equation `μ = ½ · (x ↦ β⁻¹x + 1)_* μ + ½ · (x ↦ β⁻¹x - 1)_* μ`, so it is the genuine Bernoulli
  convolution (and not, e.g., the zero measure, for which the dimension below would be `⊤`).
- `measureHausdorffDim μ` is the paper's convention `inf { dimH A : A Borel, μ A = 1 }`, with Mathlib's `dimH`.
- `IsQuarticSalemNumber β`: there are a monic integer polynomial `P` of degree 4, irreducible over `ℚ`, and a
  non-real `ζ` with `‖ζ‖ = 1`, such that the complex roots of `P` are exactly `β`, `β⁻¹`, `ζ`, `ζ̄`, and `1 < β`.
- `beta1`, `beta2` are given by the explicit radicals of the paper (`u₁ = (1+√13)/2`, `u₂ = 1+√2`,
  `βᵢ = (uᵢ + √(uᵢ² - 4))/2`); the theorems `isQuarticSalemNumber_beta1/2` prove that they are quartic Salem numbers
  (roots of `P₁ = X⁴-X³-X²-X+1` and `P₂ = X⁴-2X³+X²-2X+1`). The deficits are stated as the exact rationals
  `14/10²⁴` and `78/10²³`.

**Differences from the paper's proof.** The paper proves Theorem `thm:main` without numerical computation and
derives Theorem `thm:quantitative` from finite calculations checked by programs. In Lean, all finite calculations
are carried out inside Lean (rational interval arithmetic, checked by `decide`/kernel reduction, no `native_decide`),
and `main` is derived from the two quantitative covers together with the classification of quartic Salem numbers
(either `β ≥ 2`, where an elementary covering bound applies, or `β ∈ {β₁, β₂}`). No program outside Lean is used.

## Verification

The [build workflow](.github/workflows/build.yml) of this repository builds every module from a clean checkout
(Mathlib from its official cache), fails on any `sorry` warning, and checks with `#print axioms` that `Salem.main`,
`Salem.main_quantitative` and the three guard theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

Before this release, the development commit `4f0462a74ede405f7a42b1c38d20e599b12f388e` (proof commit `87a6599`,
later commits Markdown-only) passed an independent acceptance run (GitHub Actions run 40872718270 in a private CI
repository; its harness is not shipped here). Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

| Check | Result |
|---|---|
| Clean `lake build` of all 101 project modules | PASS: exit 0, 0 `sorry` warnings (about 34 min on a hosted runner, Mathlib cache) |
| Statement identity | PASS: every non-internal constant of the authorized frozen statement file (21: all definitions, the two endpoints and the three guards) has a structurally identical type, and for definitions an identical value, in the proved build |
| Axioms | PASS: `main` (66,080 constants traversed), `main_quantitative` (63,210) and the three guards depend only on `propext`, `Classical.choice`, `Quot.sound`; no axiom is declared in any project module |
| Kernel replay | PASS: all 101 modules re-checked by the Lean kernel (`Environment.replay`), 0 failures |
| Source scan (comments stripped) | PASS: no `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern`, `debug.skipKernelTC` |

This repository contains that tree minus the 23 modules outside the import closure of `spec/STATEMENT.lean`
(earlier, unused development modules) and the development notes, plus `README.md`, `LICENSE`, `NOTICE`, `scripts/`
and `.github/`. In `spec/STATEMENT.lean`, the module header comment was updated and one unused definition,
`IsSalemNumber` (a general Salem-number predicate that is too permissive: it admits reciprocal quadratic units),
was removed; it does not occur in the dependencies of either main theorem or of the guards, which use
`IsQuarticSalemNumber`. The build workflow of this repository passed on this tree.

## Building

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`).

## License

Apache-2.0, see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
