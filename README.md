# Stochastic Domination of Gaussian Maxima in Lean

[![Lean CI](https://github.com/abhmul/weak-simplex-conjecture-lean/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/abhmul/weak-simplex-conjecture-lean/actions/workflows/lean_action_ci.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2607.14087-b31b1b.svg)](https://arxiv.org/abs/2607.14087)

This repository contains a companion Lean 4 formalization of the Gaussian stochastic-domination theorem and its application to the Weak Simplex Conjecture in [*Stochastic Domination of Gaussian Maxima: A Resolution of the Weak Simplex Conjecture*](https://arxiv.org/abs/2607.14087) by Abhijeet Mulgund. The development also certifies strictness and the equality cases needed for uniqueness of the regular-simplex Gram matrix. It uses [mathlib](https://github.com/leanprover-community/mathlib4) and is pinned to Lean 4.31.0.

## Main results

For $m\geq 2$, let `R` be an `m × m` correlation matrix satisfying

$$
R - \frac{1}{m}\mathbf{1}\mathbf{1}^{\mathsf T} \succeq 0.
$$

If $X\sim\mathcal N(0,R)$ and $Z_1,\ldots,Z_m$ are independent standard Gaussian random variables, the main theorem proves

$$
\max_i X_i \leq_{\mathrm{st}} \max_i Z_i,
$$

or equivalently, for every $c\in\mathbb R$,

$$
\mathbb P[X_i\leq c\text{ for every }i]\geq\Phi(c)^m.
$$

The comparison is for equal-threshold lower orthants; it does not assert an analogous inequality for arbitrary threshold vectors.

The comparison is strict at every finite threshold when `R ≠ I`, and equality at any one finite threshold holds if and only if `R = I`. Consequently, every positive exponential moment of the Gaussian coordinate maximum is strictly smaller away from independence.

| Result | Lean declaration | Source |
|---|---|---|
| Theorem 2.1, lower-orthant and stochastic-order forms | `lowerOrthant_ge_iid`, `coordinateMax_tail_le_iid` | [`Orthant/Singular.lean`](WeakSimplexConjectureLean/Orthant/Singular.lean), [`Maxima/StochasticOrder.lean`](WeakSimplexConjectureLean/Maxima/StochasticOrder.lean) |
| Strict lower-orthant and equality characterization | `lowerOrthant_gt_iid_of_ne_one`, `lowerOrthant_eq_iid_iff` | [`Orthant/Strict.lean`](WeakSimplexConjectureLean/Orthant/Strict.lean) |
| Strict Gaussian-maximum MGF comparison and equality characterization for `mu > 0` | `gaussianMax_mgf_lt_regularSimplex`, `gaussianMax_mgf_eq_regularSimplex_iff` | [`Maxima/StrictExponentialMoments.lean`](WeakSimplexConjectureLean/Maxima/StrictExponentialMoments.lean) |
| Corollary 2.3, Gaussian-maximum MGF comparison | `gramGaussianMax_mgf_le_regularSimplex` | [`Coding/RegularSimplex.lean`](WeakSimplexConjectureLean/Coding/RegularSimplex.lean) |
| Strict Gram-level MGF comparison and equality characterization for `lam > 0` | `gramGaussianMax_mgf_lt_regularSimplex`, `gramGaussianMax_mgf_eq_regularSimplex_iff` | [`Coding/RegularSimplex.lean`](WeakSimplexConjectureLean/Coding/RegularSimplex.lean) |
| Corollary 2.4, Weak Simplex Conjecture | `weak_simplex`, `weak_simplex_of_scoreMaximizingDecoders` | [`Coding/WeakSimplex.lean`](WeakSimplexConjectureLean/Coding/WeakSimplex.lean) |
| Operational strictness and equality characterization for `lam > 0` | `weak_simplex_strict`, `weak_simplex_eq_iff_codeGram_eq`, `weak_simplex_strict_of_scoreMaximizingDecoders`, `weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders` | [`Coding/WeakSimplex.lean`](WeakSimplexConjectureLean/Coding/WeakSimplex.lean) |

The final coding theorems cover arbitrary measurable pointwise score-maximizing tie-breaking rules. The more general identity [`decoderSuccessOf_eq_bayesValue`](WeakSimplexConjectureLean/Coding/MLDecoder.lean) shows that every measurable likelihood-maximizing decoder has the same success probability, without assuming distinct codewords or null tie sets. The non-strict comparison permits zero signal strength. Strictness and uniqueness require `lam > 0`; uniqueness is false at `lam = 0` because every codebook has the same value there.

A regular simplex is supplied to the final theorem through the exact Gram-matrix condition `codeGram simplex = regularSimplexGram (n + 1)`. At positive signal strength, equality in Bayes/ML success is equivalent to `codeGram code = regularSimplexGram (n + 1)`, both for the deterministic tie-safe ML decoder and for arbitrary measurable score-maximizing decoders. This is uniqueness at the Gram-matrix level. A separate theorem identifying equal-Gram realizations up to orthogonal congruence is optional and is not part of the certified core result; the repository also does not separately construct a coordinate realization of the regular-simplex Gram matrix.

## Scope

The formalization includes the proof chain for the equal-threshold stochastic comparison, its strict and equality cases, its Gaussian-maximum MGF consequences, the Bayes/maximum-likelihood identity, and the Weak Simplex Conjecture with Gram-level uniqueness. It includes adaptive tilting, the centered log-concave product inequality needed by the proof, positive-definite and singular covariance arguments, and measurable treatment of decoder ties.

The paper's general monotone-function corollary, Simplex Mean Width corollary, and unrestricted finite-energy AWGN formula are not formalized here as standalone Lean theorems. The general centered product inequality remains restricted to positive-definite covariance. The uniqueness branch makes exactly two narrow departures from handling singular covariance only at the outer lower-orthant theorem: `centered_product_of_continuous` supplies a non-strict singular limit for continuous factors after the strict sum-difference step, yielding a strict theorem only for the specialized adaptive centered half-lines; and `exists_adaptiveWitnesses_of_weakSimplexCov` constructs singular adaptive witnesses as compact limits of positive-definite witnesses. These results do not constitute a generic singular centered-product strictness or equality theory.

## Building

Install Lean using the [official instructions](https://lean-lang.org/install/), then clone the repository:

```bash
git clone https://github.com/abhmul/weak-simplex-conjecture-lean.git
cd weak-simplex-conjecture-lean
```

The repository pins Lean and all Lake dependencies. Downloading the mathlib cache is optional but substantially reduces build time:

```bash
lake exe cache get
lake build --wfail
```

## Checking the proof

The project-owned production source builds without `sorry`, `admit`, project-defined axioms, unsafe declarations, or `native_decide`. The permanent audit file prints the transitive axioms of the public results:

```bash
python3 scripts/check_axiom_audit.py
```

Every audited declaration uses exactly Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. Continuous integration also builds the public root, checks the production import graph, runs the trusted-source scanner, and verifies the provenance ledger.

Deterministic floating-point sanity checks for the strict and equality cases are available separately:

```bash
python3 scripts/check_uniqueness_sanity.py
```

These diagnostics are not proof dependencies and are outside the trusted Lean development.

## Repository structure

- [`WeakSimplexConjectureLean/`](WeakSimplexConjectureLean/) contains the formalization. The principal proof branches are under `Tilt/`, `Product/`, `Orthant/`, `Maxima/`, and `Coding/`.
- [`WeakSimplexConjectureLean.lean`](WeakSimplexConjectureLean.lean) is the public umbrella import.
- [`WeakSimplexConjectureLean/Audit/Axioms.lean`](WeakSimplexConjectureLean/Audit/Axioms.lean) is the permanent axiom audit.
- [`WeakSimplexConjectureLean/Vendor/`](WeakSimplexConjectureLean/Vendor/) contains the minimal vendored StatLean source used by the proof; [`PROVENANCE.md`](PROVENANCE.md) records exact revisions, changes, licenses, and audit results.
- [`Scratch/`](Scratch/) preserves research experiments and upstream snapshots. It is not imported by the production library.
- [`docs/theorem-dependencies.md`](docs/theorem-dependencies.md) gives the principal theorem dependency graph; [`docs/`](docs/) and [`notes/`](notes/) also contain development records, architecture notes, and historical mathematical source material.

## Citation

If you use this formalization, please cite the accompanying paper. Machine-readable software and preferred-paper citation metadata are provided in [`CITATION.cff`](CITATION.cff).

```bibtex
@misc{mulgund2026stochastic,
  title        = {Stochastic Domination of Gaussian Maxima: A Resolution of the Weak Simplex Conjecture},
  author       = {Abhijeet Mulgund},
  year         = {2026},
  eprint       = {2607.14087},
  archivePrefix = {arXiv},
  primaryClass = {math.PR},
  doi          = {10.48550/arXiv.2607.14087},
  url          = {https://arxiv.org/abs/2607.14087}
}
```

Questions, corrections, and reproducibility reports are welcome through [GitHub issues](https://github.com/abhmul/weak-simplex-conjecture-lean/issues).

## Acknowledgements

The accompanying paper acknowledges support from the National Science Foundation under awards 2240532 and 2217023. This formalization relies on mathlib and on a small audited source closure from [StatLean](https://github.com/StatLean/Stat-Lean).

## License

Project-authored code is released under the [MIT License](LICENSE). Vendored StatLean code and copied research artifacts retain their upstream Apache-2.0 licenses; see [`PROVENANCE.md`](PROVENANCE.md) and the [`Scratch/WP01` provenance ledger](Scratch/WP01/README.md).
