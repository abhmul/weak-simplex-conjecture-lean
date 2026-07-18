# Weak Simplex Conjecture Lean Formalization

Formalization of the matrix-form Gaussian lower-orthant inequality and its reduction to the weak simplex conjecture. The governing architecture and trust policy are in [`docs/weak_simplex_lean_formalization_report.v3-reassessment.md`](docs/weak_simplex_lean_formalization_report.v3-reassessment.md).

## Status

WP00–WP24 are complete, closing the M0 reproducible foundation, the adaptive branch through
compatible variational witnesses and centered tilted half-lines, the Gaussian exponential-shift
bridge, the conditional positive-definite lower-orthant theorem, and the Prékopa/log-concavity
foundation, symmetric-rectangle theorem, even-factor layer cake, normalized self-convolution,
sum–difference deficit, and dyadic CLT interfaces of the product branch.
The repository now contains the frozen finite/matrix interfaces, standard-normal and scalar-tilt
calculus, positive-definite quadratic coercivity, the rank-one inverse bound, a global unconstrained
adaptive-potential maximizer, coordinate stationarity, compatibility and value identities,
`AdaptiveWitnesses`, an audited finite-dimensional Prékopa–Leindler port, positive-semidefinite
Gaussian-kernel log-concavity, measurable marginalization, convolution closure, the PSD Gaussian
measure shift and lintegral corollary, centered half-line mass and zero-barycenter identities, and
adaptive event-shift algebra, plus the positive-definite symmetric Gaussian rectangle inequality.
The product branch now also contains the bounded even log-concave factor inequality, the analytic
normalized self-convolution closure properties, its exact normalized-average measure law, and
preservation of mass one, zero Gaussian barycenter, and variance. It also contains the exact joint
Gaussian sum–difference product law, the one-step inequality `Z_R(Dh) ≤ Z_R(h)^2`, the exact
`2^r` iid normalized-sum law, strict variance positivity, and convergence of the iterated density
measures to their variance-matched Gaussian.
It also contains the explicit positive-definite Gaussian density ratio relative to product standard
Gaussian measure, its compact-box positive minimum and deterministic box lower bound, and the
eventual positive lower bound for all dyadic correlated product integrals. Repeated squaring against
that fixed lower bound proves `centered_product_of_posDef`, closing M2 without a singular-factor
continuity theorem. WP18 combines M1 and M2 to prove the unconditional
`lowerOrthant_ge_iid_of_posDef`. WP19 regularizes an arbitrary admissible covariance, proves the
exact coupled Gaussian weak limit and lower-orthant frontier nullity from its coordinate marginals,
and passes the inequality through Portmanteau. Thus `lowerOrthant_ge_iid` holds for every
admissible covariance and M3 is closed.
WP20 defines the finite coordinate maximum, identifies its lower-orthant sublevels, transfers M3
to strict upper-tail order against independent standard Gaussians, and proves the corresponding
nonnegative MGF comparison. The proof establishes exponential integrability from coordinate
marginals before converting its ENNReal layer-cake comparison to real Bochner integrals.
WP21 normalizes an arbitrary correlation matrix by an independent common Gaussian, proves the
exact prefactored-MGF identity, identifies the regular-simplex Gram matrix with identity covariance
after normalization, and transfers the WP20 comparison back to Gram matrices. Thus
`gramGaussianMax_mgf_le_regularSimplex` proves the required Gram-matrix MGF comparison.
WP22 constructs the codebook score map and proves that its standard-Gaussian pushforward has the
code Gram covariance. It defines the uniform-prior Bayes value as the integral of the pointwise
finite maximum of exact shifted-Gaussian likelihood ratios, proves its prefactored-MGF identity,
and certifies a measurable least-index ML decoder whose operational success equals that value.
The theorem `weak_simplex` compares this canonical tie-safe success probability with every supplied regular-simplex realization for `n + 1` unit signals in `Coord n`. WP24 proves that every measurable likelihood-maximizing decoder has the same Bayes value and exports `weak_simplex_of_scoreMaximizingDecoders` for arbitrary measurable score-maximizing tie-breaking rules on both codebooks. This closes the source's universal tie-breaking claim without a distinct-codeword or null-tie assumption and also covers zero signal strength.
WP23 has completed the local provenance, artifact-free source-snapshot, axiom, import-graph, and publication-documentation audits. Project-authored code is MIT-licensed, and a literal clean clone of the coherent release commit passed dependency resolution and every release gate. The repository is public, and hosted CI passed on the publication branch.

## Theorem dependency map

```text
rankOne_inverse_bound
  → exists_adaptivePotential_maximizer_with_value
  → exists_adaptiveWitnesses
exists_adaptiveWitnesses + Gaussian shift + centered tilted-half-line/event-shift identities
  → lowerOrthant_ge_iid_of_posDef_of_centeredProduct

prekopa_leindler + measurable_isLogConcave_lintegral_right
  → symmetricRectangle_ge_iid_of_posDef
  → even_logConcave_product_of_posDef
even_logConcave_product_of_posDef + Gaussian product-rotation invariance
  (private in Product/SumDifference.lean)
  → normalizedSelfConvolution_product_deficit_of_posDef
normalizedSelfConvolution_law
  → hasLaw_iteratedNormalizedSelfConvolution_dyadicSum
  → tendstoInDistribution_iteratedNormalizedSelfConvolution
tendstoInDistribution_iteratedNormalizedSelfConvolution
  + exists_pos_le_gaussianDensityRatio_on_box
  → exists_eventual_pos_lower_bound_integral_iteratedNormalizedSelfConvolution
the product-deficit theorem + the eventual positive lower bound
  → centered_product_of_posDef

lowerOrthant_ge_iid_of_posDef_of_centeredProduct + centered_product_of_posDef
  → lowerOrthant_ge_iid_of_posDef
  → lowerOrthant_ge_iid
  → coordinateMax_tail_le_iid
  → gaussianMax_mgf_le_regularSimplex

gramNormalization + gramMgf_normalization_identity + gaussianMax_mgf_le_regularSimplex
  → gramGaussianMax_mgf_le_regularSimplex
map_codeScore_stdGaussian + bayesValue_eq_gramMgf
  + gramGaussianMax_mgf_le_regularSimplex
  → bayesValue_le_regularSimplex
measurable maximizing decoder + finite tie partition
  → decoderSuccessOf_eq_bayesValue
bayesValue_le_regularSimplex + mlDecoder_success_eq_bayesValue
  → weak_simplex
bayesValue_le_regularSimplex + decoderSuccessOf_eq_bayesValue
  → weak_simplex_of_scoreMaximizingDecoders
```

## Reproduce

The repository pins Lean to `leanprover/lean4:v4.31.0` in `lean-toolchain` and pins mathlib to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in `lake-manifest.json` (direct input revision
`v4.31.0`). From a clean checkout, run:

```bash
lean --version
lake --version
lake update
lake build --wfail
lake env lean -DwarningAsError=true WeakSimplexConjectureLean/Audit/Axioms.lean
```

The trusted-source audit is:

```bash
python3 -m unittest discover -s scripts -p 'test_audit_trusted_lean.py'
python3 scripts/audit_trusted_lean.py --public-root WeakSimplexConjectureLean.lean WeakSimplexConjectureLean WeakSimplexConjectureLean.lean
```

The scanner conservatively checks forbidden spellings inside normal strings, raw strings, and
escaped identifiers; character literals are tokenized atomically, and only comment text recognized
by both structural views is ignored.

Current and completed package cards live in [`docs/work-packages/`](docs/work-packages/).

## License

Original project code is available under the [MIT License](LICENSE). Vendored StatLean sources and copied WP01 scratch artifacts retain their upstream Apache-2.0 licenses; see [PROVENANCE.md](PROVENANCE.md) and [the WP01 scratch ledger](Scratch/WP01/README.md) for exact sources, revisions, local changes, licenses, and audit boundaries.
