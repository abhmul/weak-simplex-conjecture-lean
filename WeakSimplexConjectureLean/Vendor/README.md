# Vendored Lean source

This directory contains the minimal external Lean source required by the production formalization. Every file is isolated under `WeakSimplex.Vendor`, builds on Lean 4.31.0, and is covered by the permanent transitive axiom audit.

The vendored declarations come from [StatLean](https://github.com/StatLean/Stat-Lean) commit `31c61ed887bf3be0def314a3b3e5375d203b5ba1`:

- `StatLean/PrekopaLeindler.lean` provides the finite-dimensional Prékopa–Leindler theorem used by the log-concavity argument.
- `StatLean/PiWithDensity.lean` provides the finite-product density identity.
- `StatLean/WithDensityMap.lean` provides the selected map/with-density commutation lemma.
- `StatLean/GaussianMGFShift.lean` provides the Gaussian exponential-shift chain.
- `StatLean/PiGaussian.lean` provides the finite-product Gaussian density and negation-invariance results.
- `StatLean/LICENSE` is an exact copy of StatLean's Apache-2.0 license.

No other StatLean module is included as a project dependency. [`PROVENANCE.md`](../../PROVENANCE.md) records the original path, exact revision and hashes, local adaptations, license, build command, import closure, and axiom result for every vendored artifact.
