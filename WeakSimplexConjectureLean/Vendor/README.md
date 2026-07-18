# Vendored Lean source

This directory contains only minimal, attributed external Lean source closures. Every externally
sourced file is recorded in the repository-root `PROVENANCE.md`; every Lean source must compile on
Lean 4.31.0 and pass a transitive axiom audit before a production wrapper may import it.
These files retain their upstream Apache-2.0 license and are not relicensed by the repository's MIT
license.

WP10, WP08, and WP11 vendor five source files from StatLean commit
`31c61ed887bf3be0def314a3b3e5375d203b5ba1`:

- `StatLean/PrekopaLeindler.lean`, containing the selected finite-dimensional Prékopa--Leindler
  theorem behind the `WeakSimplex.Vendor.StatLean` namespace;
- `StatLean/PiWithDensity.lean`, the shared finite-product density provider used by WP08 and WP11;
- `StatLean/WithDensityMap.lean`, the selected map/with-density commuting lemma;
- `StatLean/GaussianMGFShift.lean`, the selected four-theorem Gaussian exponential-shift chain from
  upstream `GaussianMGF.lean`;
- `StatLean/PiGaussian.lean`, the exact finite-product Gaussian density and negation-invariance
  provider used by the symmetric-rectangle theorem;
- `StatLean/LICENSE`, an exact copy of the upstream Apache-2.0 license.

The three WP08 Lean sources contain exactly 397 selected upstream lines; WP11 adds the complete
62-line `PiGaussian.lean`. No other StatLean module or external repository is vendored.
