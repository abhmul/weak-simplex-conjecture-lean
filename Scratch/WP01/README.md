# WP01 scratch artifacts

This directory preserves the exact external snapshots and standalone experiments used for WP01. It is not a Lake library root, no production module may import it, and successful compilation here does not make a declaration part of the trusted formalization. The authoritative experiment results and commands are in [`../../docs/work-packages/WP01-spike-log.md`](../../docs/work-packages/WP01-spike-log.md).

There are nine directly compilable `.lean` files and six inert `.lean.upstream` snapshots. `LeanPool/Basic.lean` is both a directly compilable input and a byte-exact upstream snapshot.

## Licensing and provenance

The repository-root MIT license applies only to project-authored material. It does not replace or supersede the licenses of copied upstream code.

- LeanPool-derived material remains under Apache-2.0. [`LeanPool/LICENSE`](LeanPool/LICENSE) and [`LeanPool/NOTICE`](LeanPool/NOTICE) are exact copies from LeanPool commit `9c296f447f48f3242df5e65e0b6120ddffcd79a7`.
- StatLean-derived material remains under Apache-2.0. [`StatLean/LICENSE`](StatLean/LICENSE) is an exact copy from StatLean commit `31c61ed887bf3be0def314a3b3e5375d203b5ba1`; that revision has no root `NOTICE` file.
- `QuadraticCoercivity.lean` and `EuclideanJacobian.lean` are project-authored prototypes under the repository-root MIT license.
- `DensityRatio.lean` is mixed: the inlined StatLean declarations remain Apache-2.0, while the project-authored `WP01Density` additions are MIT-licensed. No Apache-licensed portion is relicensed by this allocation.

The immediate LeanPool source is [`Vilin97/lean-pool`](https://github.com/Vilin97/lean-pool) at commit `9c296f447f48f3242df5e65e0b6120ddffcd79a7`. Its NOTICE attributes `LeanPool/Isoperimetric` to [`hojonathanho/isoperimetric`](https://github.com/hojonathanho/isoperimetric). The immediate StatLean source is [`StatLean/Stat-Lean`](https://github.com/StatLean/Stat-Lean) at commit `31c61ed887bf3be0def314a3b3e5375d203b5ba1`.

The exact upstream license hashes are:

| Upstream file | SHA-256 |
|---|---|
| LeanPool `LICENSE` | `c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c` |
| LeanPool `NOTICE` | `9a95fea683a51d72bd20a98e1dbe6daadbea3f0ad951ea04482328c78be06a19` |
| StatLean `LICENSE` | `d5945fe0f38866a919940212b0e3b5b0c30629b923c3e26dcce026571a29cd93` |

## Artifact inventory and modification notices

The following table and the corresponding top-of-file notices identify every adapted Apache-2.0 file in this directory and its local changes.

| Local path | Classification and source | Local changes | License |
|---|---|---|---|
| `LeanPool/Basic.lean` | Byte-exact `LeanPool/Isoperimetric/Basic.lean` snapshot | None; SHA-256 `9fa3bcb548b8697381ca787c1915a6268c0411dccfa94633356dad25840db563` | Apache-2.0 |
| `LeanPool/PrekopaLeindler.lean.upstream` | Byte-exact `LeanPool/Isoperimetric/PrekopaLeindler.lean` snapshot | None; SHA-256 `120efbe1c774b9d95bd04d59550d800f9ad93836a7c07abe4bff33fee7a971a4` | Apache-2.0 |
| `LeanPool/PrekopaLeindler.lean` | Standalone aggregation of the preceding two LeanPool files | Replaced the local LeanPool import by the exact declaration and documentation body from `Basic.lean` (lines 8–69), retained its direct Mathlib import, omitted the duplicate header, added a modification notice, and added `#print axioms prekopa_leindler`; declaration statements and proofs are unchanged | Apache-2.0 |
| `StatLean/PrekopaLeindler.lean.upstream` | Byte-exact `StatLean/AsymptoticStatistics/ForMathlib/PrekopaLeindler.lean` snapshot | None; SHA-256 `ecf65de6356e610aef1647fd473d91a0f489136e44a023b6214fd7682f582538` | Apache-2.0 |
| `StatLean/PrekopaLeindler.lean` | Standalone port of the preceding snapshot | Changed seven obsolete `zero_le _` applications to `zero_le` for Lean 4.31 and added the top-level axiom print; no statement or substantive proof step changed | Apache-2.0 |
| `StatLean/PiWithDensity.lean.upstream` | Byte-exact `StatLean/AsymptoticStatistics/ForMathlib/PiWithDensity.lean` snapshot | None; SHA-256 `f0edc1044957f7e3f0885bbb4def3ed4f375657b423d216b11129228c92bc481` | Apache-2.0 |
| `StatLean/PiWithDensity.lean` | Standalone port of the preceding snapshot | Added only `#print axioms MeasureTheory.pi_withDensity_prod` | Apache-2.0 |
| `StatLean/PiGaussian.lean.upstream` | Byte-exact `StatLean/AsymptoticStatistics/ForMathlib/PiGaussian.lean` snapshot | None; SHA-256 `693e6b99db8aa8b8914c3ed3f68190be4d272ca8ff6f74bbc1fc90a0f529f98b` | Apache-2.0 |
| `StatLean/WithDensityMap.lean.upstream` | Byte-exact lines 197–213 of `StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean` | None; SHA-256 `bc766370ab497f3a31ec3f6bc9685f2b50e50c2d50c77bcf1a0385856700bc3f` | Apache-2.0 |
| `StatLean/WithDensityMap.lean` | Standalone port of the preceding slice | Added two direct Mathlib imports, opened `ENNReal`, restored the enclosing namespace, and added the top-level axiom print; the declaration body and prose doc comment are unchanged | Apache-2.0 |
| `StatLean/GaussianMGF.lean.upstream` | Byte-exact `StatLean/AsymptoticStatistics/ForMathlib/GaussianMGF.lean` snapshot | None; SHA-256 `1c2594a34f112d90c79962a53d200ef031ae05d70e7742eeb2d737b2fbdbbf9e` | Apache-2.0 |
| `StatLean/GaussianShift.lean` | Standalone aggregation of `PiWithDensity.lean`, the `Contiguity.lean` slice, and lines 396–618 of `GaussianMGF.lean` | Replaced StatLean imports by ten direct Mathlib imports, inlined the two local providers, restored namespaces, and added the top-level axiom print; copied theorem statements and proof bodies are unchanged | Apache-2.0 |
| `QuadraticCoercivity.lean` | Project-authored standalone prototype | Original WP01 experiment; superseded by the production WP05 theorem | MIT |
| `EuclideanJacobian.lean` | Project-authored standalone prototype | Original WP01 experiment; its declaration is repeated inside `DensityRatio.lean` | MIT |
| `DensityRatio.lean` | Mixed standalone aggregation: all of StatLean `PiWithDensity.lean`, `pi_gaussianReal_eq_withDensity` from `PiGaussian.lean`, the unchanged `Measure.withDensity_map_eq_map_withDensity` declaration from the `Contiguity.lean` slice above, and project-authored density-ratio declarations | Replaced upstream imports with direct Mathlib imports, inlined provider declarations, omitted upstream prose comments around the two selected declarations, added `WP01Density` declarations, and added two top-level axiom prints | Apache-2.0 for copied StatLean portions; MIT for project-authored additions |

## Reproduction boundary

Run the nine direct compilation commands from the repository root as recorded in the WP01 spike log. The `.lean.upstream` files are immutable comparison material, not compilation targets. Production trust scans and builds intentionally exclude `Scratch/`; production adoption requires a separately reviewed vendor port, namespace isolation, provenance entry, and axiom audit.
