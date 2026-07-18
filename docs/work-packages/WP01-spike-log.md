# WP01 spike log

- **Card:** docs/work-packages/WP01.md
- **Integration owner:** /root
- **Execution handoff:** the frozen card names `/root/wp01_spikes`; `/root` reassigned execution to `/root/wp01_impl`, then assigned crash recovery and closeout to `/root/wp01_resume`, without changing scope
- **Baseline checked:** 2026-07-17; Lean 4.31.0, Lake 5.0.0, mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f
- **Owned files:** Scratch/WP01/** and this log only
- **Acceptance status:** complete; every scratch candidate and prototype compiles on Lean 4.31.0, every acceptance theorem reports only `propext`, `Classical.choice`, and `Quot.sound`, and the full trusted project build passes

## Source provenance

| Source | URL | Exact revision | Toolchain | License | Paths used |
|---|---|---|---|---|---|
| LeanPool | https://github.com/Vilin97/lean-pool | 9c296f447f48f3242df5e65e0b6120ddffcd79a7 | Lean 4.32.0-rc1 | Apache-2.0 | LeanPool/Isoperimetric/Basic.lean, LeanPool/Isoperimetric/PrekopaLeindler.lean |
| StatLean | https://github.com/StatLean/Stat-Lean | 31c61ed887bf3be0def314a3b3e5375d203b5ba1 | Lean 4.29.1 | Apache-2.0 | StatLean/AsymptoticStatistics/ForMathlib/PrekopaLeindler.lean, PiWithDensity.lean, GaussianMGF.lean, and lines 197–213 of Contiguity.lean |
| Original isoperimetric fallback | https://github.com/hojonathanho/isoperimetric | 29768f8beeaf17295cdf3853d37da35d7e2b0a5f | Lean 4.26.0-rc2 | Apache-2.0 | None; immutable revision resolved, but no source was used |

The repositories were fetched and checked out detached at the revisions above. Current branches were not used as evidence.

## A. Prékopa comparison

### Exact snapshots and modifications

The LeanPool exact sources are preserved as Scratch/WP01/LeanPool/Basic.lean and Scratch/WP01/LeanPool/PrekopaLeindler.lean.upstream. Their SHA-256 hashes exactly match the detached upstream files:

- Basic.lean: 9fa3bcb548b8697381ca787c1915a6268c0411dccfa94633356dad25840db563
- PrekopaLeindler.lean.upstream: 120efbe1c774b9d95bd04d59550d800f9ad93836a7c07abe4bff33fee7a971a4

Scratch/WP01/LeanPool/PrekopaLeindler.lean is a scratch-only standalone aggregation. It replaces the local LeanPool.Isoperimetric.Basic import by the exact 69-line contents of that file, retains the two original direct mathlib imports, and adds the top axiom print. This aggregation is necessary because Scratch/ is deliberately not a Lake library/import root; it does not alter any declaration or proof.

The exact StatLean source is preserved as Scratch/WP01/StatLean/PrekopaLeindler.lean.upstream, SHA-256 ecf65de6356e610aef1647fd473d91a0f489136e44a023b6214fd7682f582538. The compiling scratch port changes seven occurrences of the obsolete explicit application zero_le _ to Lean 4.31's zero_le, then adds the top axiom print. No statement or substantive proof step changed.

### Direct imports and local closure

LeanPool's upstream local closure is exactly two files and 843 source lines: Basic.lean (69) plus PrekopaLeindler.lean (774). Its direct mathlib imports are:

~~~text
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
~~~

StatLean's local closure is one 1036-line source file. Its direct mathlib imports are:

~~~text
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Integral.Layercake
Mathlib.Algebra.Group.Pointwise.Set.Scalar
Mathlib.Analysis.MeanInequalities
Mathlib.Analysis.InnerProductSpace.EuclideanDist
Mathlib.Analysis.SpecialFunctions.Pow.Real
~~~

All mathlib imports are transitively fixed by the pinned project manifest. The Lean source-dependency command confirmed precisely the direct source dependencies listed above and no non-mathlib dependency.

### Exact top interfaces

LeanPool exposes the scaled-x+y interface:

~~~lean
def PLConditions (n : ℕ) (θ : ℝ) (f g h : (Fin n → ℝ) → ENNReal) : Prop :=
  0 < θ ∧ θ < 1 ∧ Measurable f ∧ Measurable g ∧ Measurable h ∧
    ∀ x y, f x ^ (1 - θ) * g y ^ θ ≤ h (x + y)

theorem prekopa_leindler
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ENNReal}
    (hθfgh : PLConditions (d + 1) θ f g h) :
    ENNReal.ofReal
        ((1 - θ) ^ ((d + 1) * (1 - θ)) * θ ^ ((d + 1) * θ))⁻¹ *
      (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x
~~~

StatLean exposes the standard finite-Fintype weighted interface:

~~~lean
theorem AsymptoticStatistics.prekopaLeindler
    {ι : Type u} [Fintype ι] {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z
~~~

### Commands, costs, and audit

| Command | Result | Measured Bash time | Axioms |
|---|---|---:|---|
| `lake env lean Scratch/WP01/LeanPool/Basic.lean` | pass | 1.47 s | no top-theorem print |
| `lake env lean Scratch/WP01/LeanPool/PrekopaLeindler.lean` | pass | 4.16 s | `[propext, Classical.choice, Quot.sound]` |
| `lake env lean Scratch/WP01/StatLean/PrekopaLeindler.lean` | pass | 2.60 s | `[propext, Classical.choice, Quot.sound]` |

The source scan over all compiling Lean candidate files found no sorry, admit, declaration-level axiom, constant, unsafe, or sorryAx. The exact upstream snapshots give the same result.

### Selection

Select the StatLean lineage for the future audited Prékopa vendor port. This is a fact-based interface decision: it compiled within budget, is faster in this spike, supports an arbitrary finite Fintype, and states the standard affine weighted inequality without LeanPool's scaling prefactor or a Fin (d + 1) restriction. LeanPool remains a clean audited fallback and potentially a source of the smaller one-dimensional closure, but its theorem should not be the final public API without a separately frozen wrapper.

## B. Gaussian shift

### Search and closure decision

Pinned mathlib LSP search found no exact withDensity/map commutation theorem and no multivariate Gaussian exponential-shift identity. Semantic search returned only Radon–Nikodym results requiring measurable embeddings, which do not replace the general measurable-map helper used here. Consequently the selective StatLean chain is justified.

The rejected broad route is the 2070-line Contiguity.lean import. The selected local source closure is:

- exact PiWithDensity.lean, 157 upstream lines;
- exactly lines 197–213 of Contiguity.lean, the 17-line AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity declaration;
- exactly lines 396–618 of GaussianMGF.lean, the 1D, product, standard-Euclidean, and multivariate shift chain.

The exact snapshots are preserved as:

- Scratch/WP01/StatLean/PiWithDensity.lean.upstream, SHA-256 f0edc1044957f7e3f0885bbb4def3ed4f375657b423d216b11129228c92bc481;
- Scratch/WP01/StatLean/WithDensityMap.lean.upstream, SHA-256 bc766370ab497f3a31ec3f6bc9685f2b50e50c2d50c77bcf1a0385856700bc3f;
- Scratch/WP01/StatLean/GaussianMGF.lean.upstream, SHA-256 1c2594a34f112d90c79962a53d200ef031ae05d70e7742eeb2d737b2fbdbbf9e.

PiWithDensity.lean adds only an axiom-print command. WithDensityMap.lean adds the two minimal mathlib imports, opens the ENNReal notation scope, restores the enclosing namespace, and adds an axiom print. GaussianShift.lean is a standalone scratch aggregation because Scratch/ is not an import root: it inlines the exact PiWithDensity source and exact map helper, retains the exact four-theorem shift proof chain, replaces the two forbidden StatLean imports with ten direct mathlib imports, closes the namespace, and adds the top axiom print. No copied theorem statement or proof body changed.

The selected chain's direct mathlib imports are:

~~~text
Mathlib.Probability.Distributions.Gaussian.Multivariate
Mathlib.Probability.Moments.Basic
Mathlib.MeasureTheory.Integral.Pi
Mathlib.Analysis.InnerProductSpace.PiL2
Mathlib.Analysis.InnerProductSpace.EuclideanDist
Mathlib.Analysis.CStarAlgebra.Matrix
Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Measure.WithDensity
Mathlib.MeasureTheory.Integral.Lebesgue.Map
~~~

### Exact top interface

~~~lean
theorem ProbabilityTheory.multivariateGaussian_withDensity_exp_shift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (h : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S).withDensity
        (fun y ↦ ENNReal.ofReal
          (Real.exp (⟪h, y⟫_ℝ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2))) =
      multivariateGaussian (Matrix.toEuclideanCLM S h) S
~~~

The copied source elides the explicit real-inner parser annotation and writes toEuclideanCLM with an explicit scalar parameter; these elaborate to the intended card type without changing it.

### Commands, costs, and audit

| Command | Result | Measured Bash time | Axioms |
|---|---|---:|---|
| `lake env lean Scratch/WP01/StatLean/PiWithDensity.lean` | pass | 1.54 s | `[propext, Classical.choice, Quot.sound]` |
| `lake env lean Scratch/WP01/StatLean/WithDensityMap.lean` | pass | 1.33 s | `[propext, Classical.choice, Quot.sound]` |
| `lake env lean Scratch/WP01/StatLean/GaussianShift.lean` | pass | 3.55 s | `[propext, Classical.choice, Quot.sound]` |

The selected strategy is therefore a minimal selective port of 397 upstream source lines, not the 2070-line Contiguity module or the full 686-line GaussianMGF file. The two supporting declarations and the top theorem all received direct final axiom-print compilations.

## C. Positive quadratic coercivity

Status: complete and superseded for production by WP05. LSP and exact-checkout source search found `Matrix.PosDef.dotProduct_mulVec_pos`, `Matrix.inner_toEuclideanCLM`, `isCompact_sphere`, and `IsCompact.exists_isMinOn`, but no packaged theorem with the required uniform positive constant.

### Exact interface and proof

~~~lean
lemma Matrix.PosDef.exists_quadratic_lower_bound
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : WeakSimplex.Coord m,
        κ * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ
~~~

The 79-line prototype separates the zero-dimensional/subsingleton case and minimizes the quadratic form on the compact unit sphere in the nontrivial finite-dimensional case. Strict positivity at the minimizer comes from `Matrix.PosDef.dotProduct_mulVec_pos`; normalization and quadratic homogeneity extend the minimum to every vector. This is the report's requested compact-sphere argument with no spectral theorem, new axiom, or stronger dimension hypothesis.

Its direct imports are exactly:

~~~text
WeakSimplexConjectureLean.Core.Matrix
Mathlib.Analysis.InnerProductSpace.Rayleigh
~~~

`lake env lean --src-deps Scratch/WP01/QuadraticCoercivity.lean` reports the one project dependency `WeakSimplexConjectureLean/Core/Matrix.lean`, the one direct mathlib source above, and Lean `Init`; it reports no other Scratch or external dependency.

### Command, cost, and audit

| Command | Result | Measured Bash time | Axioms |
|---|---|---:|---|
| `lake env lean Scratch/WP01/QuadraticCoercivity.lean` | pass | 2.23 s | `[propext, Classical.choice, Quot.sound]` |

There is no remaining coercivity blocker. The later production implementation `WeakSimplex.posDef_quadratic_coercive` in WP05 owns this functionality; no production module should import the scratch theorem.

## D. Positive-definite Gaussian density ratio

Status: complete. The bounded spike did not require a new general Jacobian library: the pinned `Real.map_matrix_volume_pi_eq_smul_volume_pi` theorem and `PiLp.volume_preserving_toLp` supply the needed transport.

### Exact interfaces

The raw ratio theorem keeps the Jacobian and transformed standard density factored:

~~~lean
theorem WP01Density.multivariateGaussian_eq_stdGaussian_withDensity_raw
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (WP01Density.rawDensityRatio R) =
      multivariateGaussian 0 R
~~~

The acceptance-facing theorem has the explicit determinant/inverse formula requested by the card:

~~~lean
theorem WP01Density.multivariateGaussian_eq_stdGaussian_withDensity_explicit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun x ↦ ENNReal.ofReal ((Real.sqrt R.det)⁻¹ *
          Real.exp (-(x.ofLp ⬝ᵥ (R⁻¹ - 1).mulVec x.ofLp) / 2))) =
      multivariateGaussian 0 R
~~~

The theorem is a measure identity in the useful orientation for WP16: `N(0,R)` is obtained by applying the displayed density to product standard Gaussian measure. Positive definiteness supplies every determinant and inverse nonzero fact; no extra covariance assumption is present.

### Construction and local closure

`Scratch/WP01/DensityRatio.lean` is a 435-line standalone scratch aggregation. It carries the already-audited finite-product `withDensity` proof and map/withDensity helper from the StatLean spike, then adds project-local declarations for the standard Euclidean density, volume transport, CFC square-root Jacobian, determinant identity, inverse quadratic-form identity, raw ratio, and explicit ratio. It does not import another Scratch file because `Scratch/` is not a Lake import root.

The calculation proceeds as follows:

1. express product standard Gaussian measure as Euclidean volume with density `stdDensity`;
2. push volume through `Matrix.toEuclideanCLM (CFC.sqrt R)` using the pinned matrix Jacobian;
3. identify the pulled-back squared norm with `xᵀ R⁻¹ x` using self-adjointness and `CFC.sq_sqrt`;
4. cancel the nonzero finite standard density in `withDensity`;
5. rewrite the raw density as `(sqrt (det R))⁻¹ exp (-xᵀ(R⁻¹-I)x/2)`.

The separate 37-line `Scratch/WP01/EuclideanJacobian.lean` isolates and audits the transport brick:

~~~lean
lemma WP01Density.map_toEuclideanCLM_volume_eq_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.det ≠ 0) :
    Measure.map (Matrix.toEuclideanCLM (𝕜 := ℝ) M)
        (volume : Measure (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (|M.det|⁻¹) • volume
~~~

That declaration is intentionally repeated inside the standalone density file; the two Scratch files must not be imported together. Production adoption should keep one copy behind a project namespace.

The isolated Jacobian file directly imports `Mathlib.Analysis.CStarAlgebra.Matrix`, `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace`, and `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`; it has no local or external-repository import.

The final density file's direct imports are exactly:

~~~text
Mathlib.Analysis.CStarAlgebra.Matrix
Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Integral.Lebesgue.Map
Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
Mathlib.MeasureTheory.Measure.WithDensity
Mathlib.Probability.Distributions.Gaussian.Multivariate
~~~

`lake env lean --src-deps Scratch/WP01/DensityRatio.lean` reports precisely those eight direct mathlib sources and Lean `Init`, with no project, Scratch, or external import. During final closeout the provisional umbrella `import Mathlib` was replaced by this exact list; the theorem statements and proof bodies were unchanged. All density-specific declarations are project-local, so there is no upstream density theorem or proof modification to attribute.

### Commands, costs, and audit

| Command | Result | Measured Bash time | Axioms |
|---|---|---:|---|
| `lake env lean Scratch/WP01/EuclideanJacobian.lean` | pass | 1.89 s | `[propext, Classical.choice, Quot.sound]` |
| `lake env lean Scratch/WP01/DensityRatio.lean` immediately after crash recovery | pass | 26.36 s | both top theorems: `[propext, Classical.choice, Quot.sound]` |
| `lake env lean Scratch/WP01/DensityRatio.lean` after exact-import closeout, warm cache | pass | 3.88 s | both top theorems: `[propext, Classical.choice, Quot.sound]` |

The first row for the density file is the uncached recovery gate; the second is the final narrowed-import gate. Both emitted no errors or warnings. There is no remaining density-formula or Jacobian blocker.

## Selected strategies

- **Prékopa:** vendor the minimal StatLean lineage and expose a project wrapper around `AsymptoticStatistics.prekopaLeindler`; retain the clean LeanPool two-file port only as fallback evidence.
- **Gaussian shift:** vendor the 397-line selective StatLean closure consisting of `PiWithDensity.lean`, the 17-line map/withDensity helper, and the four-theorem shift chain; do not import full `Contiguity.lean` or all of `GaussianMGF.lean`.
- **Density ratio:** productionize the local CFC-square-root transport proved by `WP01Density.multivariateGaussian_eq_stdGaussian_withDensity_explicit`; no new Jacobian library is needed.
- **Quadratic coercivity:** use the production WP05 theorem, which supersedes the successful compact-sphere spike.

## Closing validation

Every compilable `.lean` file under `Scratch/WP01` was run individually from the repository root. The command matrix is the nine commands recorded in Sections A–D: LeanPool `Basic` and Prékopa, StatLean Prékopa, Pi-with-density, map/withDensity, Gaussian shift, quadratic coercivity, Euclidean Jacobian, and density ratio. All nine pass on the pinned toolchain; all eight files containing a `#print axioms` command report exactly `[propext, Classical.choice, Quot.sound]` for their audited top declaration(s).

The exact dependency checks were:

~~~text
lake env lean --src-deps Scratch/WP01/LeanPool/PrekopaLeindler.lean
lake env lean --src-deps Scratch/WP01/StatLean/PrekopaLeindler.lean
lake env lean --src-deps Scratch/WP01/StatLean/GaussianShift.lean
lake env lean --src-deps Scratch/WP01/QuadraticCoercivity.lean
lake env lean --src-deps Scratch/WP01/DensityRatio.lean
~~~

They confirm the local/external closure stated above: no candidate imports an external repository, no candidate imports another Scratch module, and only the coercivity spike imports a project module (`WeakSimplexConjectureLean.Core.Matrix`). Mathlib transitive dependencies are fixed by commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The final trust scans found no Lean `sorry`, tactic `admit`, declaration-level `axiom`, `constant`, `unsafe`, or `sorryAx` in any `.lean` or `.lean.upstream` source. A raw word scan finds two prose-comment occurrences of English “admit” at `StatLean/GaussianMGF.lean.upstream:411` and its exact copied line in `StatLean/GaussianShift.lean:209`; neither is Lean syntax, and both files compile without warnings. No production root imports `Scratch/WP01`.

`lake build` passes after all spike files and this log are finalized (`3075` jobs, `12.51 s` measured Bash real time), confirming the trusted project remains unaffected by the unimported Scratch closure.

## Remaining work and blockers

There is no remaining blocker to the WP01 acceptance deliverable. The following are explicit later integration actions, not spike blockers:

- production vendoring requires `PROVENANCE.md` entries, retained license headers, a dedicated vendor namespace, and integration-owner review;
- the selected Prékopa port still needs the frozen project wrapper and one downstream marginalization example in WP10;
- the selected Gaussian-shift chain still needs a production wrapper and expectation corollary in WP08;
- the density theorem still needs one nonduplicated production module and the compact-box positive-minimum consequence in WP16;
- Scratch files remain untrusted and must never be imported by a production root.
