# Lean Formalization Plan — v3 Reassessment
## Stochastic domination of Gaussian maxima and the weak simplex conjecture

- **Status:** implementation dossier for a Codex ultra formalization run
- **Date:** 2026-07-17
- **Lean baseline:** `leanprover/lean4:v4.31.0`
- **mathlib revision:** `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- **Primary mathematical source:** `simplex_optimality_proof.v3.md`
- **Associated paper:** Abhijeet Mulgund, [*Stochastic Domination of Gaussian Maxima: A Resolution of the Weak Simplex Conjecture*](https://arxiv.org/abs/2607.14087), arXiv:2607.14087
- **Supersedes for execution purposes:** an earlier internal formalization report

---

## Scoped extensions

This report governs the completed non-strict formalization. [`weak_simplex_lean_uniqueness_formalization_plan.v1.md`](weak_simplex_lean_uniqueness_formalization_plan.v1.md) governs the additive strictness and uniqueness work. It supersedes the singular-covariance restrictions here only for the explicitly named rigidity modules and preserves every existing public theorem statement.

## 0. Purpose and bottom-line recommendation

This report re-evaluates the earlier formalization plan against the v3 proof, the associated paper, the exact Lean 4.31.0/mathlib project state, the repository-local `.agents/skills/lean4` workflow, and available third-party Lean developments.

The earlier report was directionally sound: the covariance-space orthant theorem should be certified before the operational coding theorem; singular covariance should be handled at the outer boundary; the centered product theorem is the critical path; and measurable `argmax` machinery should be deferred. Those recommendations remain valid.

The v3 proof nevertheless changes the preferred implementation architecture in two important ways.

1. **The analytic main theorem should now be stated directly for an admissible correlation matrix `R`, not for a normalized codebook.** The v3 variational step is intrinsic to `R` and does not need a Gram realization. This removes all codebook geometry from the analytic core.

2. **The v3 endpoint potential should not be translated literally.** For Lean, reparameterize the v3 potential by the original scalar variables `s : Fin m → ℝ`. This removes the inverse map `H⁻¹`, the tilt map `τ`, the auxiliary function `𝓕 : (0,∞) → ℝ`, the open-domain boundary argument, strict concavity, and uniqueness. It leaves one smooth unconstrained maximization problem on a Euclidean space, with coordinatewise stationarity.

The recommended formalization-specific potential is

\[
\widetilde\Psi_c(s)
=
\sum_i \ell(s_i)
-
\frac12\bigl(H(s)-c\mathbf 1\bigr)^{\mathsf T}
R^{-1}
\bigl(H(s)-c\mathbf 1\bigr),
\]

where

\[
r(t)=\frac{\phi(t)}{\Phi(t)},\qquad
H(t)=t+r(t),\qquad
\ell(t)=\log\Phi(t)+\frac12r(t)^2.
\]

This is exactly the v3 objective after the coordinate substitution `b_i = H(s_i)`, but it avoids formalizing the global inverse of `H`. Its derivative is

\[
\partial_i\widetilde\Psi_c(s)
=
H'(s_i)
\left[
 r(s_i)-
 \bigl(R^{-1}(H(s)-c\mathbf1)\bigr)_i
\right].
\]

At a maximizer, `H'(s_i)>0`, so with `a_i=r(s_i)` one obtains

\[
H(s)-c\mathbf1=Ra,
\qquad
s+a-Ra=c\mathbf1.
\]

This is the compatibility relation required by the Gaussian change of measure.

### Executive decision

Proceed with the formalization, but replace the old adaptive-tilt work packages with the unconstrained `s`-space architecture described here. Use the copied skill at `.agents/skills/lean4` as a workflow layer, not as an autonomous specification generator. Keep its recorded snapshot fixed, add project-local instructions, require Lean LSP MCP, and disable autonomous statement rewriting and autonomous commits for the trusted development.

The critical path remains the positive-definite centered log-concave Gaussian product theorem. Existing Prékopa–Leindler and Gaussian-shift Lean code can probably reduce the workload, but no third-party theorem should be trusted until it builds on Lean 4.31.0 and passes a transitive axiom audit.

---

## 1. Reassessment of the previous report

### 1.1 Recommendations that remain correct

| Previous recommendation | Current decision | Reason |
|---|---|---|
| Certify the Gaussian lower-orthant comparison before the operational decoder theorem | **Retain** | It isolates the novel theorem and avoids decision-rule measurability during the analytic phase. |
| Handle singular covariance only at the final orthant theorem | **Retain and strengthen** | The v3 proof itself has a positive-definite orthant section followed by `Rε=(1-ε)R+εI`. The singular extension of the product theorem is unnecessary for the final proof. |
| Do not start with measurable `argmax` | **Retain** | Define a Bayes/ML value through an integral of the pointwise maximum, then package selectors last. |
| Keep covariance algebra separate from codebook geometry | **Retain and strengthen** | The analytic theorem can now be entirely matrix-based. |
| Prove only the Prékopa specialization actually needed | **Retain** | A general log-concave-measure library is not on the critical path. |
| Use explicit compact superlevel sets | **Retain, with a new objective** | The `s`-space objective has a simpler compact-superlevel proof on all of `ℝ^m`. |
| Treat uniqueness as optional | **Retain and strengthen** | Strict concavity is no longer needed at all for the formal proof. |
| Use explicit temporary theorem parameters rather than project axioms | **Retain** | This is essential for parallel development and final trust auditing. |

### 1.2 Recommendations that should be replaced

| Previous plan element | Replacement |
|---|---|
| Primary theorem tied to `normalizedCov x` | State the main analytic theorem directly for a correlation matrix `R` satisfying `R - J/m ⪰ 0`; derive the codebook theorem later. |
| Build an order isomorphism `H : ℝ ≃o (0,∞)` | Do not formalize `H⁻¹` or surjectivity. Only prove the scalar facts needed by `\widetilde\Psi`: derivatives, `H'>0`, and endpoint behavior of `ℓ`. |
| Define and differentiate `𝓕(H(s))` | Eliminate `𝓕` from the Lean development. Use `ℓ(s)` directly. |
| Formalize the paper's `(q,v)` variational problem | Do not use it in the trusted core. It remains a mathematical cross-check and fallback architecture. |
| Formalize the v3 `b`-space potential literally | Use the mathematically equivalent `s`-space potential. |
| Prove strict concavity and unique maximizer | Prove only existence of at least one global maximizer and coordinatewise derivative vanishing. |
| Extend the centered product theorem to singular `R` | Omit this theorem. Prove it only for positive-definite `R`; approximate singular covariance in the final orthant theorem. |
| Begin with a bundled `CorrelationMatrix` structure | Start with transparent predicates over raw matrices. Bundle only if repeated coercion/field projection becomes an actual problem. |

### 1.3 New conclusions from the associated paper

The associated paper identifies the centered product inequality as an exact specialization of the centered Gaussian forward–reverse Brascamp–Lieb theorem of Milman–Nakamura–Tsuji and supplies a direct proof in Appendix A. This has two consequences for the Lean project.

- It gives an independent mathematical specification against which the direct Lean product proof can be reviewed.
- It does **not** make formalizing the full forward–reverse theorem economical. No Lean implementation of that general theorem was found in the repository search conducted for this reassessment, and its abstraction level would be far larger than the one specialization required here.

The direct Appendix A route therefore remains the recommended trusted proof.

---

## 2. Certification target and milestone hierarchy

### 2.1 Primary theorem

The primary theorem should be the matrix-form lower-orthant inequality.

Informally:

> Let `m ≥ 1`. Let `R` be an `m × m` correlation matrix satisfying `R - J/m ⪰ 0`. Then, for every `c ∈ ℝ`,
> \[
> \mathbb P_{N(0,R)}\{x_i\le c\ \forall i\}\ge \Phi(c)^m.
> \]

Schematic Lean interface:

```lean
noncomputable section

abbrev Coord (m : ℕ) := EuclideanSpace ℝ (Fin m)

def allOnesMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun _ _ ↦ 1

def lowerOrthant {m : ℕ} (c : ℝ) : Set (Coord m) :=
  {x | ∀ i, x i ≤ c}

def IsCorrelation {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  R.PosSemidef ∧ ∀ i, R i i = 1

def IsWeakSimplexCov {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  IsCorrelation R ∧
    (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef

/-- Positive-definite analytic core. -/
theorem lowerOrthant_ge_iid_of_posDef
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hpd : R.PosDef)
    (c : ℝ) :
    (multivariateGaussian 0 R) (lowerOrthant c)
      ≥ (gaussianReal 0 1) (Set.Iic c) ^ m := by
  ...

/-- Final covariance theorem, including singular matrices. -/
theorem lowerOrthant_ge_iid
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian 0 R) (lowerOrthant c)
      ≥ (gaussianReal 0 1) (Set.Iic c) ^ m := by
  ...
```

The exact right-hand representation should be frozen after the first API spike. An ENNReal measure expression is preferable for the theorem boundary. A real-valued project CDF should be used for calculus, with one bridge theorem between the two.

### 2.2 Secondary theorem layers

1. **CDF/max form:** lower-orthant comparison and CDF order of coordinate maxima.
2. **MGF form:** positive exponential-moment comparison for the normalized maximum.
3. **Gram-matrix form:** exponential maximum comparison for every correlation matrix `G` against the regular-simplex Gram matrix.
4. **Codebook form:** equal-energy Gaussian classification value inequality.
5. **Operational form:** measurable ML decoder success, including ties.

### 2.3 Milestones

#### M0 — Reproducible foundation

- exact `lean-toolchain` checked in;
- project builds against the pinned manifest;
- Lean LSP MCP works from the repository;
- theorem interfaces compile;
- no production theorem is claimed.

#### M1 — Conditional positive-definite orthant theorem

Certified under an explicit parameter supplying the centered product theorem:

- scalar Gaussian calculus;
- rank-one inverse bound;
- `s`-space maximizer existence;
- stationarity and compatibility;
- tilted half-line mass/barycenter;
- multivariate Gaussian exponential shift;
- positive-definite orthant conclusion.

This is the best early mathematical milestone because it validates the adaptive mechanism without conflating it with the product theorem.

#### M2 — Certified positive-definite product theorem

- Prékopa wrapper;
- symmetric rectangle inequality;
- even-factor layer-cake inequality;
- normalized self-convolution;
- sum–difference deficit inequality;
- dyadic CLT iteration;
- positive lower bound;
- centered product theorem for `R.PosDef`.

#### M3 — Certified covariance theorem

- M1 and M2 integrated;
- outer singular approximation;
- lower-orthant theorem for every admissible correlation matrix;
- clean axiom audit.

#### M4 — Full weak simplex theorem

- common-Gaussian normalization;
- regular-simplex matrix identity;
- stochastic order to MGF;
- ML/Bayes integral identity;
- final equal-energy classification theorem.

#### M5 — Publication-quality repository

- public API documentation;
- provenance and license ledger;
- no placeholders;
- clean clone/build instructions;
- import graph and axiom report;
- independent review of the product and variational blocks.

---

## 3. Recommended formalization-specific proof architecture

### 3.1 Matrix-first analytic core

The associated paper's older `(q,v)` variational proof realizes

\[
G=\frac{m}{m-1}\left(R-\frac1mJ\right)
\]

as a Gram matrix and works with vectors `x_i`. The v3 proof eliminates this realization by using `R⁻¹`. The Lean development should follow v3 at this level: the orthant theorem should know only `R`.

Benefits:

- no rank-dependent ambient space;
- no choice of a Gram representation;
- no finite-dimensional basis construction;
- no translation between vector stationarity and matrix stationarity;
- the theorem exactly matches the strongest stochastic statement.

Codebook geometry is then a separate corollary module.

### 3.2 Eliminate `H⁻¹`, `τ`, and `𝓕`

Define scalar functions on `ℝ`:

\[
\phi(s)=\frac1{\sqrt{2\pi}}e^{-s^2/2},\quad
\Phi(s)=\int_{-\infty}^s\phi(u)\,du,
\]
\[
r(s)=\frac{\phi(s)}{\Phi(s)},\quad
H(s)=s+r(s),\quad
\ell(s)=\log\Phi(s)+\frac12r(s)^2.
\]

Required scalar identities:

\[
r'(s)=-r(s)H(s),
\]

\[
H'(s)=1-sr(s)-r(s)^2>0,
\]

\[
\ell'(s)=r(s)H'(s),
\]

\[
\ell(s)<0,
\qquad
\ell(s)\to0\quad(s\to+\infty),
\qquad
\ell(s)\to-\infty\quad(s\to-\infty).
\]

The formal proof does not need:

- `H(s)>0`;
- `H(s)→0` as `s→-∞`;
- surjectivity of `H`;
- an order isomorphism;
- an inverse derivative theorem;
- strict concavity of `𝓕`.

Those are valid mathematical facts, but they are not dependencies of the reparameterized proof.

### 3.3 The unconstrained potential

For `s : Coord m`, define coordinatewise vectors

\[
a_i=r(s_i),
\qquad
b_i=H(s_i),
\qquad
w=b-c\mathbf1.
\]

For `R.PosDef`, define

\[
\widetilde\Psi_c(s)
=
\sum_i\ell(s_i)
-
\frac12 w^{\mathsf T}R^{-1}w.
\]

Recommended Lean representation:

```lean
def r (s : ℝ) : ℝ := normalPDF s / normalCDF s

def H (s : ℝ) : ℝ := s + r s

def localLogMass (s : ℝ) : ℝ := Real.log (normalCDF s) + (r s)^2 / 2

def coordinateMap {m : ℕ} (f : ℝ → ℝ) (s : Coord m) : Coord m :=
  WithLp.toLp 2 fun i ↦ f (s i)

def displacement {m : ℕ} (c : ℝ) (s : Coord m) : Coord m :=
  coordinateMap H s - c • 1

def adaptivePotential {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (s : Coord m) : ℝ :=
  ∑ i, localLogMass (s i)
    - 1 / 2 * ⟪displacement c s,
        Matrix.toEuclideanCLM (R⁻¹) (displacement c s)⟫_ℝ
```

The code should introduce local wrappers for `EuclideanSpace`/function conversion. Do not scatter `.ofLp` and `WithLp.toLp 2` through every proof.

### 3.4 Compact-superlevel existence proof

Let

\[
L=m\log\Phi(c)-1<0.
\]

The symmetric trial point `s₀=c·1` has

\[
\widetilde\Psi_c(s_0)\ge m\log\Phi(c)>L
\]

by the rank-one inverse bound below. Consider

\[
K=\{s:\widetilde\Psi_c(s)\ge L\}.
\]

For every `s ∈ K`:

1. Every `ℓ(s_i)≤0`, and the quadratic penalty is nonpositive in the objective. Hence
   \[
   \widetilde\Psi_c(s)\le \ell(s_i),
   \]
   so `ℓ(s_i)≥L` for each `i`. Since `ℓ(t)→-∞` as `t→-∞`, all coordinates have a common lower bound.

2. Since `∑ℓ(s_i)≤0`,
   \[
   L\le\widetilde\Psi_c(s)
   \le -\frac12w^{\mathsf T}R^{-1}w,
   \]
   so
   \[
   w^{\mathsf T}R^{-1}w\le-2L.
   \]

3. Positive definiteness gives a coercivity constant `κ>0` with
   \[
   \kappa\|w\|^2\le w^{\mathsf T}R^{-1}w.
   \]
   Hence `w` is bounded.

4. Each `H(s_i)=w_i+c` is bounded above. Since `r(s_i)>0`, one has `s_i<H(s_i)`, so every coordinate has a common upper bound.

Thus `K` is closed and contained in a finite coordinate box, hence compact. Continuity gives a maximizer. No convexity or uniqueness theorem is needed.

A reusable matrix lemma should be proved once:

```lean
lemma Matrix.PosDef.exists_quadratic_lower_bound
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : Coord m,
        κ * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ := by
  ...
```

The expected proof is compactness of the unit sphere plus strict positivity. Before writing it, search for an existing coercivity theorem for positive-definite quadratic forms in the exact mathlib revision.

### 3.5 Coordinatewise stationarity

Do not introduce a full gradient or Hessian API. For each coordinate `i`, consider the one-dimensional line

\[
t\mapsto \widetilde\Psi_c(s_*+t e_i).
\]

A global maximizer gives a local maximum at `t=0`. Prove the derivative is

\[
H'(s_{*,i})
\left[
 r(s_{*,i})-
 \bigl(R^{-1}w\bigr)_i
\right].
\]

Since `H'(s_{*,i})>0`, obtain

\[
r(s_{*,i})=\bigl(R^{-1}w\bigr)_i.
\]

Set `a_i=r(s_{*,i})`. Extensionality gives `a=R⁻¹w`, hence `w=Ra`, and therefore

\[
s_*+a-Ra=c\mathbf1.
\]

This coordinate-line approach is usually easier to debug than a Fréchet-gradient proof and creates smaller theorem obligations.

### 3.6 Value identity

At the maximizer,

\[
\widetilde\Psi_c(s_*)
=
\sum_i\log\Phi(s_{*,i})
+
\frac12\|a\|^2
-
\frac12a^{\mathsf T}Ra
\]

because `w=Ra`. Thus

\[
\widetilde\Psi_c(s_*)
=
\sum_i\log\Phi(s_{*,i})
+
\frac12a^{\mathsf T}(I-R)a.
\]

Maximality and the symmetric trial point imply

\[
\sum_i\log\Phi(s_{*,i})
+
\frac12a^{\mathsf T}(I-R)a
\ge m\log\Phi(c).
\]

### 3.7 Rank-one inverse bound without matrix square roots

The v3 manuscript proves

\[
\mathbf1^{\mathsf T}R^{-1}\mathbf1\le m
\]

by conjugating with `R^{-1/2}`. That is not the recommended Lean proof.

Let

\[
x=R^{-1}\mathbf1,
\qquad
t=\mathbf1^{\mathsf T}R^{-1}\mathbf1.
\]

Evaluating `R-J/m ⪰ 0` at `x` gives

\[
x^{\mathsf T}Rx
\ge
\frac1m(\mathbf1^{\mathsf T}x)^2.
\]

Since `Rx=1`, the left side equals `t` and the right side equals `t²/m`. Positive definiteness of `R⁻¹` gives `t>0`; therefore `t≤m`.

This proof uses only matrix inverse, `mulVec`, dot products, and elementary ordered-field algebra. It should be substantially cheaper than formalizing a matrix square root/rank-one spectral argument.

### 3.8 Tilted half-lines and Gaussian shift

Define

\[
f_i(z)=e^{a_i z}\mathbf1_{z\le s_i+a_i}.
\]

Required facts:

- `a_i>0`;
- `f_i` is measurable, nonnegative, bounded, nonzero, and log-concave;
- \(\int f_i\,d\gamma=e^{a_i^2/2}\Phi(s_i)\);
- \(\int zf_i(z)\,d\gamma(z)=0\).

Apply the positive-definite centered product theorem and then the Gaussian exponential-tilt identity

\[
\int e^{\langle a,x\rangle-\frac12a^{\mathsf T}Ra}F(x)\,dN(0,R)(x)
=
\int F(x+Ra)\,dN(0,R)(x).
\]

With the compatibility relation, the event shift is exactly

\[
x+Ra\le s+a
\iff
x\le c\mathbf1.
\]

### 3.9 Singular covariance only at the outer theorem

For arbitrary admissible `R`, set

\[
R_\varepsilon=(1-\varepsilon)R+\varepsilon I,
\qquad 0<\varepsilon<1.
\]

Then:

- `Rε.PosDef`;
- its diagonal is one;
- \(R_\varepsilon-J/m\succeq0\);
- `multivariateGaussian 0 Rε` converges weakly to `multivariateGaussian 0 R`;
- the boundary of the equal-threshold lower orthant is contained in a finite union of coordinate hyperplanes;
- each coordinate marginal is `gaussianReal 0 1`, so the boundary is null;
- Portmanteau gives convergence of the orthant probabilities.

This avoids every continuity issue for arbitrary bounded log-concave factors and removes the manuscript's Section 6.4 from the Lean dependency graph.

---

## 4. Centered product theorem: detailed execution plan

The centered product theorem remains the largest and highest-risk block.

### 4.1 Target theorem

Only the positive-definite form is needed:

```lean
theorem centered_logConcave_product_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1)
    (f : Fin m → ℝ → ℝ)
    (hf_nonneg : ∀ i x, 0 ≤ f i x)
    (hf_bounded : ∀ i, Bornology.IsBounded (Set.range (f i)))
    (hf_logConcave : ∀ i, IsLogConcave (f i))
    (hf_mass_pos : ∀ i, 0 < ∫ x, f i x ∂gaussianReal 0 1)
    (hf_centered : ∀ i, ∫ x, x * f i x ∂gaussianReal 0 1 = 0) :
    ∫ x, ∏ i, f i (x i) ∂multivariateGaussian 0 R
      ≥ ∏ i, ∫ z, f i z ∂gaussianReal 0 1 := by
  ...
```

The final codomain conventions may use ENNReal internally. A real-valued wrapper is preferable at the public boundary because the orthant proof uses ordinary logarithms and exponentials.

### 4.2 Log-concavity interface

Do not build a large abstract theory. The project needs closure under:

- products;
- affine precomposition;
- indicators of convex sets/half-lines;
- Gaussian density;
- marginalization through one Prékopa theorem.

Recommended internal split:

- ENNReal-valued Prékopa statement and layer-cake lemmas;
- real-valued nonnegative wrapper for factors and calculus;
- explicit conversion lemmas under boundedness/integrability.

If the selected external Prékopa source uses a pointwise `f^t g^(1-t) ≤ h(...)` interface, wrap it rather than forcing its source code into a new `LogConcave` abstraction.

### 4.3 Symmetric Gaussian rectangle theorem

Prove first for `R.PosDef`.

For the induction step, avoid regular conditional distributions. Let `T=X_k` and define the regression residual

\[
Y_i=X_i-R_{ik}T,
\qquad i<k.
\]

Because `(Y,T)` is jointly Gaussian and has zero cross-covariance, mathlib's Gaussian independence theorem gives independence. Consequently the rectangle probability can be written by Fubini as an integral of

\[
q(t)=\mathbb P(Y+b t\in A)
\]

against the standard one-dimensional Gaussian law.

Prove:

- `q` is even, by symmetry of `A` and `Y`;
- `q` is log-concave, by the selected Prékopa theorem applied to the Gaussian density times the affine pullback of the rectangle indicator;
- an even log-concave function is nonincreasing on `[0,∞)`;
- apply the monotone covariance identity to `q(|T|)` and `1_{|T|≤r_k}`;
- invoke the induction hypothesis.

The formal statement should permit radii in `ℝ≥0∞` only if this materially simplifies unbounded endpoints. A cleaner first theorem uses finite `r_i≥0`; add `∞` by monotone convergence only if needed. The subsequent layer-cake theorem can handle unbounded superlevel intervals separately.

### 4.4 Even-factor layer cake

For bounded even log-concave `g_i`, each strict superlevel set is a centered interval, up to endpoint choices of Gaussian measure zero. Apply Tonelli/layer cake and the rectangle theorem pointwise in the level vector.

This step is a strong candidate for selective reuse from StatLean's `Anderson.lean`, which contains general layer-cake machinery. Do not import the entire Anderson development until its dependency closure is audited.

### 4.5 Normalized self-convolution

For a normalized density `h` relative to standard Gaussian measure, define

\[
(\mathcal Dh)(u)
=
\int
h\!\left(\frac{u+v}{\sqrt2}\right)
 h\!\left(\frac{u-v}{\sqrt2}\right)
\,d\gamma(v).
\]

Prove two interfaces.

#### Analytic interface

- measurable;
- bounded;
- log-concave by Prékopa;
- nonnegative;
- Gaussian integral one.

#### Probabilistic interface

If `ν = γ.withDensity h`, then `γ.withDensity (𝓓h)` is the law of `(Y+Y')/√2` for independent `Y,Y'∼ν`. Derive preservation of mean and variance from the law identity, not by recomputing integrals.

### 4.6 Sum–difference deficit inequality

Let `X,X'` be independent `N(0,R)` and set

\[
U=(X+X')/\sqrt2,
\qquad
V=(X-X')/\sqrt2.
\]

Prove a reusable theorem that `U` and `V` are independent and each has law `N(0,R)`. The preferred route is:

- independent Gaussian copies are jointly Gaussian;
- linear images remain jointly Gaussian;
- covariance of `U,V` is zero;
- use the mathlib zero-covariance Gaussian independence theorem.

Then condition by product-measure Fubini rather than a conditional-expectation API. For fixed `u`, the `v` factors are even and log-concave, so the even-factor theorem yields

\[
Z_R(h)^2\ge Z_R(\mathcal Dh).
\]

### 4.7 Dyadic CLT iteration

Normalize each original factor to a probability density `h_i dγ`, with mean zero. Show the `r`-fold transform is the law of

\[
2^{-r/2}\sum_{j=1}^{2^r}Y_j.
\]

Instantiate mathlib's one-dimensional CLT on a canonical i.i.d. sequence. Recommended construction:

- sample space `ℝ^ℕ`;
- product measure `Measure.pi (fun _ ↦ ν_i)`;
- coordinate maps;
- standard independence and identical-distribution lemmas;
- compose the full CLT with the subsequence `n=2^r`.

The factor laws have finite second moment because `h_i` is bounded relative to a Gaussian. Prove variance is nonzero by absolute continuity/non-atomicity. Mathlib's theorem `ae_eq_integral_of_variance_eq_zero` is a useful endpoint: variance zero would make the identity map almost surely constant, contradicting positive mass of two disjoint intervals.

### 4.8 Positive lower bound: density is the key dependency

For positive-definite `R`, the proof uses the density ratio

\[
L_R(x)
=(\det R)^{-1/2}
\exp\!\left[-\frac12x^{\mathsf T}(R^{-1}-I)x\right]
\]

of `N(0,R)` relative to the product standard Gaussian measure. This exact theorem is not exposed by the inspected mathlib multivariate Gaussian file.

The project should not postpone this issue. In the first week, choose one of these routes:

1. **Port an explicit multivariate Gaussian density theorem.** This is the preferred route. Isolate it behind a local theorem giving exactly the density ratio relative to `stdGaussian` or `Measure.pi`.
2. **Prove the density theorem locally from the positive-definite linear map representation.** This requires the Jacobian/change-of-variables formula and determinant/square-root algebra.

Once the ratio theorem exists, continuity and strict positivity give a positive minimum on `[-L,L]^m`, and the CLT gives a uniform positive lower bound on the coordinate box masses. This contradicts repeated squaring if the initial normalized product integral is below one.

This density theorem is one of the two highest-value external reuse targets, together with Prékopa.

### 4.9 Do not formalize the MNT specialization

The paper's identification with the centered forward–reverse Brascamp–Lieb theorem should be documented, but not used as the Lean proof unless a trusted Lean implementation of that theorem appears. Formalizing the general theorem would add determinant optimization, operator constraints, and a much larger measure-theoretic framework merely to recover one specialization whose direct proof is already available.

---

## 5. Scalar Gaussian calculus plan

### 5.1 Project-local CDF API

Define a stable real-valued CDF wrapper using the Gaussian density. Prove a single bridge to the measure-theoretic CDF.

Required API:

```lean
def normalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

def normalCDF (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, normalPDF t

lemma normalCDF_eq_measure_Iic (x : ℝ) :
  ENNReal.ofReal (normalCDF x) = (gaussianReal 0 1) (Set.Iic x)

lemma normalPDF_pos (x : ℝ) : 0 < normalPDF x
lemma normalCDF_pos (x : ℝ) : 0 < normalCDF x
lemma normalCDF_lt_one (x : ℝ) : normalCDF x < 1
lemma hasDerivAt_normalPDF (x : ℝ) : ...
lemma hasDerivAt_normalCDF (x : ℝ) : HasDerivAt normalCDF (normalPDF x) x
lemma tendsto_normalCDF_atTop : Tendsto normalCDF atTop (𝓝 1)
lemma tendsto_normalCDF_atBot : Tendsto normalCDF atBot (𝓝 0)
```

Do not mix generic `ProbabilityTheory.cdf`, interval integrals, and raw improper integrals throughout the proof. Normalize once.

### 5.2 Truncated moments

Prove by interval integration by parts:

\[
\int_{-\infty}^s x\phi(x)\,dx=-\phi(s),
\]

\[
\int_{-\infty}^s x^2\phi(x)\,dx=\Phi(s)-s\phi(s).
\]

These identities feed both `H'` and the tilted-factor barycenter calculation.

### 5.3 Strict positivity of `H'`

This is a small theorem with disproportionate downstream importance. Treat it as a dedicated spike.

Two viable proofs:

#### Route A — conditioned variance

Define the normalized restriction of standard Gaussian measure to `(-∞,s]`, compute its variance, and use the variance-zero theorem to contradict non-atomicity.

#### Route B — positive double integral

Use

\[
\Phi(s)^2 H'(s)
=
\frac12
\iint_{(-\infty,s]^2}(x-y)^2\,d\gamma(x)d\gamma(y).
\]

Show strict positivity by restricting to two disjoint subintervals below `s` on which `|x-y|` is uniformly positive.

Route B avoids normalizing a conditional measure; Route A reuses mathlib variance infrastructure. Prototype both in a scratch file and keep the shorter compiled proof.

### 5.4 Mills bounds and `ℓ` endpoints

Only the following tail estimate is required for the formal proof:

\[
\frac{t}{1+t^2}\phi(t)
\le\Phi(-t)
\le\frac{\phi(t)}t,
\qquad t>0.
\]

It yields

\[
r(-t)\le t+\frac1t
\]

and hence

\[
\ell(-t)
\le
1+\frac1{2t^2}-\log t-\frac12\log(2\pi)
\to-\infty.
\]

Do not formalize a larger inverse-Mills theory unless it directly reduces these obligations.

---

## 6. Exact mathlib inventory at the pinned revision

The project manifest pins mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, corresponding to the requested Lean 4.31.0 baseline.

### 6.1 High-value existing modules and declarations

| Need | Available infrastructure |
|---|---|
| Multivariate Gaussian measure | `Mathlib.Probability.Distributions.Gaussian.Multivariate` defines `stdGaussian`, `multivariateGaussian`, covariance, characteristic functions, coordinate marginals, and restriction to coordinate subsets. |
| Standard real Gaussian | `Mathlib.Probability.Distributions.Gaussian.Real` defines `gaussianReal`, `gaussianPDFReal`, density and moment-generating facts. |
| Gaussian independence | `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence` proves independent Gaussians are jointly Gaussian and jointly Gaussian zero-covariance families are independent. |
| One-dimensional CLT | `Mathlib.Probability.CentralLimitTheorem` provides `tendstoInDistribution_inv_sqrt_mul_sum` and the centered/variance form `tendstoInDistribution_inv_sqrt_mul_sum_sub`. |
| Weak convergence on continuity sets | `Mathlib.MeasureTheory.Measure.Portmanteau` provides probability convergence under null-frontier hypotheses. |
| Matrix positive definiteness | `Mathlib.LinearAlgebra.Matrix.PosDef` supplies quadratic positivity, invertibility, and `Matrix.PosDef.inv`. |
| Variance-zero characterization | `Mathlib.Probability.Moments.Variance` includes `ae_eq_integral_of_variance_eq_zero`. |
| CDF framework | `Mathlib.Probability.CDF` supplies generic CDF monotonicity and endpoint infrastructure. |
| Gram matrices | `Mathlib.Analysis.InnerProductSpace.GramMatrix`. |
| Improper/interval integration | `IntegralEqImproper`, interval integration by parts, dominated convergence. |

Particularly useful exact facts in the pinned multivariate Gaussian file include:

- `multivariateGaussian_zero_one`;
- `covariance_eval_multivariateGaussian`;
- `variance_eval_multivariateGaussian`;
- `measurePreserving_eval_multivariateGaussian`;
- `charFun_multivariateGaussian`;
- `measurePreserving_restrict₂_multivariateGaussian`.

### 6.2 Gaps not found in the inspected revision

Repository/declaration search did not reveal a packaged theorem with an obvious interface for:

- general log-concave functions;
- Prékopa or Prékopa–Leindler;
- Šidák's symmetric rectangle inequality;
- the centered product theorem;
- the inverse-Mills calculus used here;
- the explicit positive-definite multivariate Gaussian density relative to product standard Gaussian measure;
- the exact multivariate Gaussian exponential-tilt/mean-shift identity;
- a high-level first-order stochastic-order API needed by the final proof.

This is an inventory conclusion, not a proof that no equivalent declaration exists under an unexpected name. Every work package should begin with LSP search, LeanSearch, Loogle, and source grep on the exact checkout.

### 6.3 What should be proved locally even if general APIs exist

Some small project wrappers are worth owning locally:

- `normalCDF` and its bridge;
- equal-threshold lower orthant;
- all-ones vector/matrix;
- admissible covariance predicate;
- coordinatewise scalar map on Euclidean space;
- matrix quadratic form wrapper;
- coordinate maximum and its orthant equivalence;
- normalized codebook covariance.

These wrappers stabilize downstream code against library naming and coercion changes.

---

## 7. Third-party Lean reuse assessment

All external findings below are source-level audits. No candidate was compiled inside this reassessment environment. The adoption gate in Section 7.5 is mandatory.

### 7.1 `hojonathanho/isoperimetric`

- **Inspected commit:** `29768f8beeaf17295cdf3853d37da35d7e2b0a5f`
- **Toolchain:** Lean `v4.26.0-rc2`
- **License:** Apache 2.0

Relevant file:

- `Isoperimetric/PrekopaLeindler.lean`

The file contains a substantial one-dimensional Brunn–Minkowski/layer-cake proof and an arbitrary-dimensional Prékopa–Leindler theorem. Repository search did not find `sorry` or a custom `axiom` in the relevant source. Its theorem normalization is not exactly the one used in the manuscript, so a local wrapper is required.

**Assessment:** mathematically valuable and apparently complete, but the version gap from 4.26-rc2 to 4.31.0 is nontrivial.

### 7.2 `Vilin97/lean-pool` port of the isoperimetric development

- **Inspected commit:** `9c296f447f48f3242df5e65e0b6120ddffcd79a7`
- **Toolchain:** Lean `v4.32.0-rc1`

Relevant file:

- `LeanPool/Isoperimetric/PrekopaLeindler.lean`

This is a more recent port of the same development, with attribution. Its toolchain is much closer to 4.31.0, and repository search did not find `sorry` in the file.

**Assessment:** first-choice source for a Prékopa port spike. Do not depend on the entire LeanPool repository. Vendor only the minimal isoperimetric files and transitive local helpers after a clean 4.31.0 build.

### 7.3 StatLean

- **Inspected commit:** `31c61ed887bf3be0def314a3b3e5375d203b5ba1`
- **Toolchain:** Lean `v4.29.1`
- **License:** Apache 2.0

High-value files:

- `StatLean/AsymptoticStatistics/ForMathlib/PrekopaLeindler.lean`
- `StatLean/AsymptoticStatistics/ForMathlib/Anderson.lean`
- `StatLean/AsymptoticStatistics/ForMathlib/GaussianMGF.lean`
- `StatLean/AsymptoticStatistics/ForMathlib/PiGaussian.lean`
- selected `PiWithDensity` helpers

The current Prékopa file contains substantial completed proof code even though some comments refer to an earlier keystone gap. The comment/code mismatch is a reason for an axiom/build audit, not a reason to reject the source.

`GaussianMGF.lean` contains especially relevant results:

- `integral_exp_inner_stdGaussian`;
- `integral_exp_inner_multivariateGaussian`;
- `gaussianReal_withDensity_exp_shift`;
- `stdGaussian_withDensity_exp_shift`;
- `multivariateGaussian_withDensity_exp_shift`.

The last theorem states exactly the measure-level Esscher/Girsanov identity needed for the orthant proof, including positive-semidefinite covariance.

`PiGaussian.lean` provides the product standard Gaussian as a `withDensity` measure relative to product Lebesgue measure, useful for density calculations.

**Assessment:** best source for Gaussian shift and density-supporting helpers; plausible alternative source for Prékopa and layer cake. The repository is broad, so selective vendoring is strongly preferred over a whole-repository Lake dependency.

### 7.4 Sources not recommended as trusted dependencies

- `Brunn-Minkowski-in-Lean/BrunnMinkowski` contains explicit `sorry` in the relevant Prékopa files. It may supply proof ideas but not trusted code.
- The general Milman–Nakamura–Tsuji theorem has no located Lean implementation. Use it as a mathematical cross-check only.

### 7.5 External-code adoption gate

For each candidate theorem:

1. Pin an exact source commit.
2. Copy the minimal candidate files into an isolated port branch.
3. Make them compile under Lean 4.31.0 and the project's exact mathlib manifest.
4. Run source scans for `sorry`, `admit`, `axiom`, `unsafe`, and unexpected `classical`-choice dependencies where relevant.
5. Run `#print axioms` on the top theorem and every local wrapper.
6. Inspect all transitive non-mathlib imports.
7. Record license, source URL, commit, copied paths, and local modifications in `PROVENANCE.md`.
8. Benchmark downstream elaboration time.
9. Expose the theorem through a small project-local wrapper module.
10. Do not update the external source during the proof unless a controlled migration issue is opened.

### 7.6 Recommended reuse decision

Run two parallel port spikes:

- **PL spike A:** LeanPool isoperimetric port, 4.32-rc1 → 4.31.0.
- **PL/shift spike B:** StatLean Prékopa/Anderson and GaussianMGF, 4.29.1 → 4.31.0.

Expected decision:

- use the LeanPool lineage for the narrow Prékopa theorem if it ports cleanly;
- use selected StatLean Gaussian-shift/density helpers;
- use StatLean layer-cake code only where it is demonstrably smaller than a local proof;
- vendor, do not add a broad production dependency.

---

## 8. Assessment of the repository-local `lean4` skill

### 8.1 Inspected version

- **Project copy:** `.agents/skills/lean4`
- **Imported from local checkout:** `~/dev/lean4-skills/plugins/lean4/skills/lean4`
- **Snapshot commit:** `769fb59f9abdacdf990af1a874290eb8c7994191`
- **License:** MIT; copied as `.agents/skills/lean4/LICENSE`

The project copy is the operative workflow for agents. The local source checkout is provenance and an
update source only; formalization work must read the copied skill.

### 8.2 What should be used essentially as written

The generic Lean skill has sound defaults for local proof engineering:

- search before proving;
- compile incrementally;
- preserve theorem statements and docstrings;
- 100-character mathlib line width;
- LSP-first goal inspection and search;
- explicit review, refactor, and checkpoint phases;
- separate guided and unattended proof loops;
- axiom and `sorry` checks.

Recommended workflows:

- `learn --mode=repo` for orientation;
- `learn --mode=mathlib` for declaration search;
- `prove` for difficult load-bearing theorems;
- `autoprove` only for narrow frozen statements;
- `review` after each work package;
- `refactor` after the theorem is complete;
- `checkpoint` at integration boundaries;
- `doctor` for environment/toolchain failures.

In Codex, invoke the copied skill as `$lean4` and request the relevant workflow. The Claude discovery
symlink exposes the same core skill as `/lean4`. The upstream plugin's `/lean4:*` command surface,
hooks, helper runtime, and subagents are not installed in this repository.

### 8.3 What should not be used out of the box

The default `autoformalize` settings are inappropriate for a theorem of this size and sensitivity. At the inspected commit its defaults include:

- `--rigor=sketch`;
- `--statement-policy=rewrite-generated-only`;
- twenty cycles per claim;
- a two-hour session budget;
- `--commit=auto`.

Those defaults are reasonable for exploratory synthesis but unsafe as the outer driver of this project. The mathematical interfaces must be frozen by the plan/integration lead, and the agent must not silently rewrite statements to make them easier.

Use `autoformalize` only for isolated leaf claims and only with explicit restrictive flags, for example:

```text
$lean4 autoformalize \
  --source=docs/claims/truncated_moment_1.md \
  --claim-select=named:"first truncated Gaussian moment" \
  --out=WeakSimplexConjectureLean/Normal/TruncatedMoments.lean \
  --rigor=checked \
  --statement-policy=preserve \
  --draft-elab-check=strict \
  --max-cycles=6 \
  --max-stuck-cycles=2 \
  --max-total-runtime=30m \
  --deep=stuck \
  --commit=never
```

Do not point `autoformalize` at the full paper or full proof file.

### 8.4 Required project-local modifications

Use `.agents/skills/lean4/SKILL.md` together with:

1. repository-local Claude discovery symlinks under `.claude/skills/` for both copied skills;
2. a repository-root `AGENTS.md` containing the theorem architecture, trust policy, build commands, statement-freeze rules, and module ownership;
3. a repository skill `.agents/skills/weak-simplex-formalization/SKILL.md` containing the work-package protocol and mathematical invariants;
4. optional nested `AGENTS.md` files in `Product/` and `Tilt/` for branch-specific rules;
5. an explicit MCP configuration for Lean LSP;
6. no autonomous commits from subagents;
7. a single integration owner for public declarations.

Codex reads `AGENTS.md` from the repository root down to the working directory, with nearer files overriding broader instructions. Keep the combined instruction chain below the default size cap or deliberately increase it. Put long mathematical references in the project skill's `references/` directory rather than in `AGENTS.md`.

The project-specific skill should set `allow_implicit_invocation: false`. Invoke it explicitly for planned formalization tasks, while the generic Lean skill may remain implicitly discoverable.

### 8.5 LSP MCP should be mandatory

The generic skill itself states that scripts-only operation lacks live goals, tactic testing, and real-time diagnostics and is substantially slower. This project should treat Lean LSP MCP as required, not optional.

The operative Codex configuration is `.codex/config.toml`. The checkout must be trusted in the
user-level Codex configuration before that file is loaded. It pins `lean-lsp-mcp` to `0.28.1` and
uses absolute paths because Codex does not shell-expand `~` in an MCP server's `cwd`.

Recommended MCP policy:

- `required = true`;
- explicit `enabled_tools` allowlist;
- `tool_timeout_sec` increased for semantic search and large-file diagnostics;
- read-oriented tools enabled by default;
- write-capable tools approved explicitly.

Core tools:

```text
lean_goal
lean_hover_info
lean_local_search
lean_leanfinder
lean_leansearch
lean_loogle
lean_hammer_premise
lean_state_search
lean_multi_attempt
lean_diagnostic_messages
lean_code_actions
```

### 8.6 Recommended operating mode for Codex ultra

- Use the project plan as the source of truth for theorem statements.
- Work one work package at a time.
- Search the exact mathlib checkout before adding helpers.
- Create scratch files for API experiments; delete or move them under `Scratch/` before integration.
- Never weaken a theorem or add assumptions without an issue-level decision.
- Never add a project axiom.
- Treat a compiling theorem with a non-clean axiom report as incomplete.
- Keep external ports isolated until audited.
- Report blocked interfaces with exact goals, attempted declarations, and minimal reproductions.

---

## 9. Project configuration reassessment

### 9.1 Current state

The supplied `lakefile.toml` requires mathlib `v4.31.0` and enables:

- `pp.unicode.fun = true`;
- `relaxedAutoImplicit = false`;
- `weak.linter.mathlibStandardSet = true`;
- `maxSynthPendingDepth = 3`.

The manifest pins mathlib to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, but records `fixedToolchain = false`. No `lean-toolchain` file was supplied.

### 9.2 Required changes before formalization

1. Add a checked-in `lean-toolchain`:

   ```text
   leanprover/lean4:v4.31.0
   ```

2. Add `autoImplicit = false` to project Lean options. `relaxedAutoImplicit = false` is not a substitute for disabling automatic implicit variables.

3. Remove the global `maxSynthPendingDepth = 3`. It is likely to create artificial instance-synthesis failures in measure theory, finite-dimensional analysis, and matrix code. Reintroduce a local override only if a measured elaboration problem justifies it.

4. Keep `weak.linter.mathlibStandardSet = true` and the Unicode lambda setting.

5. Keep the exact manifest under version control. Run `lake update` only in a dedicated dependency-update change.

6. Do not add StatLean, LeanPool, or the isoperimetric repository as a whole-project `require` during the initial development. Port audited minimal files into a `Vendor/` namespace.

7. Use narrow imports in production files. `import Mathlib` is acceptable in scratch spikes only.

8. Do not set unlimited global heartbeats. Use local `set_option maxHeartbeats` around a proved bottleneck after profiling.

Suggested initial `lakefile.toml` options:

```toml
[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
pp.unicode.fun = true
weak.linter.mathlibStandardSet = true
```

### 9.3 CI jobs

Required CI:

1. `lake build` from a clean checkout and pinned toolchain.
2. Build each public root module separately to catch accidental import leakage.
3. Scan trusted source for `sorry`, `admit`, and project `axiom` declarations.
4. Run mathlib linters on public declarations.
5. Generate an import graph and reject forbidden imports from `Scratch/` or `Scaffold/`.
6. Compile `Audit/Axioms.lean`, containing `#print axioms` for every exported milestone theorem.
7. Verify `PROVENANCE.md` matches all files under `Vendor/`.
8. Optional nightly job with higher heartbeats and a current mathlib compatibility branch; this must not replace the pinned release job.

---

## 10. Recommended repository layout

```text
WeakSimplexConjectureLean/
  Core/
    Finite.lean
    Euclidean.lean
    Matrix.lean
    Correlation.lean
    QuadraticCoercivity.lean

  Normal/
    PDFCDF.lean
    TruncatedMoments.lean
    Mills.lean
    TiltFunctions.lean        # r, H, ℓ and their calculus

  Gaussian/
    Multivariate.lean
    CoordinateMarginals.lean
    SumDifference.lean
    Shift.lean
    WeakLimit.lean
    DensityRatio.lean

  LogConcavity/
    Basic.lean
    Prekopa.lean
    Indicators.lean

  Product/
    SymmetricRectangle.lean
    EvenFactors.lean
    SelfConvolution.lean
    DyadicLaw.lean
    CLT.lean
    PositiveLowerBound.lean
    Centered.lean

  Tilt/
    RankOneInverse.lean
    Potential.lean
    Compactness.lean
    Stationarity.lean
    Witnesses.lean

  Orthant/
    PositiveDefinite.lean
    Singular.lean
    Main.lean

  Maxima/
    CoordinateMax.lean
    StochasticOrder.lean
    ExponentialMoments.lean

  Coding/
    Gram.lean
    Normalization.lean
    RegularSimplex.lean
    BayesValue.lean
    MLDecoder.lean
    WeakSimplex.lean

  Vendor/
    Prekopa/
    GaussianShift/
    README.md

  Scaffold/
    ProductAssumption.lean    # never imported by final Main

  Scratch/
    ...                       # excluded from trusted roots

  Audit/
    Axioms.lean
    Imports.lean

  Main.lean
```

### Namespace policy

Use `WeakSimplex` for project theorems. Imported code should remain in an attributed vendor namespace unless a theorem is wrapped. Do not modify third-party names and project names in the same file.

---

## 11. Interface theorem catalog

The integration lead should freeze these interfaces before parallel proof work.

### 11.1 Matrix and covariance

```lean
lemma normalizedCov_isWeakSimplexCov ...
lemma regularSimplex_normalizedCov_eq_one ...
lemma weakSimplexCov_perturb_posDef ...
lemma rankOne_inverse_bound ...
lemma posDef_quadratic_coercive ...
```

### 11.2 Normal calculus

```lean
lemma normalCDF_pos ...
lemma normalCDF_lt_one ...
lemma hasDerivAt_normalCDF ...
lemma truncated_first_moment ...
lemma truncated_second_moment ...
lemma hasDerivAt_r ...
lemma hasDerivAt_H ...
lemma H_deriv_pos ...
lemma hasDerivAt_localLogMass ...
lemma localLogMass_neg ...
lemma localLogMass_tendsto_atTop ...
lemma localLogMass_tendsto_atBot ...
```

### 11.3 Variational witnesses

Package only outputs used by the orthant theorem:

```lean
structure AdaptiveWitnesses {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) where
  s : Coord m
  a : Coord m
  a_eq_r : ∀ i, a i = r (s i)
  a_pos : ∀ i, 0 < a i
  compatibility : s + a - Matrix.toEuclideanCLM R a = c • 1
  value_bound :
    (∑ i, Real.log (normalCDF (s i)))
      + (⟪a, a⟫_ℝ - ⟪a, Matrix.toEuclideanCLM R a⟫_ℝ) / 2
      ≥ m * Real.log (normalCDF c)
```

Top theorem:

```lean
theorem exists_adaptiveWitnesses
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hpd : R.PosDef)
    (hdom : (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef)
    (c : ℝ) :
    Nonempty (AdaptiveWitnesses R c)
```

### 11.4 Product theorem

```lean
theorem centered_product_of_posDef ...
```

No singular version is required.

### 11.5 Gaussian shift

Prefer a measure identity and derive the expectation identity:

```lean
theorem multivariateGaussian_withDensity_exp_shift ...

theorem integral_exp_inner_sub_quadratic_mul
    ... :
    ∫⁻ x, ENNReal.ofReal
      (Real.exp (⟪a, x⟫ - quadratic R a / 2) * F x)
      ∂multivariateGaussian 0 R
    = ∫⁻ x, ENNReal.ofReal (F (x + Rmul a))
      ∂multivariateGaussian 0 R
```

### 11.6 Main analytic theorem

```lean
theorem lowerOrthant_ge_iid_of_posDef ...
theorem lowerOrthant_ge_iid ...
```

### 11.7 Coding theorem

```lean
theorem gaussianMax_mgf_le_regularSimplex ...
theorem bayesSuccess_le_regularSimplex ...
theorem weak_simplex ...
```

---

## 12. Revised work packages

### WP00 — Baseline, CI, and agent configuration

**Deliverables**

- `lean-toolchain` pinned to v4.31.0;
- corrected Lake options;
- Lean LSP MCP verified;
- root `AGENTS.md` and project skill installed;
- clean CI and axiom-audit skeleton.

**Gate:** no mathematical work begins on an unpinned or scripts-only environment.

### WP01 — Exact API and external-port spikes

Parallel spikes:

- Prékopa from LeanPool lineage;
- Prékopa/Anderson from StatLean;
- StatLean Gaussian shift;
- positive-definite Gaussian density ratio;
- positive quadratic coercivity.

**Gate:** select the port strategy and publish exact theorem names/imports.

### WP02 — Core finite/matrix wrappers

- all-ones vector/matrix;
- Euclidean/function conversion;
- quadratic form wrappers;
- correlation/admissibility predicates;
- lower orthant measurability;
- finite product/sum helpers.

### WP03 — Normal PDF/CDF and truncated moments

- project-local CDF;
- measure bridge;
- derivative and tails;
- first and second truncated moments.

### WP04 — `r`, `H`, and `ℓ`

- derivative identities;
- strict positivity `H'`;
- Mills bounds;
- `ℓ<0` and endpoint limits.

**Stop/go criterion:** do not start the variational proof until `H_deriv_pos` and `localLogMass_tendsto_atBot` compile.

### WP05 — Matrix inverse lemmas

- `R.PosDef → R⁻¹.PosDef` wrappers;
- quadratic coercivity;
- rank-one inverse bound;
- symmetric/self-adjoint simplification lemmas.

### WP06 — Potential and compact maximizer

- define `\widetilde\Psi`;
- continuity;
- trial-point lower bound;
- compact superlevel set;
- existence of a global maximizer.

### WP07 — Coordinate stationarity and witnesses

- line restriction along basis directions;
- derivative computation;
- compatibility `s+a-Ra=c1`;
- value identity;
- `AdaptiveWitnesses` theorem.

### WP08 — Tilted half-lines and Gaussian shift

- factor regularity/log-concavity;
- mass and barycenter identities;
- port/prove Gaussian shift;
- event-shift algebra.

### WP09 — Conditional PD orthant theorem

Prove `lowerOrthant_ge_iid_of_posDef` under an explicit centered-product theorem parameter. This is M1.

### WP10 — Prékopa wrapper and log-concavity basics

- selected vendored theorem;
- affine/product/indicator/Gaussian closure;
- exact marginalization wrapper used in rectangle and self-convolution.

### WP11 — Symmetric rectangles

- regression decomposition;
- Gaussian independence;
- even/log-concave shift probability;
- monotone covariance induction.

### WP12 — Even-factor layer cake

- strict superlevel interval classification;
- endpoint-null lemmas;
- Tonelli/layer-cake product inequality.

### WP13 — Normalized self-convolution

- transform definition;
- boundedness/log-concavity;
- law identity;
- mass/mean/variance preservation.

### WP14 — Sum–difference theorem

- Gaussian law/independence of `U,V`;
- fixed-`u` even factors;
- deficit inequality.

### WP15 — Dyadic law and CLT

- canonical i.i.d. construction;
- iterated transform law;
- nonzero variance;
- dyadic subsequence convergence.

### WP16 — Positive lower bound

- density ratio theorem;
- compact-box positive minimum;
- coordinate box probability limits;
- uniform lower bound.

### WP17 — Centered product theorem

- repeated-squaring inequality;
- contradiction;
- denormalization;
- axiom audit.

This is M2.

### WP18 — Unconditional PD orthant theorem

Integrate WP09 and WP17. No scaffold imports remain.

### WP19 — Singular outer approximation

- admissibility of `Rε`;
- Gaussian weak convergence;
- lower-orthant frontier/null boundary;
- Portmanteau limit.

This completes M3.

### WP20 — Maximum and exponential moments

- orthant/max equivalence;
- CDF/tail direction;
- layer-cake or monotone-function theorem for `exp(μ·)`;
- finiteness of the independent maximum MGF.

### WP21 — Codebook normalization

- Gram PSD and diagonal;
- `R=((m-1)/m)G+J/m` admissible;
- common-Gaussian representation;
- MGF normalization identity;
- regular-simplex matrix maps to identity.

### WP22 — Bayes/ML identity

- pointwise maximum of class densities;
- integral identity;
- deferred measurable selector/tie partition;
- final operational theorem.

### WP23 — Audit and publication preparation

- remove scratch/scaffold dependencies;
- `#print axioms` dossier;
- provenance/license review;
- docs and theorem map;
- independent proof review.

---

## 13. Dependency graph and parallel execution

```text
WP00 ──┬── WP01 external/API spikes
       ├── WP02 core matrix wrappers
       └── WP03 normal calculus base

WP03 ──> WP04 r/H/ℓ
WP02 ──> WP05 inverse/coercivity
WP04 + WP05 ──> WP06 compact maximizer
WP06 ──> WP07 stationarity/witnesses
WP03 + WP07 + WP08 ──> WP09 conditional PD orthant

WP01 ──> WP10 Prékopa wrapper
WP10 + WP02 ──> WP11 rectangles
WP11 ──> WP12 even factors
WP10 + WP12 ──> WP13 self-convolution
WP13 + Gaussian independence ──> WP14 sum-difference
WP13 + CLT ──> WP15 dyadic CLT
WP01 density + WP15 ──> WP16 positive lower bound
WP14 + WP16 ──> WP17 centered product

WP09 + WP17 ──> WP18 PD orthant
WP18 ──> WP19 singular theorem
WP19 ──> WP20 MGF
WP20 + WP21 + WP22 ──> final weak simplex theorem
```

### Parallel waves

#### Wave A — first two weeks

- foundation/CI/skills;
- external port spikes;
- normal calculus;
- matrix coercivity/rank-one lemma;
- theorem skeletons.

#### Wave B — weeks 3–6

- adaptive branch: WP06–WP09;
- product branch: WP10–WP14;
- Gaussian density/shift ports hardened.

#### Wave C — weeks 6–10

- CLT and positive lower bound;
- centered product integration;
- unconditional positive-definite orthant theorem.

#### Wave D — weeks 10+

- singular limit;
- maxima/MGF;
- coding and operational packaging;
- audit and documentation.

Calendar ranges are planning estimates, not commitments; the density-ratio and Prékopa port spikes determine the actual schedule.

---

## 14. Codex ultra coordination protocol

### 14.1 Work-package card

Every task given to an agent must include:

- owned file set;
- frozen theorem statement;
- allowed imports;
- prerequisite theorem names;
- forbidden shortcuts;
- exact acceptance command;
- required axiom report;
- mathematical source section.

### 14.2 File ownership

One agent owns one file at a time. Parallel agents use disjoint files or separate worktrees. Public theorem signatures are changed only by the integration lead.

### 14.3 Scaffold policy

Downstream work may assume an upstream theorem only through an explicit parameter or a non-production `Scaffold` module. Never declare a project-level axiom. Final `Main.lean` must not import `Scaffold` or `Scratch`.

### 14.4 Search and proof loop

For each lemma:

1. inspect the exact goal with LSP;
2. search local project and mathlib;
3. test candidate declarations in a scratch/example block;
4. write the smallest stable proof;
5. compile the touched file;
6. run diagnostics and linters;
7. record any new reusable helper;
8. checkpoint only after the package acceptance theorem compiles.

### 14.5 Statement safety

The agent must stop and report rather than:

- add an assumption;
- weaken a quantifier;
- change `≤` to `<` or conversely;
- change real integrals to extended-real statements without a bridge;
- replace a covariance hypothesis with a stronger one;
- restrict to nonsingular covariance in a final theorem;
- introduce a custom axiom;
- hide an unresolved theorem behind `by classical exact ...` plus a placeholder.

### 14.6 Review cadence

- leaf lemma: local self-review;
- work package: `/lean4:review` plus integration review;
- M1/M2/M3: independent mathematical reviewer;
- external port: separate provenance/axiom reviewer.

---

## 15. Risk register

| Risk | Probability | Impact | Mitigation |
|---|---:|---:|---|
| Prékopa source fails to port cleanly to 4.31.0 | Medium | High | Run two independent port spikes; keep a narrow local 1D fallback. |
| Explicit multivariate Gaussian density ratio is expensive | High | High | Treat as week-one spike; selectively port StatLean density infrastructure; isolate exact required theorem. |
| `H'(s)>0` becomes measure-theoretically cumbersome | Medium | Medium | Prototype variance and double-integral proofs before choosing. |
| Positive quadratic coercivity lacks a ready theorem | Medium | Medium | Prove once by compact unit sphere; keep it independent of probability code. |
| EuclideanSpace/function coercions destabilize matrix proofs | High | Medium | Centralize conversions and use `toEuclideanCLM`; avoid mixed representations within lemmas. |
| Product layer cake causes ENNReal/real friction | High | Medium | Keep nonnegative inequality internally in ENNReal and expose a finite real wrapper. |
| Canonical i.i.d. sequence for CLT is laborious | Medium | High | Build a reusable product-measure sequence module; inspect StatLean's Pi helpers. |
| Sum–difference independence proof is elaboration-heavy | Medium | Medium | Use existing Gaussian-law independence theorem, not characteristic-function algebra from scratch. |
| Whole-repository external dependency creates version churn | High | High | Vendor minimal audited source and wrap it locally. |
| Codex rewrites statements or overuses autonomous synthesis | Medium | High | Project skill, frozen interfaces, `statement-policy=preserve`, `commit=never`, integration ownership. |
| Operational decoder ties consume excessive time | Medium | Low for M3 | Defer until after covariance/MGF theorem; define Bayes value first. |
| Proof compiles only with extreme heartbeats | Medium | Medium | Refactor into helper lemmas; profile; local heartbeat overrides only. |
| Singular product theorem becomes a distraction | Medium | Medium | Explicitly remove it from the dependency graph. |

### Highest-risk order

1. positive-definite multivariate Gaussian density ratio;
2. Prékopa port and wrapper;
3. normalized self-convolution law plus CLT;
4. `H'>0` scalar proof;
5. Euclidean/matrix derivative and coercivity engineering.

---

## 16. Revised effort estimate

The v3 covariance formulation and the `s`-space reparameterization materially reduce the adaptive branch, but they do not remove the product-theorem critical path.

### With successful selective reuse

| Block | Expert person-weeks |
|---|---:|
| Baseline, APIs, agent configuration | 1–2 |
| Normal CDF, moments, Mills, `r/H/ℓ` | 3–6 |
| Matrix inverse/coercivity/rank-one bound | 2–4 |
| `s`-space variational witnesses | 3–5 |
| Gaussian shift and tilted factors | 2–4 |
| Prékopa/rectangle/layer cake | 4–8 |
| Self-convolution/sum–difference/CLT | 7–13 |
| Density lower bound/product theorem integration | 4–8 |
| Singular limit, MGF, coding, operational layer | 4–7 |
| Audit/refactor/documentation | 2–4 |
| **Total** | **32–61 person-weeks before parallel overlap** |

Because several blocks overlap and external ports may collapse multiple rows, a realistic integrated planning range is approximately **22–40 effective expert-weeks** with successful reuse and strong coordination.

### Without successful reuse

Add approximately 10–20 expert-weeks for a local Prékopa proof, density infrastructure, and shift machinery. The total may reach 32–60 effective expert-weeks.

### Calendar interpretation

- one primary Codex ultra agent with continuous expert review: roughly 16–28 weeks;
- four to six effective agents with strict file ownership and daily integration: roughly 10–18 weeks;
- conditional M1 adaptive certificate: roughly 4–8 expert-weeks.

These ranges are uncertainty bounds, not promises. The week-one port/density spikes should replace them with measured estimates.

### Expected code volume

- with selective reuse: approximately 8,000–20,000 lines of project Lean;
- without reuse: approximately 15,000–30,000 lines.

Generated or vendored code should be reported separately from original project code.

---

## 17. First fourteen days

### Days 1–2

- add `lean-toolchain` and correct Lake options;
- verify the pinned repository-local `.agents/skills/lean4` copy;
- configure and test Lean LSP MCP;
- create module skeleton and CI;
- create `AGENTS.md`, project skill, `PROVENANCE.md`, and `Audit/Axioms.lean`.

### Days 3–5

Parallel spikes:

- compile LeanPool Prékopa source on 4.31.0;
- compile StatLean Prékopa/Anderson subset on 4.31.0;
- port `multivariateGaussian_withDensity_exp_shift`;
- locate/port/prove the density-ratio theorem;
- prove a toy positive quadratic coercivity lemma;
- prove a toy coordinate marginal/orthant boundary lemma.

### End-of-week-one gate

Publish:

- selected Prékopa source;
- selected Gaussian shift source;
- density-ratio strategy;
- exact imports and transitive vendor closure;
- clean axiom reports for all ported top theorems;
- revised measured port cost.

### Days 6–10

- complete project CDF/PDF API;
- prove both truncated moments;
- prototype both `H'>0` proofs and select one;
- prove rank-one inverse bound;
- define `\widetilde\Psi` and compile continuity/trial evaluation;
- instantiate the one-dimensional CLT in a toy canonical i.i.d. example.

### Days 11–14

- finish `ℓ` endpoint lemmas;
- finish compact-superlevel theorem;
- prove coordinate derivative formula in dimension two, then generalize;
- freeze `AdaptiveWitnesses` interface;
- freeze centered-product interface;
- prove one nontrivial Prékopa marginalization example;
- update risk/effort ledger.

### End-of-week-two gate

Required:

- clean full build;
- no trusted-source placeholders;
- `H_deriv_pos` compiled;
- rank-one inverse bound compiled;
- compact-superlevel theorem compiled or reduced to one named coercivity blocker;
- exact Prékopa and density interfaces selected;
- conditional orthant branch and product branch interfaces frozen.

---

## 18. Definition of done

### M1 is done when

- `exists_adaptiveWitnesses` compiles;
- the Gaussian shift theorem compiles;
- tilted factors satisfy the centered-product hypotheses;
- the positive-definite orthant theorem compiles under an explicit centered-product parameter;
- `#print axioms` shows only accepted foundational axioms.

### M2 is done when

- `centered_product_of_posDef` compiles with no theorem parameter;
- the CLT and density lower-bound chain is complete;
- no singular-factor continuity theorem is imported;
- the top theorem has a clean axiom report;
- a second reviewer verifies the deficit direction and lower-bound contradiction.

### M3 is done when

- `lowerOrthant_ge_iid` compiles for singular admissible covariance;
- the lower orthant's frontier-null proof uses coordinate marginals explicitly;
- no scaffold/vendor-unaudited import reaches the theorem;
- the matrix-form theorem exactly matches the intended quantifiers.

### M4 is done when

- the MGF comparison compiles;
- normalized covariance algebra and regular-simplex identity compile;
- Bayes/ML integral identity compiles;
- the final equal-energy classification theorem compiles;
- duplicate codewords/ties are handled or the operational theorem is stated through the Bayes value with a separately certified selector theorem.

### M5 is done when

- clean clone and `lake build` succeed;
- all dependencies and external source commits are pinned;
- `PROVENANCE.md` is complete;
- `Audit/Axioms.lean` covers every public milestone theorem;
- no `sorry`, `admit`, project axiom, or unaudited external theorem remains;
- the repository contains a theorem dependency map and the README contains reproduction instructions and a paper-to-Lean theorem correspondence table.

---

## 19. Final handoff directive for Codex ultra

Use the following as the governing implementation instruction.

> Formalize the matrix-form lower-orthant theorem first. Keep the analytic core independent of codebooks. Implement the adaptive branch through the unconstrained `s`-space potential `\widetilde\Psi_c`, not through `H⁻¹`, `τ`, `𝓕`, or the paper's `(q,v)` objective. Prove only the positive-definite centered product theorem; handle singular covariance once, at the outer orthant theorem. Freeze all public statements before proof search. Reuse third-party Prékopa, density, and Gaussian-shift code only after a successful Lean 4.31.0 port and transitive `#print axioms` audit. Use explicit theorem parameters for temporary upstream dependencies, never a project axiom. Do not use whole-paper autoformalization, autonomous statement rewriting, or autonomous commits. A work package is complete only when its acceptance theorem builds, its source contains no placeholders, and its axiom report is clean.

---

## 20. Research snapshot and provenance references

### Project sources

- earlier internal formalization report
- `simplex_optimality_proof.v3.md`
- Abhijeet Mulgund, [*Stochastic Domination of Gaussian Maxima: A Resolution of the Weak Simplex Conjecture*](https://arxiv.org/abs/2607.14087), arXiv:2607.14087
- `lakefile.toml`
- `lake-manifest.json`

### Exact mathlib baseline

- repository: `leanprover-community/mathlib4`
- commit: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- release input: `v4.31.0`

### Lean workflow source

- project copy: `.agents/skills/lean4`
- Claude discovery link: `.claude/skills/lean4`
- imported from local checkout: `~/dev/lean4-skills/plugins/lean4/skills/lean4`
- snapshot commit: `769fb59f9abdacdf990af1a874290eb8c7994191`
- license: MIT

### External Lean candidates

- `hojonathanho/isoperimetric`, commit `29768f8beeaf17295cdf3853d37da35d7e2b0a5f`, Apache 2.0
- `Vilin97/lean-pool`, commit `9c296f447f48f3242df5e65e0b6120ddffcd79a7`
- `StatLean/Stat-Lean`, commit `31c61ed887bf3be0def314a3b3e5375d203b5ba1`, Apache 2.0

### Required audit commands

```bash
lake build

grep -RInE '\b(sorry|admit)\b' WeakSimplexConjectureLean
grep -RInE '^[[:space:]]*axiom[[:space:]]' WeakSimplexConjectureLean
grep -RInE '^[[:space:]]*unsafe[[:space:]]' WeakSimplexConjectureLean
```

```lean
#print axioms WeakSimplex.centered_product_of_posDef
#print axioms WeakSimplex.exists_adaptiveWitnesses
#print axioms WeakSimplex.lowerOrthant_ge_iid_of_posDef
#print axioms WeakSimplex.lowerOrthant_ge_iid
#print axioms WeakSimplex.weak_simplex
#print axioms WeakSimplex.weak_simplex_of_scoreMaximizingDecoders
```

---

## 21. Final verdict

The proof remains a credible and worthwhile Lean target. The v3 covariance formulation is better than the paper's earlier codebook-space potential for formalization, and the additional `s`-space reparameterization makes the adaptive branch substantially leaner still. The resulting plan removes several of the old report's most delicate obligations: no global inverse of `H`, no auxiliary endpoint function `𝓕`, no open-domain boundary proof, no uniqueness theorem, no Gram realization in the analytic core, and no singular centered-product extension.

The project is still not a routine formalization. Its decisive difficulty is the direct centered product theorem, especially the Prékopa interface, the explicit multivariate density ratio, and the normalized self-convolution/CLT chain. Those risks are concrete, testable in the first week, and partially addressable through existing Lean code.

The recommended strategy is therefore not a monolithic paper translation. It is a two-branch certification program:

1. complete the conditional positive-definite orthant theorem through the new `s`-space potential; and
2. independently complete the positive-definite centered product theorem.

Integrate them only after both branches have clean interfaces and axiom reports, then perform the singular limit and coding reduction. This gives the Codex agent a precise critical path, useful intermediate certificates, and a trust boundary that can be audited mechanically.
