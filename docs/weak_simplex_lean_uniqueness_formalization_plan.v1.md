# Lean Formalization Plan — Uniqueness Extension
## Strict Gaussian lower-orthant comparison and uniqueness of the regular simplex

- **Status:** implemented and certified
- **Date:** 2026-07-19
- **Repository:** `https://github.com/abhmul/weak-simplex-conjecture-lean`
- **Baseline branch:** `main`
- **Baseline commit:** `b86317606e04b8956611b7dacbf822112b97ea66`
- **Lean baseline:** `leanprover/lean4:v4.31.0`
- **Pinned mathlib commit:** `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- **Existing architecture source:** `docs/weak_simplex_lean_formalization_report.v3-reassessment.md`
- **Mathematical source for the extension:** the theorem derivations in this dossier. The uniqueness manuscript named by the original draft was not present in the baseline checkout, and the public arXiv record was still v1 when U00 was run; source-level comparison remains a review item.
- **Primary certification target:** equality in decoding success at one signal strength `lam > 0` holds if and only if the code Gram matrix is the regular-simplex Gram matrix
- **Implementation result:** work packages U00–U12 and U14 are complete; the optional U13 orthogonal-congruence layer is deferred
- **Certification result:** the 3244-job warning-clean build passes, all 139 audited Lean declarations use exactly the accepted foundational axioms, all 50 repository Python tests pass, and all 18 retained numerical diagnostics pass outside the trusted proof boundary
- **Reading note:** the body below preserves the baseline-relative implementation directive and frozen target interfaces as an audit record; completion state and any deliberate implementation refinements are recorded in the work-package logs and metadata above

---

## 0. Executive decision

The completed formalization should be **extended rather than rewritten**. The existing positive-definite adaptive-tilt branch, centered product theorem, singular outer approximation, stochastic-order reduction, common-Gaussian normalization, and decoder API should remain intact.

The uniqueness extension should add one new rigidity branch whose central theorem is

```lean
/-- Strict lower-orthant comparison away from the independent covariance. -/
theorem lowerOrthant_gt_iid_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (c : ℝ) :
    (gaussianReal 0 1) (Set.Iic c) ^ m <
      (multivariateGaussian 0 R) (lowerOrthant c)
```

for every finite `c`.

The recommended implementation is deliberately **not** a Lean translation of the new endpoint/Gram-space variational problem. Instead, use a formalization-specific compactness argument to extend the **already formalized** positive-definite adaptive witnesses to singular admissible covariances. This is the key simplification.

For the regularizations

\[
R_n=(1-\varepsilon_n)R+\varepsilon_n I,
\qquad \varepsilon_n\downarrow0,
\]

the current theorem `exists_adaptiveWitnesses` supplies witnesses `(s_n,a_n)` for `R_n`. Their existing value and compatibility fields imply a covariance-independent compact bound on `s_n`. A convergent subsequence therefore produces an `AdaptiveWitnesses R c` object directly. No `H⁻¹`, endpoint potential `𝓕`, matrix factorization, or second variational proof is needed.

The other new analytic input is strictness in the first sum–difference step for the adaptive half-lines. Formalize only the equality information actually required:

1. finite positive symmetric rectangles are strict unless the covariance is the identity;
2. the normalized self-convolutions of the adaptive half-lines satisfy the non-strict product inequality at singular covariance by a small continuous-factor regularization lemma;
3. the conditional sum–difference inequality is strict on a positive-probability set.

This route reuses the completed implementation maximally and avoids formalizing the Nakamura–Tsuji equality theorem, the full equality theory of the centered product theorem, or a second singular variational architecture.

### Bottom-line theorem ladder

The trusted extension should certify, in this order:

1. `symmetricRectangle_gt_iid_of_ne_one`;
2. `centeredTiltedHalfLine_product_lt_of_ne_one`;
3. `exists_adaptiveWitnesses_of_weakSimplexCov`;
4. `lowerOrthant_gt_iid_of_ne_one` and `lowerOrthant_eq_iid_iff`;
5. `gaussianMax_mgf_lt_regularSimplex` for `mu > 0`;
6. `gramGaussianMax_mgf_lt_regularSimplex` for `lam > 0`;
7. strict and equality-characterization versions of `bayesValue_le_regularSimplex`, `weak_simplex`, and `weak_simplex_of_scoreMaximizingDecoders`.

The canonical formal uniqueness conclusion should be **Gram-matrix equality**. Orthogonal congruence of two realizations with the same full-rank Gram matrix is mathematically standard but is a separate linear-algebra package and should not block the core result.

---

## 1. What is already complete and should be reused

The baseline repository already contains the full non-strict proof chain. The uniqueness work should treat the following declarations as frozen dependencies unless a narrowly scoped refactor is explicitly listed below.

| Existing layer | Principal declaration(s) | Role in uniqueness extension |
|---|---|---|
| Covariance predicates | `IsCorrelation`, `IsWeakSimplexCov` | Reuse unchanged. |
| Scalar tilt calculus | `r`, `H`, `localLogMass`, `r_pos`, `H_deriv_pos`, `localLogMass_neg`, `localLogMass_tendsto_atBot` | Supplies all scalar facts needed for compact singular-witness extraction, except `H_pos`, which should be added. |
| Positive-definite witnesses | `AdaptiveWitnesses`, `exists_adaptiveWitnesses` | Reuse as the source of a witness sequence for regularized covariances. |
| Tilted half-lines | `centeredTiltedHalfLine` and its mass, barycenter, boundedness, measurability, and log-concavity lemmas | Reuse unchanged; add a normalized wrapper and a self-convolution continuity theorem. |
| Non-strict rectangles | `symmetricRectangle_ge_iid_of_posDef` and the regression machinery in `Product/SymmetricRectangle.lean` | Generalize the public induction theorem from `PosDef` to `PosSemidef`; the one-step regression lemma already uses only positive semidefiniteness. |
| Positive-definite product theorem | `centered_product_of_posDef` | Reuse unchanged inside a continuous-factor singular limit. Do not re-prove the CLT branch. |
| Sum–difference rotation | `map_multivariateGaussian_sumDifference_eq_prod`, `normalizedSelfConvolution_product_deficit_of_posDef` and private helper definitions in `Product/SumDifference.lean` | Reuse the rotation identity; expose or duplicate only the small helper interface required by the strict specialized proof. |
| Non-strict singular orthant theorem | `lowerOrthant_ge_iid` | Reuse both as the existing theorem and, deliberately, to prove that the strictness set in the sum–difference argument has positive probability. |
| Stochastic/MGF reduction | `coordinateMax_tail_le_iid`, `gaussianMax_mgf_le_regularSimplex` | Add strict companions; retain old declarations. |
| Gram normalization | `regularSimplexGram`, `gramNormalization`, `gramMgf_normalization_identity` | Add an equality/rigidity lemma and strict companions. |
| Decoder layer | `bayesValue_eq_gramMgf`, `decoderSuccessOf_eq_bayesValue`, `weak_simplex`, `weak_simplex_of_scoreMaximizingDecoders` | Add strict and iff declarations for `lam > 0`. |
| Trust audit | `WeakSimplexConjectureLean/Audit/Axioms.lean` and repository scripts | Extend to every new public rigidity theorem. |

### Governing architecture update (completed)

At the baseline, `AGENTS.md` said that singular covariance was handled only at the outer lower-orthant theorem. That remains correct for the completed non-strict branch, but the rigidity extension required two tightly controlled exceptions:

- a continuous-factor singular limit used only after one strict sum–difference step;
- a compact limit of positive-definite `AdaptiveWitnesses` used only to construct witnesses for the strict theorem.

`AGENTS.md` now records that this uniqueness plan supersedes the old singular-only-at-the-boundary rule only inside explicitly scoped extension modules and preserves the prohibition on a wholesale singular rewrite of the centered product theorem.

---

## 2. Formal theorem targets

### 2.1 Strict symmetric rectangles

```lean
/-- The symmetric rectangle comparison for an arbitrary correlation matrix. -/
theorem symmetricRectangle_ge_iid
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsCorrelation R)
    (rad : Fin m → ℝ)
    (hrad : ∀ i, 0 ≤ rad i) :
    (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))) ≤
      multivariateGaussian (0 : Coord m) R (symmetricRectangle rad)

/-- A finite nondegenerate symmetric rectangle is strict unless `R = I`. -/
theorem symmetricRectangle_gt_iid_of_ne_one
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsCorrelation R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (rad : Fin m → ℝ)
    (hrad : ∀ i, 0 < rad i) :
    (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))) <
      multivariateGaussian (0 : Coord m) R (symmetricRectangle rad)

/-- Equality characterization for finite positive radii. -/
theorem symmetricRectangle_eq_iid_iff
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsCorrelation R)
    (rad : Fin m → ℝ)
    (hrad : ∀ i, 0 < rad i) :
    multivariateGaussian (0 : Coord m) R (symmetricRectangle rad) =
        ∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i)) ↔
      R = (1 : Matrix (Fin m) (Fin m) ℝ)
```

The strict theorem should be proved directly from the existing regression induction. Do not formalize Nakamura–Tsuji.

### 2.2 Continuous-factor singular product bridge

The full singular centered product theorem is not required. Add only the following reusable strengthening of the existing positive-definite theorem.

```lean
/-- The centered product theorem at singular covariance for continuous factors. -/
theorem centered_product_of_continuous
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsCorrelation R)
    (f : Fin m → ℝ → ℝ)
    (hf_cont : ∀ i, Continuous (f i))
    (hf_meas : ∀ i, Measurable (f i))
    (hf_nonneg : ∀ i x, 0 ≤ f i x)
    (hf_bounded : ∀ i, Bornology.IsBounded (Set.range (f i)))
    (hf_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (f i x)))
    (hf_mass_pos : ∀ i, 0 < ∫ x, f i x ∂gaussianReal 0 1)
    (hf_barycenter : ∀ i, ∫ x, x * f i x ∂gaussianReal 0 1 = 0) :
    (∏ i, ∫ x, f i x ∂gaussianReal 0 1) ≤
      ∫ x, ∏ i, f i (x i) ∂multivariateGaussian 0 R
```

This theorem is proved by covariance regularization and bounded convergence. It does not require a classification of discontinuities of arbitrary log-concave functions.

### 2.3 Strict product inequality for the actual adaptive factors

Prefer a theorem specialized to the existing `centeredTiltedHalfLine` parameterization.

```lean
/-- The adaptive centered half-lines have a strict product gain away from independence. -/
theorem centeredTiltedHalfLine_product_lt_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (s : Coord m) :
    (∏ i, ∫ z, centeredTiltedHalfLine (s i) z ∂gaussianReal 0 1) <
      ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
        ∂multivariateGaussian 0 R
```

A more general theorem for arbitrary `a_i,b_i` may be added later, but it is not on the critical path.

### 2.4 Singular adaptive witnesses

Keep the existing `AdaptiveWitnesses` structure. Add a second constructor theorem rather than replacing the positive-definite one.

```lean
/-- Adaptive witnesses exist for every admissible covariance, including singular ones. -/
theorem exists_adaptiveWitnesses_of_weakSimplexCov
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    Nonempty (AdaptiveWitnesses R c)
```

This theorem should be proved by compactness of witnesses for regularized covariances, as detailed in Section 3.3 below.

### 2.5 Strict lower orthants and equality

```lean
/-- Strict lower-orthant comparison away from the identity covariance. -/
theorem lowerOrthant_gt_iid_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (c : ℝ) :
    (gaussianReal 0 1) (Set.Iic c) ^ m <
      (multivariateGaussian 0 R) (lowerOrthant c)

/-- Equality at one finite threshold characterizes independence. -/
theorem lowerOrthant_eq_iid_iff
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian 0 R) (lowerOrthant c) =
        (gaussianReal 0 1) (Set.Iic c) ^ m ↔
      R = (1 : Matrix (Fin m) (Fin m) ℝ)
```

### 2.6 Strict stochastic and MGF comparison

```lean
/-- Strict upper-tail comparison away from identity. -/
theorem coordinateMax_tail_lt_iid_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (c : ℝ) :
    (multivariateGaussian 0 R) {x | c < coordinateMax hm x} <
      (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ))
        {x | c < coordinateMax hm x}

/-- Positive exponential moments are strictly smaller away from identity. -/
theorem gaussianMax_mgf_lt_regularSimplex
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (mu : ℝ) (hmu : 0 < mu) :
    mgf (coordinateMax hm) (multivariateGaussian 0 R) mu <
      mgf (coordinateMax hm)
        (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu
```

Also add an equality iff theorem for the MGF at any one `mu > 0`.

```lean
/-- Equality of one positive exponential moment characterizes independence. -/
theorem gaussianMax_mgf_eq_regularSimplex_iff
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (mu : ℝ) (hmu : 0 < mu) :
    mgf (coordinateMax hm) (multivariateGaussian 0 R) mu =
        mgf (coordinateMax hm)
          (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu ↔
      R = (1 : Matrix (Fin m) (Fin m) ℝ)
```

### 2.7 Gram and operational uniqueness

```lean
/-- The normalization equals identity exactly at the regular-simplex Gram matrix. -/
theorem gramNormalization_eq_one_iff
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) :
    ((((m : ℝ) - 1) / (m : ℝ)) • G +
        (1 / (m : ℝ)) • allOnesMatrix m =
      (1 : Matrix (Fin m) (Fin m) ℝ)) ↔
      G = regularSimplexGram m

/-- Strict Gram-level MGF comparison. -/
theorem gramGaussianMax_mgf_lt_regularSimplex
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G)
    (hGne : G ≠ regularSimplexGram m)
    (lam : ℝ) (hlam : 0 < lam) :
    mgf (coordinateMax (Nat.zero_lt_of_lt hm))
        (multivariateGaussian 0 G) lam <
      mgf (coordinateMax (Nat.zero_lt_of_lt hm))
        (multivariateGaussian 0 (regularSimplexGram m)) lam

/-- Equality of one positive Gram-level MGF characterizes the regular simplex. -/
theorem gramGaussianMax_mgf_eq_regularSimplex_iff
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G)
    (lam : ℝ) (hlam : 0 < lam) :
    mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 G) lam =
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 (regularSimplexGram m)) lam ↔
      G = regularSimplexGram m
```

Final coding targets:

```lean
/-- Strict Bayes-value comparison for a non-simplex Gram matrix. -/
theorem bayesValue_lt_regularSimplex
    {m n k : ℕ} (hm : 1 < m)
    (code : Fin m → Coord n) (simplex : Fin m → Coord k)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram m)
    (hcode_ne : codeGram code ≠ regularSimplexGram m)
    (lam : ℝ) (hlam : 0 < lam) :
    bayesValue (Nat.zero_lt_of_lt hm) code lam <
      bayesValue (Nat.zero_lt_of_lt hm) simplex lam

/-- Equality in Bayes value is equivalent to the regular-simplex Gram matrix. -/
theorem bayesValue_eq_regularSimplex_iff
    {m n k : ℕ} (hm : 1 < m)
    (code : Fin m → Coord n) (simplex : Fin m → Coord k)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram m)
    (lam : ℝ) (hlam : 0 < lam) :
    bayesValue (Nat.zero_lt_of_lt hm) code lam =
        bayesValue (Nat.zero_lt_of_lt hm) simplex lam ↔
      codeGram code = regularSimplexGram m
```

Add corresponding `decoderSuccess` and arbitrary measurable score-maximizing-decoder theorems. Every uniqueness theorem must assume `lam > 0`. At `lam = 0`, all codebooks have the same value, so uniqueness is false.

Freeze their names as `weak_simplex_strict`, `weak_simplex_eq_iff_codeGram_eq`, `weak_simplex_strict_of_scoreMaximizingDecoders`, and `weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders`. Their arguments mirror the corresponding existing non-strict theorem, with `hlam : 0 < lam`; strict variants additionally assume `codeGram code ≠ regularSimplexGram (n + 1)`, while iff variants conclude equality of success values iff `codeGram code = regularSimplexGram (n + 1)`.

---

## 3. Recommended proof architecture

## 3.1 Generalize the rectangle induction from positive definite to positive semidefinite

The existing private theorem `symmetricRectangle_step` already assumes only

```lean
hR : R.PosSemidef
```

and the unit diagonal. The public induction theorem was restricted to `PosDef` only because that was all the original product proof required. Copy the induction with the following substitutions:

- use `hR.submatrix Fin.castSucc` instead of the positive-definite submatrix theorem;
- retain the same regression residual and last-coordinate independence proof;
- retain the same even log-concave shift-mass argument.

The old `symmetricRectangle_ge_iid_of_posDef` should remain available, ideally as a one-line wrapper around the new PSD theorem.

## 3.2 Prove strictness inside the existing regression induction

For `R : Matrix (Fin (n+1)) (Fin (n+1)) ℝ`, let

```lean
β := regressionSlope R
q := regressionShiftMass R firstRadii
```

The existing proof gives

\[
\gamma([-r,r])\int q\,d\gamma
\le
\int_{[-r,r]}q\,d\gamma.
\]

Add a strict version when `β ≠ 0` and all radii are positive.

The most Lean-friendly strictness argument avoids continuity of `q`.

1. `q` is measurable, even, and log-concave, hence antitone on `[0,∞)`; the existing file already proves the required non-strict monotonicity.
2. The total integral of `q` is the first-coordinate rectangle probability. By the new PSD rectangle theorem, it is at least a product of positive one-dimensional interval probabilities, hence is strictly positive.
3. Choose `j` with `β j ≠ 0`. Bound
   \[
   q(t)\le \Pr\{|Y_j+\beta_jt|\le r_j\}.
   \]
   The right side tends to zero as `t → +∞`, using only probability tails on the real line. Thus `q(t) → 0`.
4. Let `r` be the last radius.
   - If `q r = 0`, antitonicity implies `q=0` outside `[-r,r]`, while the total integral is positive. Therefore the inside integral is strictly larger than `q r · γ([-r,r]) = 0`.
   - If `q r > 0`, choose `b > r` with `q b < q r`. On the positive-measure interval `[b,b+1]`, antitonicity gives `q ≤ q b < q r`. Hence the outside integral is strictly smaller than `q r · γ([-r,r]^c)`.
5. Combine the strict inside/outside comparison exactly as in the existing threshold proof.

Package the one-dimensional measure argument as a reusable private or internal theorem. Do not introduce covariance as a real expectation unless it makes the Lean proof shorter; the current ENNReal set-integral formulation is already close to the needed inequalities.

### Strict induction without coordinate permutations

Proceed by induction on `m` and split on `β = 0`.

- If `β ≠ 0`, the last regression step is strict; combine it with the non-strict induction theorem for the first `m-1` coordinates.
- If `β = 0`, show that `R ≠ I` implies the leading principal submatrix is not the identity. Apply the strict induction hypothesis to that submatrix, multiply by the strictly positive last interval probability, and finish with the non-strict last step.

To prove the matrix implication in the second branch, use:

- `R.PosSemidef` gives Hermitian symmetry;
- `β = 0` gives the last column off the diagonal;
- Hermitian symmetry gives the last row;
- the diagonal hypothesis gives the final diagonal entry;
- if the leading submatrix is identity, matrix extensionality over `Fin.cases` gives `R = 1`.

This is preferable to formalizing covariance permutations.

## 3.3 Construct singular adaptive witnesses by compactness

This is the central implementation simplification.

Let

\[
L=m\log\Phi(c)<0,
\qquad
R_n=(1-\varepsilon_n)R+\varepsilon_nI,
\qquad
\varepsilon_n=2^{-(n+1)}.
\]

For each `n`, choose

```lean
w n : AdaptiveWitnesses (regularizedCovariance R (regularizationEpsilon n)) c
```

using the existing `exists_adaptiveWitnesses` theorem.

Write `s_n = (w n).s`, `a_n = (w n).a`, and `R_n` for the regularized covariance. The witness fields imply

\[
\sum_i \operatorname{localLogMass}(s_{n,i})
-\frac12 qform(R_n,a_n)
\ge L.
\]

The following bounds are uniform in `n`.

### 3.3.1 Uniform quadratic bound

Since every `localLogMass` is nonpositive,

\[
qform(R_n,a_n)\le -2L.
\]

Formal helper:

```lean
lemma AdaptiveWitnesses.qform_le_of_value
    ... : qform R w.a ≤ -2 * ((m : ℝ) * Real.log (normalCDF c))
```

The proof uses only `w.value_bound`, `w.a_eq_r`, `localLogMass`, `localLogMass_neg`, and positive semidefiniteness of `R`.

### 3.3.2 Uniform lower coordinate bound

For each coordinate `i`, all other local-log-mass terms and the quadratic penalty are nonpositive, so

\[
L\le \operatorname{localLogMass}(s_{n,i}).
\]

Use `localLogMass_tendsto_atBot` to choose one `B` such that

\[
s_{n,i}\ge B
\]

for every `n,i`.

### 3.3.3 Uniform upper coordinate bound

Prove the matrix lemma

```lean
lemma sq_matrixMul_apply_le_qform_of_isCorrelation
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : IsCorrelation R) (a : Coord m) (i : Fin m) :
    (matrixMul R a i) ^ 2 ≤ qform R a
```

A direct proof avoids spectral theory: apply nonnegativity of `qform R` to

```lean
a - (matrixMul R a i) • basisVector i
```

and expand, using `R i i = 1` and Hermitian symmetry.

The uniform quadratic bound gives

\[
(R_na_n)_i\le \sqrt{-2L}.
\]

Compatibility and positivity of `a_{n,i}` give

\[
s_{n,i}
=c+(R_na_n)_i-a_{n,i}
<c+(R_na_n)_i
\le c+\sqrt{-2L}.
\]

Thus all `s_n` lie in one closed Euclidean box, hence in one compact closed ball.

### 3.3.4 Extract and pass to a subsequential limit

Use sequential compactness of the closed ball to obtain a strict monotone subsequence `φ` and

```lean
Tendsto (fun n ↦ s (φ n)) atTop (𝓝 sStar)
```

Define

```lean
aStar := coordinateMap r sStar
```

and prove:

- `a_(φ n) → aStar`, from `w.a_eq_r` and continuity of `r`;
- `R_(φ n) → R` entrywise;
- `matrixMul R_(φ n) a_(φ n) → matrixMul R aStar`, coordinatewise through finite sums;
- compatibility passes to the limit;
- the value expression passes to the limit and the closed inequality is preserved.

Then package

```lean
{
  s := sStar
  a := aStar
  a_eq_r := by intro i; rfl
  a_pos := fun i ↦ r_pos _
  compatibility := ...
  value_bound := ...
}
```

as `AdaptiveWitnesses R c`.

### Why this is preferable to the manuscript's direct singular variational proof

The paper's direct proof introduces the inverse endpoint map, a strictly concave local endpoint potential, a Gram realization, an open domain, compact superlevels away from the domain boundary, and stationarity in `(q,v)`. All of those are mathematically clean, but the current Lean development deliberately avoided them. The compact-limit argument needs only:

- the already certified positive-definite witness theorem;
- the existing scalar endpoint limits;
- one elementary PSD Cauchy bound;
- finite-dimensional sequential compactness and continuity.

Keep the Gram-space variational argument as the fallback in Section 9.1, not the primary path.

## 3.4 Add only the singular product theorem needed after one strict step

The strict sum–difference proof needs

\[
\mathcal Z_R(\mathcal D h_1,\ldots,\mathcal D h_m)\ge1
\]

for singular `R`, where each `h_i` is a normalized centered tilted half-line. Do not formalize the full singular centered product theorem for arbitrary discontinuous log-concave factors.

### 3.4.1 Normalized adaptive factor

Add

```lean
def normalizedCenteredTiltedHalfLine (s x : ℝ) : ℝ :=
  (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ *
    centeredTiltedHalfLine s x
```

and prove mass one, zero barycenter, nonnegativity, boundedness, measurability, and log-concavity using existing lemmas.

### 3.4.2 Positivity of the endpoint

Add

```lean
lemma H_pos (s : ℝ) : 0 < H s
```

A robust proof is

\[
H(s)\Phi(s)
=\int_{-\infty}^s (s-x)\phi(x)\,dx>0.
\]

The integrand is nonnegative and strictly positive on a set of positive Lebesgue measure; `normalCDF_pos` then permits division. This avoids introducing the inverse of `H` or an endpoint limit.

### 3.4.3 Explicit self-convolution and continuity

For `h = normalizedCenteredTiltedHalfLine s`, derive

\[
(\mathcal D h)(u)
=
C_s^2 e^{\sqrt2 r(s)u}
\gamma\bigl([-(\sqrt2H(s)-u),\sqrt2H(s)-u]\bigr)
\]

when `u ≤ √2 H(s)`, and zero otherwise. Equivalently, express the interval mass through `normalCDF`.

At the boundary `u=√2H(s)`, the interval is the singleton `{0}` and has Gaussian measure zero, so the two pieces agree. Deduce

```lean
theorem continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine
    (s : ℝ) :
    Continuous
      (normalizedSelfConvolution (normalizedCenteredTiltedHalfLine s))
```

This is the only new continuity theorem required by the critical path.

### 3.4.4 Continuous-factor covariance limit

Move the reusable Gaussian regularization definitions and convergence lemmas currently private in `Orthant/Singular.lean` into a public module, suggested path:

```text
WeakSimplexConjectureLean/Gaussian/Regularization.lean
```

Then prove `centered_product_of_continuous` by:

1. applying `centered_product_of_posDef` to every regularized covariance;
2. coupling the regularized Gaussian vector to the singular one;
3. using continuity and boundedness of the finite product to invoke bounded convergence;
4. passing the constant left side to the limit.

Apply this theorem to the self-convolved normalized adaptive factors.

## 3.5 Prove the strict adaptive product inequality

Let

```lean
h i := normalizedCenteredTiltedHalfLine (s i)
```

and let `U,V` be independent with law `N(0,R)`. The existing Gaussian sum–difference rotation gives

\[
\mathcal Z_R(h)^2
=
\int \mathbb E_V\prod_i
h_i\!\left(\frac{u_i+V_i}{\sqrt2}\right)
 h_i\!\left(\frac{u_i-V_i}{\sqrt2}\right)
\,d\mu_R(u).
\]

For fixed `u`, prove the exact identity

\[
h_i\!\left(\frac{u_i+v}{\sqrt2}\right)
 h_i\!\left(\frac{u_i-v}{\sqrt2}\right)
=
A_i(u_i)\,
\mathbf 1_{[-\rho_i(u),\rho_i(u)]}(v),
\]

where

\[
A_i(u_i)>0,
\qquad
\rho_i(u)=\sqrt2H(s_i)-u_i.
\]

If some `ρ_i(u)<0`, both the independent product and correlated product are zero. If every radius is nonnegative, apply `symmetricRectangle_ge_iid`. If every radius is positive and `R ≠ I`, apply `symmetricRectangle_gt_iid_of_ne_one`.

Define

\[
E=\{u:u_i<\sqrt2H(s_i)\text{ for all }i\}.
\]

To prove `μ_R(E)>0` without formalizing Gaussian support:

1. `H_pos` gives `0 < √2 H(s_i)` for every coordinate;
2. therefore `lowerOrthant 0 ⊆ E`;
3. invoke the already certified non-strict theorem `lowerOrthant_ge_iid`;
4. the iid lower bound is positive because `normalCDF 0 > 0` and `m > 0`.

This deliberate dependency on the completed non-strict orthant theorem is non-circular: the old theorem does not import any rigidity module.

Integrate the pointwise comparison. Use a general strict-integral lemma or integrate the nonnegative difference. The repository already uses `setIntegral_pos_iff_support_of_nonneg_ae`; it is a suitable fallback for proving strictness from `μ_R(E)>0`.

Obtain

\[
\mathcal Z_R(h)^2
>
\mathcal Z_R(\mathcal D h).
\]

The continuous-factor product theorem gives `1 ≤ 𝒵_R(𝒟h)`, hence `1 < 𝒵_R(h)^2`. Since `𝒵_R(h) ≥ 0`, conclude `1 < 𝒵_R(h)` and undo normalization.

## 3.6 Refactor the adaptive orthant reduction once

`Orthant/PositiveDefiniteConditional.lean` currently contains private calculations that are independent of positive definiteness except for the source of witnesses and product inequality. Extract them to a reusable module, suggested path:

```text
WeakSimplexConjectureLean/Orthant/AdaptiveReduction.lean
```

Public or internal declarations should include:

- the adaptive endpoint indicator and its measurability;
- the compatibility preimage identity;
- the exact Gaussian shift/lower-orthant identity for `R.PosSemidef`;
- the product-mass identity;
- the exponential form of `AdaptiveWitnesses.value_bound`.

A useful central lemma is schematically:

```lean
theorem lowerOrthant_eq_adaptiveProduct
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef)
    (c : ℝ)
    (w : AdaptiveWitnesses R c) :
    (multivariateGaussian 0 R) (lowerOrthant c) =
      ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R)
```

Refactor the old positive-definite conditional theorem to use this lemma. Its public statement and proof result must remain unchanged.

## 3.7 Strict lower orthants

For `R ≠ I`, choose `w : AdaptiveWitnesses R c` from the compact-limit theorem. The witness value bound yields

\[
\Phi(c)^m
\le
\exp\!\left(-\frac12a^TRa\right)
\prod_i\int f_i\,d\gamma.
\]

The strict adaptive product theorem yields

\[
\exp\!\left(-\frac12a^TRa\right)
\prod_i\int f_i\,d\gamma
<
\exp\!\left(-\frac12a^TRa\right)
\int\prod_i f_i(x_i)\,dN(0,R)(x),
\]

because the exponential prefactor is strictly positive. The adaptive reduction identifies the final expression with the lower-orthant probability. This proves `lowerOrthant_gt_iid_of_ne_one` directly at the singular covariance.

The equality iff theorem follows by cases on `R = 1`. For the identity case, expose or restate the existing independent-coordinate lower-orthant calculation from `Maxima/StochasticOrder.lean`.

## 3.8 Strict MGF and coding uniqueness

### Strict MGF

Extend the existing layer-cake proof. For `mu > 0`, strict tail comparison at every real threshold implies strict comparison of

\[
\int_0^\infty \Pr(e^{\mu M}>t)\,dt.
\]

A Lean-friendly strictness witness is the level interval `t ∈ Set.Icc 1 2`: every such positive level corresponds to a finite threshold `log t / mu`, so the tail gap is pointwise strict on a set of positive Lebesgue measure. Integrability is already available for Gaussian coordinate maxima.

Add a generic helper if useful:

```lean
theorem mgf_lt_of_tail_lt
    ...
    (htail_le : ∀ c, p {x | c < U x} ≤ q {x | c < V x})
    (htail_lt : ∀ c, p {x | c < U x} < q {x | c < V x})
    (mu : ℝ) (hmu : 0 < mu) :
    mgf U p mu < mgf V q mu
```

The theorem may be private if its general hypotheses create substantial API overhead.

### Gram rigidity

Prove `gramNormalization_eq_one_iff` by matrix extensionality and field algebra. Do not refactor the two existing private normalization definitions unless that refactor demonstrably reduces code. The expanded-expression theorem is enough for the strict Gram result.

Use the existing exact normalization identity. A positive prefactor preserves strict inequality. The normalized covariance is identity if and only if `G = regularSimplexGram m`.

### Decoder equality

At `lam > 0`, strict Gram-MGF comparison transfers through the positive Bayes prefactor. Existing likelihood-maximizing-decoder identities show that every admissible tie-breaking rule has the same Bayes value. Therefore equality in either `decoderSuccess` or `decoderSuccessOf` is equivalent to regular-simplex Gram equality.

Do not state an iff theorem at `lam = 0`.

---

## 4. Proposed module changes

The following layout minimizes disruption to the completed branch.

| Path | Change |
|---|---|
| `AGENTS.md` | Register this plan and the two narrowly scoped singular exceptions for rigidity. |
| `WeakSimplexConjectureLean/Gaussian/Regularization.lean` | New reusable home for covariance regularization, coupling/map law, preservation, and convergence lemmas currently private in `Orthant/Singular.lean`. |
| `WeakSimplexConjectureLean/Orthant/Singular.lean` | Refactor to import the new regularization module; preserve `lowerOrthant_ge_iid`. |
| `WeakSimplexConjectureLean/Product/SymmetricRectangle.lean` | Add PSD non-strict theorem, strict step, strict induction theorem, and equality iff. |
| `WeakSimplexConjectureLean/Product/ContinuousCenteredProduct.lean` | New continuous-factor singular product theorem. |
| `WeakSimplexConjectureLean/Normal/TiltFunctions.lean` | Add `H_pos`. |
| `WeakSimplexConjectureLean/Tilt/NormalizedTiltedHalfLine.lean` | New normalized factor, exact self-convolution formula, continuity. |
| `WeakSimplexConjectureLean/Tilt/SingularWitnesses.lean` | New compact-limit construction of `AdaptiveWitnesses R c` for singular admissible `R`. |
| `WeakSimplexConjectureLean/Orthant/AdaptiveReduction.lean` | Extract covariance-agnostic adaptive shift and value lemmas from the positive-definite conditional module. |
| `WeakSimplexConjectureLean/Rigidity/TiltedHalfLineProduct.lean` | New cross-layer strict sum–difference theorem. It may import the completed non-strict `Orthant/Singular.lean`. |
| `WeakSimplexConjectureLean/Orthant/Strict.lean` | New strict lower-orthant and equality iff theorems. |
| `WeakSimplexConjectureLean/Maxima/StrictStochasticOrder.lean` | Strict CDF/tail declarations. |
| `WeakSimplexConjectureLean/Maxima/StrictExponentialMoments.lean` | Strict MGF and MGF equality iff. |
| `WeakSimplexConjectureLean/Coding/Gram.lean` | Add normalization equality iff. |
| `WeakSimplexConjectureLean/Coding/RegularSimplex.lean` | Add strict Gram-MGF and equality iff. |
| `WeakSimplexConjectureLean/Coding/WeakSimplex.lean` | Add strict Bayes/decoder theorems and equality characterizations. |
| `WeakSimplexConjectureLean/Audit/Axioms.lean` | Audit every new public theorem. |
| `WeakSimplexConjectureLean.lean` | Add public imports after the completed non-strict branch. |
| `docs/theorem-dependencies.md` | Add the rigidity DAG. |
| `README.md` | State strictness and unique Gram optimizer, with the `lam > 0` qualification. |

### Import-cycle rule

`Rigidity/TiltedHalfLineProduct.lean` may import the already completed `Orthant/Singular.lean` solely to prove positive probability of the strictness set. `Orthant/Strict.lean` then imports the rigidity product module. This is acyclic because `Orthant/Singular.lean` must never import any rigidity file.

---

## 5. Work packages

Each package has one acceptance theorem. Do not start the next dependent package until the acceptance theorem builds and its axiom output is clean.

## U00 — Baseline freeze and branch preparation

**Files:** no production proof edits initially.

**Tasks:**

1. verify baseline commit `b86317606e04b8956611b7dacbf822112b97ea66`;
2. run the full build and current audit;
3. keep this plan in `docs/` as the canonical uniqueness architecture;
4. update `AGENTS.md` governing-document order;
5. create a uniqueness worktree or branch;
6. record the exact baseline audit output.

**Acceptance:** the untouched baseline passes `lake build` and `python3 scripts/check_axiom_audit.py`.

## U01 — Reusable Gaussian covariance regularization

**Files:** new `Gaussian/Regularization.lean`; refactor `Orthant/Singular.lean`.

**Acceptance theorem:** the existing `lowerOrthant_ge_iid` compiles unchanged after the refactor.

**Required public/internal API:** `regularizedCovariance`, dyadic epsilon, positivity/range, preservation of `IsWeakSimplexCov`, positive definiteness, map law, and convergence in distribution or the explicit a.s. coupling.

**Risk:** accidental import expansion. Keep the module below both product-continuity and orthant layers.

## U02 — PSD symmetric rectangle inequality

**File:** `Product/SymmetricRectangle.lean`.

**Acceptance theorem:** `symmetricRectangle_ge_iid`.

**Method:** reuse the current induction and `symmetricRectangle_step`; no approximation.

## U03 — Strict symmetric rectangles

**File:** `Product/SymmetricRectangle.lean`, or a tightly coupled `Product/StrictSymmetricRectangle.lean` if compile times become problematic.

**Acceptance theorem:** `symmetricRectangle_gt_iid_of_ne_one`.

**Subtasks:**

- strict threshold-integral lemma;
- tail limit for a shifted one-dimensional marginal;
- positivity of the regression-shift-mass integral;
- `β = 0` matrix reconstruction lemma;
- strict induction;
- equality iff wrapper.

**Primary risk:** ENNReal strict inequality bookkeeping. Prototype the one-dimensional strict threshold lemma in `Scratch/` first.

## U04 — Continuous-factor singular product bridge

**File:** `Product/ContinuousCenteredProduct.lean`.

**Acceptance theorem:** `centered_product_of_continuous`.

**Method:** positive-definite theorem plus U01 coupling and bounded convergence.

**Do not:** classify discontinuities of arbitrary log-concave functions.

## U05 — Normalized adaptive factor and continuous self-convolution

**Files:** `Normal/TiltFunctions.lean`; new `Tilt/NormalizedTiltedHalfLine.lean`.

**Acceptance theorem:**

```lean
continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine
```

**Subtasks:** `H_pos`, normalization properties, exact fixed-average identity, explicit self-convolution formula, boundary continuity.

## U06 — Singular adaptive witnesses by compactness

**File:** new `Tilt/SingularWitnesses.lean`.

**Dependencies:** U01 and the existing positive-definite `exists_adaptiveWitnesses` theorem.

**Acceptance theorem:** `exists_adaptiveWitnesses_of_weakSimplexCov`.

**Subtasks:**

- uniform qform bound;
- coordinate local-log-mass lower bound;
- PSD matrix coordinate Cauchy lemma;
- compact ball containing all regularized witness `s` vectors;
- subsequence extraction;
- continuity of `r`, compatibility, and value under the limit.

**Primary risk:** sequence/subsequence API, not mathematics. Freeze a minimal scratch proof of compact subsequence extraction before writing witness algebra.

## U07 — Adaptive orthant reduction refactor

**Files:** new `Orthant/AdaptiveReduction.lean`; edit `Orthant/PositiveDefiniteConditional.lean`.

**Acceptance theorem:** the existing

```lean
lowerOrthant_ge_iid_of_posDef_of_centeredProduct
```

has the same public statement and compiles through the new shared lemmas.

## U08 — Strict product for adaptive half-lines

**File:** new `Rigidity/TiltedHalfLineProduct.lean`.

**Acceptance theorem:** `centeredTiltedHalfLine_product_lt_of_ne_one`.

**Dependencies:** U01, U03, U04, U05, and the completed `lowerOrthant_ge_iid`.

**Subtasks:**

- promote only `fixedAverageFactor`, `sumDifferenceProduct`, `integral_fixedAverageFactor_eq_normalizedSelfConvolution`, and one packaged rotation/Fubini identity from `Product/SumDifference.lean`; keep the remaining non-strict proof plumbing private;
- exact fixed-`u` rectangle representation;
- non-strict pointwise comparison for all `u`;
- strict comparison on `E`;
- positivity of `E` from a smaller equal-threshold lower orthant;
- strict integration;
- application of U04 to self-convolved factors;
- normalization cancellation.

## U09 — Strict lower orthants

**File:** new `Orthant/Strict.lean`.

**Acceptance theorem:** `lowerOrthant_gt_iid_of_ne_one`.

**Dependencies:** U06, U07, U08.

**Secondary acceptance:** `lowerOrthant_eq_iid_iff`.

## U10 — Strict stochastic order and MGF

**Files:** new `Maxima/StrictStochasticOrder.lean`, `Maxima/StrictExponentialMoments.lean`.

**Acceptance theorem:** `gaussianMax_mgf_lt_regularSimplex`.

**Secondary acceptance:** `gaussianMax_mgf_eq_regularSimplex_iff`.

**Subtasks:** strict complement calculation, strict layer-cake lemma, equality iff. Any generic strict layer-cake helper must take explicit integrability hypotheses for both exponential transforms at the selected positive parameter; do not hide finiteness in an ellipsis or an unaudited typeclass assumption.

## U11 — Gram rigidity and strict Gaussian-max comparison

**Files:** `Coding/Gram.lean`, `Coding/RegularSimplex.lean`.

**Acceptance theorem:** `gramGaussianMax_mgf_lt_regularSimplex`.

**Secondary acceptance:** `gramNormalization_eq_one_iff` and `gramGaussianMax_mgf_eq_regularSimplex_iff`.

## U12 — Operational uniqueness

**File:** `Coding/WeakSimplex.lean`.

**Acceptance theorem:** `weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders`, the strongest operational equality characterization.

**Prerequisite acceptance:** `bayesValue_eq_regularSimplex_iff`.

**Also add:**

- `weak_simplex_strict`;
- `weak_simplex_eq_iff_codeGram_eq`;
- strict and iff versions for arbitrary measurable score-maximizing decoders.

Every theorem in this package assumes `0 < lam`.

## U13 — Optional geometric congruence

**File:** optional `Coding/Congruence.lean`.

**Goal:** equal regular-simplex Gram matrices imply orthogonal congruence of spanning realizations.

This package is not part of the core definition of done. The Gram matrix is the canonical Lean invariant, and the current repository already specifies a regular simplex through its Gram matrix.

## U14 — Audit, documentation, and release

**Files:** root import, `WeakSimplexConjectureLean/Audit/Axioms.lean`, `scripts/check_axiom_audit.py`, README, theorem-dependency graph, and release notes.

**Acceptance:** full build, exact axiom audit, trusted-source scan, and no production placeholders.

---

## 6. Dependency graph and parallel execution

```text
completed non-strict repository
        │
        ├── U01 regularization ───────────────┐
        ├── U02 PSD rectangles ── U03 strict rectangles ───────┐
        ├── U05 normalized tilted factor ───────────────────────┤
        ├── U06 singular witnesses (after U01) ─────────────┐     │
        └── U07 adaptive reduction refactor ──────────────┤     │
                                                         │     │
U01 + U04 continuous product + U05 + U03 + old orthant ─ U08 strict product
                                                         │
U06 + U07 + U08 ───────────────────────────────────────── U09 strict orthant
                                                         │
U09 ── U10 strict MGF ── U11 Gram rigidity ── U12 decoder uniqueness
                                                         │
                                                         U14 audit/release
```

### Safe parallel waves

- **Wave A:** U01, U02/U03, U05, U06 scratch/API work, and U07 can proceed in separate worktrees.
- **Wave B:** U04 after U01; U06 production after U01 and its compactness spike; U03 completes.
- **Wave C:** U08 integration.
- **Wave D:** U09 and then U10.
- **Wave E:** U11, U12, U14.

One integration owner controls public names, root imports, and any change to an existing theorem statement. Subagents return patches and proof logs; they do not commit or merge autonomously.

---

## 7. Mandatory API spikes before deep proof work

The following should each be tested in a minimal `Scratch/Uniqueness/*.lean` file. Record exact declarations found in the pinned mathlib checkout.

### S1 — Strict integrals

Find or prove a minimal lemma of the form:

```lean
Integrable f μ → Integrable g μ →
(∀ᵐ x ∂μ, f x ≤ g x) →
0 < μ {x | f x < g x} →
∫ x, f x ∂μ < ∫ x, g x ∂μ
```

Fallback: integrate `g-f` and use `setIntegral_pos_iff_support_of_nonneg_ae`, already used in the repository.

### S2 — PSD coordinate Cauchy bound

Search for an existing Cauchy–Schwarz theorem for a positive-semidefinite matrix form. If the API is awkward, use the direct `qform R (a - b e_i) ≥ 0` expansion described above.

### S3 — Compact subsequences in `Coord m`

Freeze the exact theorem chain for:

- closed ball compactness in finite-dimensional Euclidean space;
- `IsCompact.isSeqCompact` or the corresponding subsequence theorem;
- a strict monotone extraction map;
- passing coordinatewise finite sums through `Tendsto`.

### S4 — Real-line probability tails

Locate exact lemmas for

```lean
Tendsto (fun t ↦ μ (Set.Iic t)) atBot (𝓝 0)
Tendsto (fun t ↦ μ (Set.Ici t)) atTop (𝓝 0)
```

for a probability measure. These drive `regressionShiftMass t → 0`.

### S5 — Positive Gaussian interval mass

Find or prove

```lean
0 < gaussianReal 0 1 (Set.Icc (-r) r)
```

from `0 < r`, preferably through strict monotonicity of `normalCDF` or positive density on `Ioo (-r) r`.

### S6 — Piecewise continuity of the self-convolution formula

Prototype the exact formula and boundary simplification at `u = √2 * H s`. Avoid launching a generic convolution-continuity library.

### S7 — Strict layer cake for MGF

Prototype strictness on the level interval `[1,2]` before modifying `Maxima/ExponentialMoments.lean`.

---

## 8. Risk register

| Risk | Severity | Mitigation | Fallback |
|---|---:|---|---|
| Strict ENNReal rectangle step becomes algebraically unwieldy | High | Separate the one-dimensional strict threshold lemma; keep regression geometry out of it. | Convert the bounded probability-valued `q` to a real function with `.toReal`, prove strict covariance there, then translate back. |
| Singular witness subsequence proof becomes dominated by topology API | Medium–high | Spike compact closed-ball subsequences first; use coordinatewise limits, not operator-norm abstractions. | Formalize the manuscript's direct Gram-space endpoint potential, as described in Section 9.1. |
| Continuity of the self-convolved factor is awkward | Medium | Derive the explicit CDF formula and prove piecewise continuity. | Prove only a.e. continuity at a standard Gaussian coordinate and use the explicit single boundary point. |
| Import cycle caused by using `lowerOrthant_ge_iid` to show `μ(E)>0` | Medium | Put the strict product in a new `Rigidity/` module imported only by `Orthant/Strict`; never import rigidity from old orthant files. | Prove positive mass of relative neighborhoods from a Gaussian factor representation. |
| Strict MGF layer-cake conversion is cumbersome | Medium | Work first in `ℝ≥0∞`, show a positive gap over `[1,2]`, then use existing integrability to convert. | Prove strict expectation for the single increasing function `exp (mu * ·)` directly through integration by parts of the CDF. |
| Normalization map has duplicate private definitions | Low–medium | Add one expanded-expression equality iff theorem without refactoring. | Consolidate definitions only after the strict theorem compiles. |
| Accidental uniqueness claim at `lam = 0` | High conceptual | Every strict/iff coding theorem takes `hlam : 0 < lam`; add a regression test for zero signal. | None; the theorem is false at zero. |
| Geometric congruence consumes disproportionate effort | Medium | Make Gram equality the core uniqueness theorem. | Defer U13 to a separate project milestone. |

---

## 9. Fallback architectures

## 9.1 Fallback for singular witnesses: direct Gram-space endpoint potential

Use this only if U06 fails for Lean-engineering reasons after a documented compactness spike.

The fallback follows the manuscript directly:

1. prove `H : ℝ → (0,∞)` is a strict monotone bijection;
2. define the endpoint inverse and
   \[
   \mathcal F(H(s))=\log\Phi(s)+\frac12r(s)^2;
   \]
3. prove `𝓕' = r ∘ H⁻¹`, strict concavity, and endpoint limits;
4. choose a Gram factor for
   \[
   G=\frac m{m-1}\left(R-\frac1mJ\right);
   \]
5. formalize the open-domain strictly concave `(q,v)` potential;
6. prove compact superlevels stay away from the boundary;
7. derive stationarity, compatibility, and the value bound.

This fallback is mathematically direct but is expected to be significantly larger than U06.

## 9.2 Fallback for strict rectangles

Do not formalize the Nakamura–Tsuji equality theorem. If the simultaneous induction becomes difficult, a secondary direct route is:

- permute one correlated pair into the first two coordinates;
- prove strictness in dimension two with the same regression-shift argument;
- add remaining coordinates one at a time with the non-strict rectangle step;
- transport rectangle probabilities under coordinate permutations.

This trades the `β=0` induction branch for matrix/measure permutation infrastructure and is not the preferred route.

## 9.3 Optional stronger singular product theorem

If the continuous-factor bridge is already easy, do not broaden it. If later work needs arbitrary bounded log-concave factors at singular covariance, add a separate theorem based on the fact that a nonzero one-dimensional log-concave function is continuous in the interior of its support and has at most two endpoint discontinuities. This is outside the uniqueness critical path.

---

## 10. Trust, validation, and regression requirements

The repository's existing trust policy remains in force.

### 10.1 Build checks after every package

```bash
lake env lean <edited-file>
lake build
python3 scripts/check_axiom_audit.py

grep -RInE '\b(sorry|admit)\b' WeakSimplexConjectureLean
grep -RInE '^[[:space:]]*axiom[[:space:]]' WeakSimplexConjectureLean
grep -RInE '^[[:space:]]*unsafe[[:space:]]' WeakSimplexConjectureLean
```

Use `lake build --wfail` before release if supported by the existing CI invocation.

### 10.2 New axiom-audit entries

At minimum add:

```lean
#print axioms WeakSimplex.symmetricRectangle_ge_iid
#print axioms WeakSimplex.symmetricRectangle_gt_iid_of_ne_one
#print axioms WeakSimplex.symmetricRectangle_eq_iid_iff
#print axioms WeakSimplex.centered_product_of_continuous
#print axioms WeakSimplex.H_pos
#print axioms WeakSimplex.continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine
#print axioms WeakSimplex.exists_adaptiveWitnesses_of_weakSimplexCov
#print axioms WeakSimplex.centeredTiltedHalfLine_product_lt_of_ne_one
#print axioms WeakSimplex.lowerOrthant_gt_iid_of_ne_one
#print axioms WeakSimplex.lowerOrthant_eq_iid_iff
#print axioms WeakSimplex.coordinateMax_tail_lt_iid_of_ne_one
#print axioms WeakSimplex.gaussianMax_mgf_lt_regularSimplex
#print axioms WeakSimplex.gaussianMax_mgf_eq_regularSimplex_iff
#print axioms WeakSimplex.gramNormalization_eq_one_iff
#print axioms WeakSimplex.gramGaussianMax_mgf_lt_regularSimplex
#print axioms WeakSimplex.gramGaussianMax_mgf_eq_regularSimplex_iff
#print axioms WeakSimplex.bayesValue_eq_regularSimplex_iff
#print axioms WeakSimplex.weak_simplex_strict
#print axioms WeakSimplex.weak_simplex_eq_iff_codeGram_eq
#print axioms WeakSimplex.weak_simplex_strict_of_scoreMaximizingDecoders
#print axioms WeakSimplex.weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders
```

Accepted output remains exactly the standard `[propext, Classical.choice, Quot.sound]` set used by the current project.

### 10.3 Mathematical regression checks

Although numerical tests are not proof dependencies, retain small external sanity checks for:

- a singular admissible covariance such as the rank-one all-ones covariance when admissible in the selected dimension;
- a nonidentity positive-definite admissible covariance;
- strict rectangle probabilities for random radii;
- strict lower-orthant comparison at negative, zero, and positive thresholds;
- strict MGF comparison for several positive parameters;
- equality for `R=I` and for `G=regularSimplexGram`;
- non-uniqueness at `lam=0`.

Do not use `native_decide` or numerical computation inside trusted analytic proofs.

### 10.4 Existing theorem regression

The statements and behavior of the following must remain unchanged:

```lean
centered_product_of_posDef
exists_adaptiveWitnesses
lowerOrthant_ge_iid_of_posDef
lowerOrthant_ge_iid
coordinateMax_tail_le_iid
gaussianMax_mgf_le_regularSimplex
gramGaussianMax_mgf_le_regularSimplex
weak_simplex
weak_simplex_of_scoreMaximizingDecoders
```

The strict theorems are additions, not replacements.

---

## 11. Definition of done

The uniqueness extension is complete only when all of the following hold.

1. For every admissible `R ≠ I` and every real threshold `c`, Lean proves strict lower-orthant comparison.
2. Lean proves equality at one finite threshold if and only if `R = I`.
3. For every `mu > 0`, Lean proves strict normalized Gaussian-maximum MGF comparison away from `I`.
4. For every correlation Gram matrix `G` and `lam > 0`, Lean proves strict MGF comparison away from `regularSimplexGram m`.
5. For unit codebooks and `lam > 0`, Lean proves equality in Bayes/ML success if and only if the code Gram matrix is `regularSimplexGram`.
6. The arbitrary measurable score-maximizing tie-breaking theorem has the same equality characterization.
7. The old non-strict public API still builds unchanged.
8. No production source contains `sorry`, `admit`, a project axiom, `unsafe`, or `native_decide`.
9. Every new public theorem has an accepted transitive axiom report.
10. README and theorem-dependency documentation state explicitly that uniqueness requires positive signal strength and is certified at the Gram-matrix level.

Orthogonal-congruence and mean-width equality theorems are valuable follow-ups but are not required for this core milestone.

---

## 12. Execution directive for implementation agents

Use the following as the run-level instruction.

> Extend the completed repository at baseline commit `b86317606e04b8956611b7dacbf822112b97ea66` according to this uniqueness plan. Do not rewrite the completed non-strict formalization. Preserve every existing public theorem statement. Work one package at a time, with one acceptance theorem per package. Use Lean LSP and the pinned mathlib source before inventing helpers. Prototype uncertain topology, ENNReal strict-integral, matrix-PSD, and piecewise-continuity APIs in `Scratch/`. Do not formalize Nakamura–Tsuji, the full centered-product equality theory, or the endpoint/Gram-space variational problem unless the compact singular-witness package is demonstrably blocked and the fallback is explicitly approved. Never claim uniqueness at `lam = 0`. The core endpoint is the operational equality theorem characterized by `codeGram code = regularSimplexGram`; geometric congruence is optional. After every package, compile the edited file, run the full build, update the axiom audit, and report exact blockers with a minimal reproducer rather than weakening a theorem.

---

## Appendix A. Compact singular-witness derivation in theorem-proof form

This appendix is included because it is the main departure from the manuscript and should be reviewed before implementation.

> **Lemma.** Let `R` be an admissible weak-simplex covariance and `c ∈ ℝ`. If every positive-definite regularization `R_n` has an `AdaptiveWitnesses R_n c`, then `AdaptiveWitnesses R c` is nonempty.

**Proof outline.** Put `L=m log Φ(c)<0`. For witnesses `(s_n,a_n)`, use `a_n=r(s_n)` to rewrite the value field as

\[
L\le
\sum_i\operatorname{localLogMass}(s_{n,i})
-\frac12qform(R_n,a_n).
\]

All local-log-mass terms are negative and the quadratic form is nonnegative. Hence

\[
qform(R_n,a_n)\le-2L
\]

and, for every `i`,

\[
L\le\operatorname{localLogMass}(s_{n,i}).
\]

The second inequality and the `atBot` limit give a uniform lower bound on `s_{n,i}`. Positive-semidefinite Cauchy–Schwarz with unit diagonal gives

\[
|(R_na_n)_i|^2\le qform(R_n,a_n)\le-2L.
\]

Compatibility gives

\[
s_{n,i}=c+(R_na_n)_i-a_{n,i}<c+\sqrt{-2L},
\]

so `s_n` lies in one compact box. Choose a convergent subsequence `s_{n_k}→s`. Continuity gives `a_{n_k}=r(s_{n_k})→a=r(s)`, while `R_{n_k}→R`. Passing to the limit in compatibility and in the continuous value expression produces all fields of `AdaptiveWitnesses R c`. Positivity of the limiting tilt is supplied directly by `r_pos`, not by a limit of strict inequalities. ∎

No uniqueness of the positive-definite variational maximizer is used.

---

## Appendix B. Core rigidity dependency DAG

```text
Product/SymmetricRectangle
  symmetricRectangle_ge_iid
  symmetricRectangle_gt_iid_of_ne_one
            │
            ├────────────────────────────────────┐
            │                                    │
Gaussian/Regularization                          │
  regularized covariance/coupling                │
            │                                    │
            ├── Product/ContinuousCenteredProduct│
            │       centered_product_of_continuous
            │                                    │
Normal/TiltFunctions ─ Tilt/NormalizedTiltedHalfLine
  H_pos                    continuous D h
            │                                    │
            └──────────── Rigidity/TiltedHalfLineProduct
                              strict adaptive product
                                         │
Tilt/SingularWitnesses ─ Orthant/AdaptiveReduction
          │                              │
          └────────────── Orthant/Strict
                           strict lower orthant
                                  │
                   Maxima/StrictExponentialMoments
                                  │
                      Coding/RegularSimplex
                                  │
                       Coding/WeakSimplex
                   equality iff regular Gram
```
