/-
Scratch adaptation notice.
Upstream repository: https://github.com/StatLean/Stat-Lean
Upstream commit: 31c61ed887bf3be0def314a3b3e5375d203b5ba1
Upstream paths:
  StatLean/AsymptoticStatistics/ForMathlib/PiWithDensity.lean;
  StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean, lines 197-213; and
  StatLean/AsymptoticStatistics/ForMathlib/GaussianMGF.lean, lines 396-618
License: Apache-2.0; see StatLean/LICENSE.
Apart from this notice, local changes replaced StatLean imports with ten direct Mathlib imports,
inlined the two local providers, restored the enclosing namespaces, and added the top-level axiom
print. Copied theorem statements and proof bodies are unchanged.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map


/-!
# Pi measure under withDensity

A pi-measure tilted by a product density decomposes componentwise into the product
of individually-tilted measures:
```
(Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  = Measure.pi (fun i => (μ i).withDensity (f i))
```

Middle brick in the multivariate Girsanov chain used by Theorem 7.10 `hTilt`: given
the 1D Girsanov identity `(gaussianReal 0 1).withDensity (exp-shift) = gaussianReal a 1`
and `map_pi_eq_stdGaussian`, this theorem promotes it from 1D to finite products.

The proof goes through an ENNReal version of
`MeasureTheory.integral_fintype_prod_eq_prod`, which Mathlib (at `v4.29.1`) only has
for the Bochner integral. We derive the ENNReal analogue by induction on `Fin n`
using `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`, then lift to a
general `Fintype` via `measurePreserving_piCongrLeft`, and finally apply
`Measure.pi_eq` on rectangles.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

section LintegralProd

variable {ι : Type*} [Fintype ι]

/-- **ENNReal Fubini on `Fin n`**: the `lintegral` of a product of per-coordinate
functions over `Measure.pi μ` factors as a product of per-coordinate lintegrals.

ENNReal analogue of `MeasureTheory.integral_fin_nat_prod_eq_prod`. Proved by induction
on `n` using `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : Fin n) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have mp := measurePreserving_piFinSuccAbove μ 0
      have h_prod_meas : Measurable fun x : (i : Fin (n + 1)) → E i => ∏ i, f i (x i) :=
        Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
      have hf0_ae : AEMeasurable (f 0) (μ 0) := (hf 0).aemeasurable
      have h_tail_ae :
          AEMeasurable (fun y : (i : Fin n) → E i.succ => ∏ i, f i.succ (y i))
            (Measure.pi (fun i => μ i.succ)) :=
        (Finset.measurable_prod _ (fun i _ =>
          (hf _).comp (measurable_pi_apply i))).aemeasurable
      have ih' : ∫⁻ y : (i : Fin n) → E i.succ, ∏ i, f i.succ (y i)
                   ∂Measure.pi (fun i : Fin n => μ i.succ)
                 = ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ :=
        ih (E := fun i : Fin n => E i.succ) (μ := fun i : Fin n => μ i.succ)
           (f := fun i : Fin n => f i.succ) (fun i => hf _)
      calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ z : E 0 × ((i : Fin n) → E i.succ),
              f 0 z.1 * ∏ i, f i.succ (z.2 i)
              ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
            rw [← mp.symm.lintegral_comp h_prod_meas]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
            rfl
        _ = (∫⁻ x, f 0 x ∂μ 0)
              * ∫⁻ y : (i : Fin n) → E i.succ,
                  (∏ i : Fin n, f i.succ (y i)) ∂Measure.pi (fun i : Fin n => μ i.succ) :=
            lintegral_prod_mul hf0_ae h_tail_ae
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by rw [ih']
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
            rw [← Fin.prod_univ_succ (fun i : Fin (n + 1) => ∫⁻ x, f i x ∂μ i)]

/-- **ENNReal Fubini on a general `Fintype`**: same factorisation as
`lintegral_fin_nat_prod_eq_prod`, but with variables indexed by any finite type.
Lifts the `Fin n` case through `measurePreserving_piCongrLeft`. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : ι) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have mp := measurePreserving_piCongrLeft (fun i => μ i) e
  have h_meas : Measurable fun x : (i : ι) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  rw [← mp.lintegral_comp h_meas]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => hf _)

end LintegralProd

section PiWithDensity

variable {ι : Type*} [Fintype ι]

/-- **Pi measure tilted by a product density**. A product of per-coordinate densities
applied to the product measure equals the product of per-coordinate tilted measures:
```
(Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  = Measure.pi (fun i => (μ i).withDensity (f i))
```

Proof: compare both sides on rectangles using `Measure.pi_eq`. On a rectangle
`Set.univ.pi s`, the left side becomes `∫⁻ x in pi s, ∏ f i (x i) ∂pi μ`, and the
rectangle indicator factors as a product of indicators; `lintegral_fintype_prod_eq_prod`
then splits the integral into `∏ i, ∫⁻ (s i).indicator (f i)`, each of which is
`(μ i).withDensity (f i) (s i)` by `withDensity_apply`.

Second step of the multivariate Girsanov chain (Theorem 7.10 `hTilt`); combines with
`gaussianReal_withDensity_exp_shift` and `map_pi_eq_stdGaussian` to give the standard
multivariate Gaussian Girsanov identity on `EuclideanSpace ℝ (Fin k)`. -/
theorem pi_withDensity_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : ι) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
      = Measure.pi (fun i => (μ i).withDensity (f i)) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) fun s hs => ?_).symm
  -- LHS on the rectangle `∏ᵢ sᵢ`.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  -- Rewrite indicator of a rectangle as a product of indicators.
  have h_indic : ∀ x : (i : ι) → E i,
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
        = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hx i (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_univ_pi] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  simp_rw [h_indic]
  -- Apply the ENNReal Fubini factorisation.
  rw [lintegral_fintype_prod_eq_prod (fun i => (hf i).indicator (hs i))]
  -- Reassemble each factor as `(μ i).withDensity (f i) (s i)`.
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

end PiWithDensity

end MeasureTheory

namespace AsymptoticStatistics

/-- **Commuting `withDensity` past `Measure.map`**:
`(μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ`, for measurable `φ` and `h`.

Useful for pushing a density through a measurable pushforward — e.g., when a joint
law `π_tilted = π.map φ` is `withDensity`-ed against a function `h` that factors
through `φ`, the calculation can be pulled back to `π` under the composed density. -/
lemma Measure.withDensity_map_eq_map_withDensity
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : MeasureTheory.Measure α) (φ : α → β) (hφ : Measurable φ)
    (h : β → ℝ≥0∞) (hh : Measurable h) :
    (μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.withDensity_apply _ hA,
      MeasureTheory.Measure.map_apply hφ hA,
      MeasureTheory.withDensity_apply _ (hφ hA),
      MeasureTheory.setLIntegral_map hA hh hφ]
  rfl

end AsymptoticStatistics

open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder ENNReal

namespace ProbabilityTheory

/-- **Girsanov / Esscher identity for 1D standard Gaussian**. Tilting
`gaussianReal 0 1` by the exponential density `exp(a · x - a² / 2)` produces
`gaussianReal a 1` — i.e., shifts the mean by `a`.

Proof by PDF comparison: both sides rewrite to `volume.withDensity f` via
`gaussianReal_of_var_ne_zero`, then `withDensity_mul` composes the 0-mean PDF
with the exponential tilt, and the resulting density matches the `a`-mean PDF
because `exp(-(x-a)²/2) = exp(-x²/2) · exp(a·x - a²/2)`.

First step of the Girsanov chain for the Theorem 7.10 `hTilt` provider; lifts
to the multivariate case via the product-measure representation of `stdGaussian`. -/
lemma gaussianReal_withDensity_exp_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  -- Both `gaussianReal`s admit an explicit `volume.withDensity gaussianPDF` form
  -- (since `v = 1 ≠ 0`), turning the identity into a density-side comparison.
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0)]
  have h_tilt_meas :
      Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))) := by
    fun_prop
  rw [← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) h_tilt_meas]
  congr 1
  ext x
  -- Pointwise identity on densities. Move ENNReal.ofReal out and reduce to real algebra.
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  -- Real identity: `gaussianPDFReal 0 1 x · exp(a·x - a²/2) = gaussianPDFReal a 1 x`.
  -- Expand the PDFs and collapse `exp(-x²/2) · exp(a·x - a²/2) = exp(-(x-a)²/2)`.
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Pi-product Girsanov for standard 1D Gaussians**. Tilting the product of `ι`
copies of `gaussianReal 0 1` by `exp(∑ᵢ aᵢ yᵢ - ∑ᵢ aᵢ² / 2)` shifts the mean in each
coordinate:
```
(Measure.pi (fun _ => gaussianReal 0 1)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
  = Measure.pi (fun i => gaussianReal (a i) 1).
```

Proof goes through `pi_withDensity_prod`: the exponential density factors as a
product `∏ i, exp(aᵢ yᵢ - aᵢ² / 2)`, each factor is the 1D Girsanov density, and
`gaussianReal_withDensity_exp_shift` shifts each component individually.

Second step of the multivariate Girsanov chain (`hTilt` for Theorem 7.10). -/
lemma pi_gaussianReal_withDensity_exp_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  -- Record the 1D Girsanov identity on each coordinate; this gives the
  -- `IsProbabilityMeasure` instance needed for `pi_withDensity_prod`.
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))
        = gaussianReal (a i) 1 := fun i => gaussianReal_withDensity_exp_shift (a i)
  haveI : ∀ i, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  -- Factor the product density: `exp(∑ aᵢyᵢ - ∑ aᵢ²/2) = ∏ exp(aᵢyᵢ - aᵢ²/2)`.
  have h_density : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - a i ^ 2 / 2)) := by
    funext y
    rw [show (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)
          = ∑ i, (a i * y i - a i ^ 2 / 2) from (Finset.sum_sub_distrib _ _).symm,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
        (fun i _ => Real.exp_nonneg _)]
  rw [h_density, pi_withDensity_prod
    (f := fun i x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- **Standard Gaussian Girsanov on `EuclideanSpace ℝ ι`** (Esscher shift). Tilting
the standard Gaussian by `exp(⟪a, y⟫ - ‖a‖² / 2)` shifts the mean by `a`:
```
(stdGaussian (EuclideanSpace ℝ ι)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖² / 2)))
  = (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => y + a).
```

Lifts the pi-version `pi_gaussianReal_withDensity_exp_shift` through the isomorphism
`(Measure.pi …).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ ι)` on both
sides. The LHS commutes withDensity past map (`withDensity_map_eq_map_withDensity`)
and expands `⟪a, toLp y⟫` / `‖a‖²` into coordinate sums. The RHS composes the maps
(`Measure.map_map`), rewrites `+ a` on the Lp side as `+ a.ofLp` on the pi side
(linearity of `WithLp.toLp`), and distributes via `pi_map_pi` + `gaussianReal_map_add_const`. -/
theorem stdGaussian_withDensity_exp_shift {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖ ^ 2 / 2)))
      = (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => y + a) := by
  classical
  -- Each 1D shift is a probability measure; promote for `pi_map_pi`'s SigmaFinite instance.
  haveI : ∀ i,
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun x : ℝ => x + a.ofLp i)) := by
    intro i; rw [gaussianReal_map_add_const]; infer_instance
  -- Pull both sides back to `pi` via `map_pi_eq_stdGaussian`.
  rw [← map_pi_eq_stdGaussian (ι := ι)]
  -- LHS: commute withDensity past map. RHS: compose the two maps.
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _
    (by fun_prop) _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  -- Rewrite RHS function `(· + a) ∘ toLp = toLp ∘ (· + a.ofLp)` by linearity of `toLp`,
  -- then split the composed map back so both sides have `.map (toLp)` outermost.
  have h_add : ((fun y : EuclideanSpace ℝ ι => y + a) ∘ WithLp.toLp 2 (V := ι → ℝ))
      = (WithLp.toLp 2) ∘ fun y : ι → ℝ => y + a.ofLp := by
    funext y
    simp only [Function.comp_apply]
    rw [WithLp.toLp_add, WithLp.toLp_ofLp]
  rw [h_add, ← Measure.map_map (by fun_prop) (by fun_prop)]
  -- Strip the common `.map (toLp 2)` from both sides.
  congr 1
  -- LHS: rewrite the pulled-back density in pi-coord form, then apply pi-Girsanov.
  have h_density : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖ ^ 2 / 2))) ∘ WithLp.toLp 2 (V := ι → ℝ))
      = fun y : ι → ℝ =>
          ENNReal.ofReal (Real.exp (∑ i, a.ofLp i * y i - ∑ i, a.ofLp i ^ 2 / 2)) := by
    funext y
    simp only [Function.comp_apply]
    have h_inner : ⟪a, (WithLp.toLp 2 y : EuclideanSpace ℝ ι)⟫
        = ∑ i, a.ofLp i * y i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change y i * a.ofLp i = a.ofLp i * y i
      ring
    have h_norm : (‖a‖ : ℝ) ^ 2 / 2 = (∑ i, a.ofLp i ^ 2) / 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [h_inner, h_norm, Finset.sum_div]
  rw [h_density, pi_gaussianReal_withDensity_exp_shift (fun i => a.ofLp i)]
  -- RHS: distribute the coordinate-wise shift through `pi_map_pi`.
  rw [show (fun y : ι → ℝ => y + a.ofLp) = (fun y i => y i + a.ofLp i) from rfl,
    Measure.pi_map_pi (fun i =>
      (by fun_prop : Measurable (fun x : ℝ => x + a.ofLp i)).aemeasurable)]
  simp_rw [gaussianReal_map_add_const, zero_add]

/-- **Multivariate Gaussian Girsanov / Esscher identity**. Tilting the centred
multivariate Gaussian `N(0, S)` by `exp(⟪h, y⟫ - ⟨h, S h⟩ / 2)` shifts the mean to
`S h`:
```
(multivariateGaussian 0 S).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)))
  = multivariateGaussian (toEuclideanCLM S h) S.
```

Lifts the `stdGaussian` version `stdGaussian_withDensity_exp_shift` through the
square-root decomposition `multivariateGaussian μ S = stdGaussian.map (μ + √S ·)`.

Let `A = toEuclideanCLM (sqrt S)`; by CFC, `A ∘ A = toEuclideanCLM S`, and since
`sqrt S ≥ 0`, `A` is self-adjoint. The LHS density composed with `A` simplifies:
`⟪h, A x⟫ = ⟪A h, x⟫` (self-adjoint) and `⟨h, S h⟩ = ‖A h‖²` (`A ∘ A = S`),
so `(tilt h) ∘ A = tilt_std (A h)`. Applying the `stdGaussian` shift at parameter
`A h` produces `stdGaussian.map (· + A h)`, and composing with `A` on the outside
yields `stdGaussian.map (fun x => A x + A (A h)) = stdGaussian.map (fun x =>
toEuclideanCLM S h + A x)`, which is `multivariateGaussian (toEuclideanCLM S h) S`
by definition. -/
theorem multivariateGaussian_withDensity_exp_shift {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (h : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S).withDensity
        (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫
          - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)))
      = multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) S h) S := by
  classical
  -- Abbreviation `A := toEuclideanCLM (sqrt S)` : self-adjoint, `A ∘ A = toEuclideanCLM S`.
  set A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA_def
  set_option backward.isDefEq.respectTransparency false in
  have hA_sa : IsSelfAdjoint A :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
  have hAA : A ∘L A = toEuclideanCLM (𝕜 := ℝ) S := by
    change A * A = toEuclideanCLM (𝕜 := ℝ) S
    rw [hA_def, ← map_mul, CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  have hA_meas : Measurable A := A.continuous.measurable
  -- Adjoint-swap helper.
  have h_inner_swap : ∀ u v, ⟪u, A v⟫ = ⟪A u, v⟫ := fun u v => by
    have := ContinuousLinearMap.adjoint_inner_left A v u
    rw [hA_sa.adjoint_eq] at this
    exact this.symm
  -- `A (A h) = toEuclideanCLM S h` from `A ∘L A = toEuclideanCLM S`.
  have hAAh : A (A h) = (toEuclideanCLM (𝕜 := ℝ) S) h := by
    change (A ∘L A) h = _
    rw [hAA]
  -- Unfold `multivariateGaussian 0 S = stdGaussian.map A` (the `0 +` simplifies).
  have hMvG0 : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map A := by
    rw [multivariateGaussian]
    congr 1
    funext x
    simp [hA_def]
  -- Unfold RHS similarly.
  have hMvGSh : multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) S h) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map
          (fun x => toEuclideanCLM (𝕜 := ℝ) S h + A x) := by
    rw [multivariateGaussian]
  rw [hMvG0, hMvGSh]
  -- Commute withDensity past `.map A` on the LHS.
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _ hA_meas _
    (by fun_prop)]
  -- Rewrite the pulled-back density as the stdGaussian-tilt at parameter `A h`.
  have h_density : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2))) ∘ A)
      = fun x => ENNReal.ofReal (Real.exp (⟪A h, x⟫ - ‖A h‖ ^ 2 / 2)) := by
    funext x
    simp only [Function.comp_apply]
    -- Inner-product swap: `⟪h, A x⟫ = ⟪A h, x⟫`.
    have h_inner : ⟪h, A x⟫ = ⟪A h, x⟫ := h_inner_swap h x
    -- `‖A h‖² = h.ofLp ⬝ᵥ S.mulVec h.ofLp`.
    have h_norm_sq : ‖A h‖ ^ 2 = h.ofLp ⬝ᵥ S.mulVec h.ofLp := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, h_inner_swap, hAAh,
        real_inner_comm, Matrix.inner_toEuclideanCLM]
    rw [h_inner, h_norm_sq]
  rw [h_density, stdGaussian_withDensity_exp_shift (A h),
    Measure.map_map hA_meas (by fun_prop)]
  -- Collapse `A ∘ (· + A h) = (toEuclideanCLM S h + ·) ∘ A`.
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [A.map_add, hAAh, add_comm]

#print axioms multivariateGaussian_withDensity_exp_shift

end ProbabilityTheory
