/-
Scratch adaptation and mixed-license notice.
Upstream repository: https://github.com/StatLean/Stat-Lean
Upstream commit: 31c61ed887bf3be0def314a3b3e5375d203b5ba1
Upstream paths:
  StatLean/AsymptoticStatistics/ForMathlib/PiWithDensity.lean;
  StatLean/AsymptoticStatistics/ForMathlib/PiGaussian.lean
    (`pi_gaussianReal_eq_withDensity`); and
  StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean, lines 197-213
    (`Measure.withDensity_map_eq_map_withDensity`)
License: copied StatLean portions remain Apache-2.0; see StatLean/LICENSE. The project-authored
`WP01Density` additions are MIT-licensed under the repository-root LICENSE.
Apart from this notice, local changes replaced upstream imports with eight direct Mathlib imports,
inlined the provider declarations, omitted upstream prose comments around the two selected
declarations, added the project-local density-ratio declarations, and added two top-level axiom
prints. Copied declaration statements and proof bodies are unchanged.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Multivariate

noncomputable section

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

open ProbabilityTheory

namespace AsymptoticStatistics

variable {ι : Type*} [Fintype ι]

lemma pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1)
      = (volume : Measure (ι → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  have h_each : (fun _ : ι => gaussianReal 0 1)
      = fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    funext _
    exact gaussianReal_of_var_ne_zero 0 one_ne_zero
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]
    infer_instance
  rw [h_each, ← MeasureTheory.pi_withDensity_prod
    (fun _ : ι => measurable_gaussianPDF 0 1)]
  rfl

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

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProduct InnerProductSpace MatrixOrder

namespace WP01Density

variable {ι : Type*} [Fintype ι]

def stdDensity (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

lemma measurable_stdDensity : Measurable (stdDensity (ι := ι)) := by
  unfold stdDensity
  fun_prop

lemma stdDensity_ne_zero (x : EuclideanSpace ℝ ι) : stdDensity x ≠ 0 := by
  unfold stdDensity
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact (gaussianPDF_pos 0 one_ne_zero (x i)).ne'

lemma stdDensity_ne_top (x : EuclideanSpace ℝ ι) : stdDensity x ≠ ∞ := by
  exact ENNReal.prod_ne_top fun _ _ ↦ gaussianPDF_ne_top

lemma toReal_stdDensity (x : EuclideanSpace ℝ ι) :
    (stdDensity x).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        Real.exp (-‖x‖ ^ 2 / 2) := by
  rw [stdDensity, ENNReal.toReal_prod]
  simp_rw [toReal_gaussianPDF, gaussianPDFReal]
  rw [Finset.prod_mul_distrib]
  simp_rw [← Real.exp_sum]
  rw [EuclideanSpace.real_norm_sq_eq]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  simp only [NNReal.coe_one, mul_one, Nat.ofNat_nonneg, Real.sqrt_mul, mul_inv_rev,
    Finset.prod_const, Finset.card_univ, sub_zero, mul_eq_mul_left_iff, Real.exp_eq_exp,
    pow_eq_zero_iff', mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    or_false, ne_eq, hsqrt, false_and]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma stdDensity_div_eq_exp_norm (x y : EuclideanSpace ℝ ι) :
    stdDensity y / stdDensity x =
      ENNReal.ofReal (Real.exp (-(‖y‖ ^ 2 - ‖x‖ ^ 2) / 2)) := by
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (stdDensity_ne_top y) (stdDensity_ne_zero x))
    ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_div, toReal_stdDensity, toReal_stdDensity,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι ≠ 0 := by
    apply pow_ne_zero
    exact inv_ne_zero (Real.sqrt_pos.2 (mul_pos zero_lt_two Real.pi_pos)).ne'
  field_simp [hc, Real.exp_ne_zero]
  rw [← Real.exp_add]
  congr 1
  ring

lemma stdGaussian_eq_volume_withDensity :
    stdGaussian (EuclideanSpace ℝ ι) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity stdDensity := by
  rw [← map_pi_eq_stdGaussian, AsymptoticStatistics.pi_gaussianReal_eq_withDensity]
  have hmap := AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    (volume : Measure (ι → ℝ)) (WithLp.toLp 2) (by fun_prop)
    (stdDensity (ι := ι)) measurable_stdDensity
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hmap
  exact hmap.symm.trans (by rfl)

variable [DecidableEq ι]

lemma map_toEuclideanCLM_volume_eq_smul
    {M : Matrix ι ι ℝ} (hM : M.det ≠ 0) :
    Measure.map (Matrix.toEuclideanCLM (𝕜 := ℝ) M)
        (volume : Measure (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (|M.det|⁻¹) • volume := by
  rw [← (PiLp.volume_preserving_toLp ι).map_eq]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      Matrix.toEuclideanCLM (𝕜 := ℝ) M ∘ WithLp.toLp 2 =
        WithLp.toLp 2 ∘ Matrix.toLin' M := by
    funext x
    simp [Function.comp_apply]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hM, Measure.map_smul,
    (PiLp.volume_preserving_toLp ι).map_eq]
  rw [abs_inv]

def sqrtInvDensity (R : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  stdDensity ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)⁻¹) x)

def jacobianFactor (R : Matrix ι ι ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|(CFC.sqrt R).det|⁻¹)

def rawDensityRatio (R : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  jacobianFactor R * sqrtInvDensity R x / stdDensity x

def explicitDensityRatio (R : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt R.det)⁻¹ *
    Real.exp (-(x.ofLp ⬝ᵥ (R⁻¹ - 1).mulVec x.ofLp) / 2))

lemma measurable_sqrtInvDensity (R : Matrix ι ι ℝ) :
    Measurable (sqrtInvDensity R) := by
  exact measurable_stdDensity.comp
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)⁻¹).continuous.measurable

lemma measurable_rawDensityRatio (R : Matrix ι ι ℝ) :
    Measurable (rawDensityRatio R) := by
  exact (measurable_const.mul (measurable_sqrtInvDensity R)).div measurable_stdDensity

lemma det_sqrt_ne_zero {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (CFC.sqrt R).det ≠ 0 := by
  rw [hR.posSemidef.det_sqrt]
  simpa using (Real.sqrt_pos.2 hR.det_pos).ne'

lemma jacobianFactor_eq_det {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    jacobianFactor R = ENNReal.ofReal (Real.sqrt R.det)⁻¹ := by
  rw [jacobianFactor, hR.posSemidef.det_sqrt]
  simp [abs_of_pos (Real.sqrt_pos.2 hR.det_pos)]

/-- The square-root transport has the intended inverse-covariance quadratic form. -/
lemma norm_sqrt_inv_sq_eq_qform {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : EuclideanSpace ℝ ι) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)⁻¹) x‖ ^ 2 =
      x.ofLp ⬝ᵥ R⁻¹.mulVec x.ofLp := by
  let B : Matrix ι ι ℝ := CFC.sqrt R
  let A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹
  have hBself : IsSelfAdjoint B := by
    exact (CFC.sqrt_nonneg R).isSelfAdjoint
  have hBinvself : IsSelfAdjoint B⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact hBself.ringInverse
  have hAself : IsSelfAdjoint A := by
    rw [isSelfAdjoint_iff, ← map_star, hBinvself.star_eq]
  have hAadj : A† = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hAself.star_eq
  have hsqrt : B * B = R := by
    change (CFC.sqrt R) * (CFC.sqrt R) = R
    simpa [pow_two] using (CFC.sq_sqrt R)
  have hAA : A† ∘L A = Matrix.toEuclideanCLM (𝕜 := ℝ) R⁻¹ := by
    rw [hAadj]
    change A * A = _
    change Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ *
        Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹ = _
    rw [← map_mul, ← Matrix.mul_inv_rev, hsqrt]
  change ‖A x‖ ^ 2 = _
  rw [A.apply_norm_sq_eq_inner_adjoint_right x, hAA]
  exact Matrix.inner_toEuclideanCLM R⁻¹ x x

lemma qform_inv_sub_one {R : Matrix ι ι ℝ} (x : EuclideanSpace ℝ ι) :
    x.ofLp ⬝ᵥ (R⁻¹ - 1).mulVec x.ofLp =
      x.ofLp ⬝ᵥ R⁻¹.mulVec x.ofLp - ‖x‖ ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

lemma rawDensityRatio_eq_explicit {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : EuclideanSpace ℝ ι) :
    rawDensityRatio R x = explicitDensityRatio R x := by
  rw [rawDensityRatio, mul_div_assoc, jacobianFactor_eq_det hR,
    sqrtInvDensity, stdDensity_div_eq_exp_norm, norm_sqrt_inv_sq_eq_qform hR,
    ← qform_inv_sub_one (R := R) x, explicitDensityRatio]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg R.det))]

lemma multivariateGaussian_eq_smul_volume_withDensity
    {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    multivariateGaussian 0 R =
      jacobianFactor R •
        (volume : Measure (EuclideanSpace ℝ ι)).withDensity (sqrtInvDensity R) := by
  let B : Matrix ι ι ℝ := CFC.sqrt R
  let A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) B
  have hBdet : B.det ≠ 0 := by
    simpa [B] using det_sqrt_ne_zero hR
  have hBunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBA (x : EuclideanSpace ℝ ι) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹) (A x) = x := by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) B⁻¹)
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) B) x) = x
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      Matrix.nonsing_inv_mul B hBunit, map_one]
    rfl
  have hcomp :
      sqrtInvDensity R ∘ A = stdDensity := by
    funext x
    simp [sqrtInvDensity, Function.comp_apply, A, B, hBA]
  have hmap := AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    (volume : Measure (EuclideanSpace ℝ ι)) A A.continuous.measurable
    (sqrtInvDensity R) (measurable_sqrtInvDensity R)
  have htransport :
      Measure.map A
          ((volume : Measure (EuclideanSpace ℝ ι)).withDensity stdDensity) =
        (Measure.map A volume).withDensity (sqrtInvDensity R) := by
    simpa [hcomp] using hmap.symm
  rw [multivariateGaussian, stdGaussian_eq_volume_withDensity]
  simp only [zero_add]
  change Measure.map A
      ((volume : Measure (EuclideanSpace ℝ ι)).withDensity stdDensity) = _
  rw [htransport, map_toEuclideanCLM_volume_eq_smul hBdet,
    MeasureTheory.withDensity_smul_measure]
  rfl

theorem multivariateGaussian_eq_stdGaussian_withDensity_raw
    {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity (rawDensityRatio R) =
      multivariateGaussian 0 R := by
  rw [stdGaussian_eq_volume_withDensity,
    ← MeasureTheory.withDensity_mul (volume : Measure (EuclideanSpace ℝ ι))
      measurable_stdDensity (measurable_rawDensityRatio R)]
  have hdensity :
      stdDensity * rawDensityRatio R = jacobianFactor R • sqrtInvDensity R := by
    funext x
    change stdDensity x *
      (jacobianFactor R * sqrtInvDensity R x / stdDensity x) =
        jacobianFactor R * sqrtInvDensity R x
    rw [mul_comm, ENNReal.div_mul_cancel (stdDensity_ne_zero x) (stdDensity_ne_top x)]
  rw [hdensity, MeasureTheory.withDensity_smul'
    (jacobianFactor R) (sqrtInvDensity R) ENNReal.ofReal_ne_top]
  exact (multivariateGaussian_eq_smul_volume_withDensity hR).symm

theorem multivariateGaussian_eq_stdGaussian_withDensity_explicit
    {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun x ↦ ENNReal.ofReal ((Real.sqrt R.det)⁻¹ *
          Real.exp (-(x.ofLp ⬝ᵥ (R⁻¹ - 1).mulVec x.ofLp) / 2))) =
      multivariateGaussian 0 R := by
  change (stdGaussian (EuclideanSpace ℝ ι)).withDensity (explicitDensityRatio R) = _
  have hfun : explicitDensityRatio R = rawDensityRatio R := by
    funext x
    exact (rawDensityRatio_eq_explicit hR x).symm
  rw [hfun]
  exact multivariateGaussian_eq_stdGaussian_withDensity_raw hR

#print axioms WP01Density.multivariateGaussian_eq_stdGaussian_withDensity_raw
#print axioms WP01Density.multivariateGaussian_eq_stdGaussian_withDensity_explicit

end WP01Density
