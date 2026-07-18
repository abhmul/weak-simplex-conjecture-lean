import WeakSimplexConjectureLean.Core.Matrix
import WeakSimplexConjectureLean.Vendor.StatLean.PiGaussian
import WeakSimplexConjectureLean.Vendor.StatLean.WithDensityMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProduct InnerProductSpace MatrixOrder

namespace WeakSimplex

variable {ι : Type*} [Fintype ι]

private def stdDensity (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

private lemma measurable_stdDensity : Measurable (stdDensity (ι := ι)) := by
  unfold stdDensity
  fun_prop

private lemma stdDensity_ne_zero (x : EuclideanSpace ℝ ι) : stdDensity x ≠ 0 := by
  unfold stdDensity
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact (gaussianPDF_pos 0 one_ne_zero (x i)).ne'

private lemma stdDensity_ne_top (x : EuclideanSpace ℝ ι) : stdDensity x ≠ ∞ := by
  exact ENNReal.prod_ne_top fun _ _ ↦ gaussianPDF_ne_top

private lemma toReal_stdDensity (x : EuclideanSpace ℝ ι) :
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

private lemma stdDensity_div_eq_exp_norm (x y : EuclideanSpace ℝ ι) :
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

private lemma stdGaussian_eq_volume_withDensity :
    stdGaussian (EuclideanSpace ℝ ι) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity stdDensity := by
  rw [← map_pi_eq_stdGaussian, Vendor.StatLean.AsymptoticStatistics.pi_gaussianReal_eq_withDensity]
  have hmap := Vendor.StatLean.AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    (volume : Measure (ι → ℝ)) (WithLp.toLp 2) (by fun_prop)
    (stdDensity (ι := ι)) measurable_stdDensity
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hmap
  exact hmap.symm.trans (by rfl)

variable [DecidableEq ι]

private lemma map_toEuclideanCLM_volume_eq_smul
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

private def sqrtInvDensity (R : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  stdDensity ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)⁻¹) x)

private def jacobianFactor (R : Matrix ι ι ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|(CFC.sqrt R).det|⁻¹)

private def rawDensityRatio (R : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  jacobianFactor R * sqrtInvDensity R x / stdDensity x

private def explicitDensityRatio (R : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt R.det)⁻¹ *
    Real.exp (-(x.ofLp ⬝ᵥ (R⁻¹ - 1).mulVec x.ofLp) / 2))

private lemma measurable_sqrtInvDensity (R : Matrix ι ι ℝ) :
    Measurable (sqrtInvDensity R) := by
  exact measurable_stdDensity.comp
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)⁻¹).continuous.measurable

private lemma measurable_rawDensityRatio (R : Matrix ι ι ℝ) :
    Measurable (rawDensityRatio R) := by
  exact (measurable_const.mul (measurable_sqrtInvDensity R)).div measurable_stdDensity

private lemma det_sqrt_ne_zero {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (CFC.sqrt R).det ≠ 0 := by
  rw [hR.posSemidef.det_sqrt]
  simpa using (Real.sqrt_pos.2 hR.det_pos).ne'

private lemma jacobianFactor_eq_det {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    jacobianFactor R = ENNReal.ofReal (Real.sqrt R.det)⁻¹ := by
  rw [jacobianFactor, hR.posSemidef.det_sqrt]
  simp [abs_of_pos (Real.sqrt_pos.2 hR.det_pos)]

/-- The square-root transport has the intended inverse-covariance quadratic form. -/
private lemma norm_sqrt_inv_sq_eq_qform {R : Matrix ι ι ℝ} (hR : R.PosDef)
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

private lemma qform_inv_sub_one {R : Matrix ι ι ℝ} (x : EuclideanSpace ℝ ι) :
    x.ofLp ⬝ᵥ (R⁻¹ - 1).mulVec x.ofLp =
      x.ofLp ⬝ᵥ R⁻¹.mulVec x.ofLp - ‖x‖ ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

private lemma rawDensityRatio_eq_explicit {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : EuclideanSpace ℝ ι) :
    rawDensityRatio R x = explicitDensityRatio R x := by
  rw [rawDensityRatio, mul_div_assoc, jacobianFactor_eq_det hR,
    sqrtInvDensity, stdDensity_div_eq_exp_norm, norm_sqrt_inv_sq_eq_qform hR,
    ← qform_inv_sub_one (R := R) x, explicitDensityRatio]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg R.det))]

private lemma multivariateGaussian_eq_smul_volume_withDensity
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
  have hmap := Vendor.StatLean.AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
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

private theorem multivariateGaussian_eq_stdGaussian_withDensity_raw
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

private theorem multivariateGaussian_eq_stdGaussian_withDensity_explicit
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

section Public

variable {m : ℕ}

/-- The positive-definite Gaussian density ratio relative to product standard Gaussian. -/
def gaussianDensityRatio (R : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) : ℝ :=
  (Real.sqrt R.det)⁻¹ * Real.exp (-(qform (R⁻¹ - 1) x) / 2)

private lemma continuous_gaussianDensityRatio (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (gaussianDensityRatio R) := by
  unfold gaussianDensityRatio qform matrixMul
  fun_prop

private lemma gaussianDensityRatio_pos {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef) (x : Coord m) :
    0 < gaussianDensityRatio R x := by
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.2 hR.det_pos)) (Real.exp_pos _)

/-- A positive-definite centered Gaussian has the displayed density relative to product standard
Gaussian measure. -/
theorem multivariateGaussian_eq_stdGaussian_withDensity
    {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) :
    multivariateGaussian 0 R =
      (stdGaussian (Coord m)).withDensity
        (fun x ↦ ENNReal.ofReal (gaussianDensityRatio R x)) := by
  symm
  simpa only [gaussianDensityRatio, qform_eq_dotProduct, Coord.toFun] using
    multivariateGaussian_eq_stdGaussian_withDensity_explicit hR

private def coordinateBox (L : ℝ) : Set (Coord m) :=
  {x | ∀ i, x i ∈ Set.Icc (-L) L}

private lemma isCompact_coordinateBox (L : ℝ) :
    IsCompact (coordinateBox (m := m) L) := by
  let e : Coord m ≃ₜ (Fin m → ℝ) := PiLp.homeomorph 2 (fun _ : Fin m ↦ ℝ)
  have hfun : IsCompact (Set.univ.pi fun _ : Fin m ↦ Set.Icc (-L) L) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hset : coordinateBox (m := m) L =
      e ⁻¹' (Set.univ.pi fun _ : Fin m ↦ Set.Icc (-L) L) := by
    ext x
    simp [coordinateBox, e, PiLp.homeomorph, WithLp.equiv, Pi.le_def, forall_and]
  rw [hset]
  exact e.isCompact_preimage.mpr hfun

private lemma measurableSet_coordinateBox (L : ℝ) :
    MeasurableSet (coordinateBox (m := m) L) := by
  rw [coordinateBox, Set.setOf_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

private theorem lintegral_coordinateBox_product_eq_prod
    (f : Fin m → ℝ → ℝ) (hf_meas : ∀ i, Measurable (f i)) (L : ℝ) :
    (∫⁻ x in coordinateBox (m := m) L,
        ∏ i, ENNReal.ofReal (f i (x i)) ∂stdGaussian (Coord m)) =
      ∏ i, ∫⁻ z in Set.Icc (-L) L,
        ENNReal.ofReal (f i z) ∂gaussianReal 0 1 := by
  let G : Coord m → ℝ≥0∞ := fun x ↦ ∏ i, ENNReal.ofReal (f i (x i))
  have hG : Measurable G := by
    apply Finset.measurable_prod Finset.univ
    intro i hi
    exact ENNReal.measurable_ofReal.comp
      ((hf_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable)
  rw [← map_pi_eq_stdGaussian]
  rw [setLIntegral_map (measurableSet_coordinateBox L) hG (by fun_prop)]
  have hpre : (WithLp.toLp 2) ⁻¹' coordinateBox (m := m) L =
      Set.univ.pi fun _ : Fin m ↦ Set.Icc (-L) L := by
    ext x
    simp [coordinateBox, Pi.le_def, forall_and]
  rw [hpre, ← lintegral_indicator (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)]
  have hindicator : ∀ x : Fin m → ℝ,
      (Set.univ.pi fun _ : Fin m ↦ Set.Icc (-L) L).indicator
          (fun y ↦ G (WithLp.toLp 2 y)) x =
        ∏ i, (Set.Icc (-L) L).indicator (fun z ↦ ENNReal.ofReal (f i z)) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi fun _ : Fin m ↦ Set.Icc (-L) L
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_univ_pi] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  simp_rw [hindicator]
  have hprod :=
    WeakSimplex.Vendor.StatLean.MeasureTheory.lintegral_fintype_prod_eq_prod
      (μ := fun _ : Fin m ↦ gaussianReal 0 1)
      (f := fun i z ↦
        (Set.Icc (-L) L).indicator (fun y ↦ ENNReal.ofReal (f i y)) z)
      (fun i ↦ (ENNReal.measurable_ofReal.comp (hf_meas i)).indicator measurableSet_Icc)
  simpa only [← lintegral_indicator measurableSet_Icc] using hprod

/-- The positive-definite Gaussian density ratio has a strictly positive uniform lower bound on
every centered coordinate box. -/
theorem exists_pos_le_gaussianDensityRatio_on_box
    {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) (L : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : Coord m, (∀ i, x i ∈ Set.Icc (-L) L) → c ≤ gaussianDensityRatio R x := by
  obtain ⟨c, hc, hle⟩ :=
    (isCompact_coordinateBox (m := m) L).exists_forall_le'
      (continuous_gaussianDensityRatio R).continuousOn
      (fun x _ ↦ gaussianDensityRatio_pos hR x)
  exact ⟨c, hc, fun x hx ↦ hle x hx⟩

private theorem ofReal_mul_prod_setLIntegral_le_lintegral
    {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) (L : ℝ)
    (f : Fin m → ℝ → ℝ) (hf_meas : ∀ i, Measurable (f i))
    {c : ℝ} (hcle : ∀ x : Coord m,
      (∀ i, x i ∈ Set.Icc (-L) L) → c ≤ gaussianDensityRatio R x) :
    ENNReal.ofReal c *
        (∏ i, ∫⁻ z in Set.Icc (-L) L,
          ENNReal.ofReal (f i z) ∂gaussianReal 0 1) ≤
      ∫⁻ x, ∏ i, ENNReal.ofReal (f i (x i))
        ∂multivariateGaussian (0 : Coord m) R := by
  let F : Coord m → ℝ≥0∞ := fun x ↦ ∏ i, ENNReal.ofReal (f i (x i))
  let rho : Coord m → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (gaussianDensityRatio R x)
  have hF : Measurable F := by
    apply Finset.measurable_prod Finset.univ
    intro i hi
    exact ENNReal.measurable_ofReal.comp
      ((hf_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable)
  have hrho : Measurable rho := by
    exact ENNReal.measurable_ofReal.comp (continuous_gaussianDensityRatio R).measurable
  rw [← lintegral_coordinateBox_product_eq_prod f hf_meas L]
  calc
    ENNReal.ofReal c *
          (∫⁻ x in coordinateBox (m := m) L, F x ∂stdGaussian (Coord m)) =
        ∫⁻ x in coordinateBox (m := m) L,
          ENNReal.ofReal c * F x ∂stdGaussian (Coord m) := by
      rw [lintegral_const_mul _ hF]
    _ ≤ ∫⁻ x in coordinateBox (m := m) L,
          rho x * F x ∂stdGaussian (Coord m) := by
      apply setLIntegral_mono (hrho.mul hF)
      intro x hx
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hcle x hx)) (F x)
    _ ≤ ∫⁻ x, rho x * F x ∂stdGaussian (Coord m) :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, F x ∂(stdGaussian (Coord m)).withDensity rho := by
      exact (lintegral_withDensity_eq_lintegral_mul _ hrho hF).symm
    _ = ∫⁻ x, F x ∂multivariateGaussian (0 : Coord m) R := by
      rw [show (stdGaussian (Coord m)).withDensity rho =
          multivariateGaussian (0 : Coord m) R by
        simpa only [rho] using (multivariateGaussian_eq_stdGaussian_withDensity hR).symm]

private theorem exists_norm_bound_of_isBounded_range
    {X : Type*} {f : X → ℝ} (hf : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf
  refine ⟨C, fun x ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self x)

/-- A pointwise lower bound for the Gaussian density ratio on a centered coordinate box gives the
corresponding product-of-truncated-masses lower bound. -/
theorem mul_prod_setIntegral_le_integral_of_le_gaussianDensityRatio_on_box
    {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef) (L : ℝ)
    (f : Fin m → ℝ → ℝ) (hf_meas : ∀ i, Measurable (f i))
    (hf_nonneg : ∀ i x, 0 ≤ f i x)
    (hf_bounded : ∀ i, Bornology.IsBounded (Set.range (f i)))
    {c : ℝ} (hc : 0 ≤ c)
    (hcle : ∀ x : Coord m,
      (∀ i, x i ∈ Set.Icc (-L) L) → c ≤ gaussianDensityRatio R x) :
    c * (∏ i, ∫ z in Set.Icc (-L) L, f i z ∂gaussianReal 0 1) ≤
      ∫ x, ∏ i, f i (x i) ∂multivariateGaussian (0 : Coord m) R := by
  have hfactor_int (i : Fin m) : Integrable (f i) (gaussianReal 0 1) := by
    obtain ⟨C, hC⟩ := exists_norm_bound_of_isBounded_range (hf_bounded i)
    have hint := (integrable_const (1 : ℝ) :
      Integrable (fun _ : ℝ ↦ (1 : ℝ)) (gaussianReal 0 1))
    have hmul := hint.bdd_mul (hf_meas i).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
    simpa using hmul
  choose C hC using fun i ↦ exists_norm_bound_of_isBounded_range (hf_bounded i)
  have hcoord_meas (i : Fin m) : Measurable (fun x : Coord m ↦ f i (x i)) :=
    (hf_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable
  have hcoord_bound (i : Fin m) : ∀ x : Coord m, ‖f i (x i)‖ ≤ C i :=
    fun x ↦ hC i (x i)
  have hproduct_int_finset (s : Finset (Fin m)) :
      Integrable (fun x : Coord m ↦ ∏ i ∈ s, f i (x i))
        (multivariateGaussian (0 : Coord m) R) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
        have hmul := hs.bdd_mul (hcoord_meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall (hcoord_bound i))
        simpa [Finset.prod_insert hi] using hmul
  have hproduct_int :
      Integrable (fun x : Coord m ↦ ∏ i, f i (x i))
        (multivariateGaussian (0 : Coord m) R) := by
    simpa using hproduct_int_finset Finset.univ
  have hproduct_nonneg : ∀ x : Coord m, 0 ≤ ∏ i, f i (x i) :=
    fun x ↦ Finset.prod_nonneg fun i _ ↦ hf_nonneg i (x i)
  have hleft :
      ENNReal.ofReal
          (c * (∏ i, ∫ z in Set.Icc (-L) L, f i z ∂gaussianReal 0 1)) =
        ENNReal.ofReal c *
          (∏ i, ∫⁻ z in Set.Icc (-L) L,
            ENNReal.ofReal (f i z) ∂gaussianReal 0 1) := by
    rw [ENNReal.ofReal_mul hc,
      ENNReal.ofReal_prod_of_nonneg
        (fun i _ ↦ setIntegral_nonneg measurableSet_Icc fun x _ ↦ hf_nonneg i x)]
    apply congrArg (fun t ↦ ENNReal.ofReal c * t)
    apply Finset.prod_congr rfl
    intro i hi
    exact ofReal_integral_eq_lintegral_ofReal (hfactor_int i).integrableOn
      (Filter.Eventually.of_forall (hf_nonneg i))
  have hright :
      ENNReal.ofReal
          (∫ x, ∏ i, f i (x i) ∂multivariateGaussian (0 : Coord m) R) =
        ∫⁻ x, ∏ i, ENNReal.ofReal (f i (x i))
          ∂multivariateGaussian (0 : Coord m) R := by
    rw [ofReal_integral_eq_lintegral_ofReal hproduct_int
      (Filter.Eventually.of_forall hproduct_nonneg)]
    apply lintegral_congr
    intro x
    exact ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hf_nonneg i (x i)
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hproduct_nonneg)).1
  rw [hleft, hright]
  exact ofReal_mul_prod_setLIntegral_le_lintegral hR L f hf_meas hcle

end Public
end WeakSimplex
