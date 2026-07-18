import WeakSimplexConjectureLean.Gaussian.Shift
import WeakSimplexConjectureLean.LogConcavity.Indicators
import WeakSimplexConjectureLean.Normal.TiltFunctions

/-!
# Centered tilted half-lines

This module defines the truncated exponential factors used after adaptive tilting and verifies their
measurability, boundedness, log-concavity, Gaussian mass, and zero barycenter.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WeakSimplex

/-- A one-dimensional exponential tilt, truncated to a lower half-line. -/
def tiltedHalfLine (a b x : ℝ) : ℝ :=
  (Set.Iic b).indicator (fun y ↦ Real.exp (a * y)) x

theorem measurable_tiltedHalfLine (a b : ℝ) :
    Measurable (tiltedHalfLine a b) := by
  exact (Real.continuous_exp.measurable.comp
    (measurable_const.mul measurable_id)).indicator measurableSet_Iic

theorem tiltedHalfLine_nonneg (a b x : ℝ) :
    0 ≤ tiltedHalfLine a b x := by
  by_cases hx : x ∈ Set.Iic b
  · simp [tiltedHalfLine, hx, Real.exp_nonneg]
  · simp [tiltedHalfLine, hx]

theorem tiltedHalfLine_ne_zero (a b : ℝ) :
    tiltedHalfLine a b b ≠ 0 := by
  simp [tiltedHalfLine, Real.exp_ne_zero]

theorem isBounded_range_tiltedHalfLine {a b : ℝ} (ha : 0 ≤ a) :
    Bornology.IsBounded (Set.range (tiltedHalfLine a b)) := by
  apply (Metric.isBounded_Icc (0 : ℝ) (Real.exp (a * b))).subset
  rintro y ⟨x, rfl⟩
  refine ⟨tiltedHalfLine_nonneg a b x, ?_⟩
  by_cases hx : x ∈ Set.Iic b
  · rw [tiltedHalfLine, Set.indicator_of_mem hx]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ha)
  · simp [tiltedHalfLine, hx, Real.exp_nonneg]

theorem integrable_tiltedHalfLine {a b : ℝ} (ha : 0 ≤ a) :
    Integrable (tiltedHalfLine a b) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const (Real.exp (a * b)))
    (measurable_tiltedHalfLine a b).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (tiltedHalfLine_nonneg a b x)]
  by_cases hx : x ∈ Set.Iic b
  · rw [tiltedHalfLine, Set.indicator_of_mem hx]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ha)
  · simp [tiltedHalfLine, hx, Real.exp_nonneg]

private theorem isLogConcave_expLinear (a : ℝ) :
    IsLogConcave (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (a * x))) := by
  intro t ht_pos ht_lt x y
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simp only [smul_eq_mul]
  ring_nf
  exact le_rfl

theorem isLogConcave_tiltedHalfLine (a b : ℝ) :
    IsLogConcave (fun x ↦ ENNReal.ofReal (tiltedHalfLine a b x)) := by
  have hmul := (isLogConcave_expLinear a).mul
    (isLogConcave_convexIndicator (convex_Iic b))
  convert hmul using 1
  funext x
  by_cases hx : x ∈ Set.Iic b
  · simp [tiltedHalfLine, convexIndicator, hx]
  · simp [tiltedHalfLine, convexIndicator, hx]

private theorem lintegral_exp_sub_sq_half_Iic (a s : ℝ) :
    (∫⁻ x in Set.Iic (s + a),
        ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))
      ∂gaussianReal 0 1) = ENNReal.ofReal (normalCDF s) := by
  have hmap : (gaussianReal 0 1).map (fun x ↦ x + a) =
      gaussianReal a 1 := by
    simpa only [zero_add] using
      ProbabilityTheory.gaussianReal_map_add_const
        (μ := 0) (v := 1) a
  have hpre : (fun x : ℝ ↦ x + a) ⁻¹' Set.Iic (s + a) =
      Set.Iic s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro hx <;> linarith
  rw [← withDensity_apply _ measurableSet_Iic,
    gaussianReal_withDensity_exp_shift,
    ← hmap,
    Measure.map_apply (by fun_prop) measurableSet_Iic,
    hpre, ← normalCDF_eq_measure_Iic]

private theorem lintegral_tiltedHalfLine (a s : ℝ) :
    (∫⁻ x, ENNReal.ofReal (tiltedHalfLine a (s + a) x)
      ∂gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (a ^ 2 / 2) * normalCDF s) := by
  have hindicator :
      (fun x ↦ ENNReal.ofReal (tiltedHalfLine a (s + a) x)) =
        (Set.Iic (s + a)).indicator
          (fun x ↦ ENNReal.ofReal (Real.exp (a * x))) := by
    funext x
    by_cases hx : x ∈ Set.Iic (s + a)
    · simp [tiltedHalfLine, hx]
    · simp [tiltedHalfLine, hx]
  have hfactor : ∀ x : ℝ,
      ENNReal.ofReal (Real.exp (a * x)) =
        ENNReal.ofReal (Real.exp (a ^ 2 / 2)) *
          ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  rw [hindicator, lintegral_indicator measurableSet_Iic]
  simp_rw [hfactor]
  rw [lintegral_const_mul]
  · rw [lintegral_exp_sub_sq_half_Iic,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  · fun_prop

theorem integral_tiltedHalfLine {a s : ℝ} (ha : 0 ≤ a) :
    (∫ x, tiltedHalfLine a (s + a) x ∂gaussianReal 0 1) =
      Real.exp (a ^ 2 / 2) * normalCDF s := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (tiltedHalfLine_nonneg a (s + a)))
    (mul_nonneg (Real.exp_nonneg _) (normalCDF_pos s).le)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_tiltedHalfLine ha)
    (ae_of_all _ (tiltedHalfLine_nonneg a (s + a))),
    lintegral_tiltedHalfLine]

private theorem integral_id_Iic_gaussianReal (s : ℝ) :
    (∫ x in Set.Iic s, x ∂gaussianReal 0 1) = -normalPDF s := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero,
    setIntegral_withDensity_eq_setIntegral_toReal_smul]
  · simpa only [normalPDF, gaussianPDF, ENNReal.toReal_ofReal
      (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 _), smul_eq_mul, mul_comm]
      using truncated_first_moment s
  · exact ProbabilityTheory.measurable_gaussianPDF 0 1
  · exact ae_of_all _ fun _ ↦ ProbabilityTheory.gaussianPDF_lt_top
  · exact measurableSet_Iic

private theorem integral_id_Iic_shifted_gaussianReal (a s : ℝ) :
    (∫ x in Set.Iic (s + a), x ∂gaussianReal a 1) =
      -normalPDF s + a * normalCDF s := by
  have hmap : (gaussianReal 0 1).map (fun x ↦ x + a) =
      gaussianReal a 1 := by
    simpa only [zero_add] using
      ProbabilityTheory.gaussianReal_map_add_const
        (μ := 0) (v := 1) a
  have hpre : (fun x : ℝ ↦ x + a) ⁻¹' Set.Iic (s + a) =
      Set.Iic s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro hx <;> linarith
  have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) := by
    exact (ProbabilityTheory.memLp_id_gaussianReal
      (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hmeasure : (gaussianReal 0 1).real (Set.Iic s) =
      normalCDF s := by
    rw [measureReal_def, ← normalCDF_eq_measure_Iic,
      ENNReal.toReal_ofReal (normalCDF_pos s).le]
  rw [← hmap, setIntegral_map measurableSet_Iic (by fun_prop) (by fun_prop),
    hpre, integral_add hid.integrableOn (integrable_const a),
    integral_id_Iic_gaussianReal, integral_const,
    measureReal_restrict_apply_univ, hmeasure]
  simp only [smul_eq_mul]
  ring

private theorem integral_mul_exp_sub_sq_half_Iic (a s : ℝ) :
    (∫ x in Set.Iic (s + a),
        x * Real.exp (a * x - a ^ 2 / 2)
      ∂gaussianReal 0 1) =
      -normalPDF s + a * normalCDF s := by
  let rho : ℝ → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))
  have hrho : Measurable rho := by
    dsimp only [rho]
    fun_prop
  have hrho_top : ∀ᵐ x ∂(gaussianReal 0 1).restrict (Set.Iic (s + a)),
      rho x < ∞ := by
    exact ae_of_all _ fun _ ↦ by
      simp [rho, ENNReal.ofReal_lt_top]
  calc
    (∫ x in Set.Iic (s + a),
          x * Real.exp (a * x - a ^ 2 / 2)
        ∂gaussianReal 0 1) =
        ∫ x in Set.Iic (s + a), (rho x).toReal • x
          ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [rho, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
      ring
    _ = ∫ x in Set.Iic (s + a), x
          ∂(gaussianReal 0 1).withDensity rho := by
      exact (setIntegral_withDensity_eq_setIntegral_toReal_smul
        hrho hrho_top (fun x : ℝ ↦ x) measurableSet_Iic).symm
    _ = ∫ x in Set.Iic (s + a), x ∂gaussianReal a 1 := by
      rw [show (gaussianReal 0 1).withDensity rho = gaussianReal a 1 by
        simpa only [rho] using
          gaussianReal_withDensity_exp_shift a]
    _ = -normalPDF s + a * normalCDF s :=
      integral_id_Iic_shifted_gaussianReal a s

theorem integral_mul_tiltedHalfLine (a s : ℝ) :
    (∫ x, x * tiltedHalfLine a (s + a) x ∂gaussianReal 0 1) =
      Real.exp (a ^ 2 / 2) *
        (-normalPDF s + a * normalCDF s) := by
  have hindicator :
      (fun x ↦ x * tiltedHalfLine a (s + a) x) =
        (Set.Iic (s + a)).indicator
          (fun x ↦ x * Real.exp (a * x)) := by
    funext x
    by_cases hx : x ∈ Set.Iic (s + a)
    · simp [tiltedHalfLine, hx]
    · simp [tiltedHalfLine, hx]
  have hfactor : ∀ x : ℝ,
      x * Real.exp (a * x) = Real.exp (a ^ 2 / 2) *
        (x * Real.exp (a * x - a ^ 2 / 2)) := by
    intro x
    rw [show Real.exp (a ^ 2 / 2) *
        (x * Real.exp (a * x - a ^ 2 / 2)) =
          x * (Real.exp (a ^ 2 / 2) *
            Real.exp (a * x - a ^ 2 / 2)) by ring,
      ← Real.exp_add]
    congr 2
    ring
  rw [hindicator, integral_indicator measurableSet_Iic]
  simp_rw [hfactor]
  rw [integral_const_mul, integral_mul_exp_sub_sq_half_Iic]

/-- The adaptive half-line factor with tilt `r s` and endpoint `H s`. -/
def centeredTiltedHalfLine (s x : ℝ) : ℝ :=
  tiltedHalfLine (r s) (H s) x

theorem measurable_centeredTiltedHalfLine (s : ℝ) :
    Measurable (centeredTiltedHalfLine s) :=
  measurable_tiltedHalfLine (r s) (H s)

theorem centeredTiltedHalfLine_nonneg (s x : ℝ) :
    0 ≤ centeredTiltedHalfLine s x :=
  tiltedHalfLine_nonneg (r s) (H s) x

theorem centeredTiltedHalfLine_ne_zero (s : ℝ) :
    centeredTiltedHalfLine s (H s) ≠ 0 :=
  tiltedHalfLine_ne_zero (r s) (H s)

theorem isBounded_range_centeredTiltedHalfLine (s : ℝ) :
    Bornology.IsBounded (Set.range (centeredTiltedHalfLine s)) := by
  exact isBounded_range_tiltedHalfLine (r_pos s).le

theorem isLogConcave_centeredTiltedHalfLine (s : ℝ) :
    IsLogConcave
      (fun x ↦ ENNReal.ofReal (centeredTiltedHalfLine s x)) :=
  isLogConcave_tiltedHalfLine (r s) (H s)

theorem integrable_centeredTiltedHalfLine (s : ℝ) :
    Integrable (centeredTiltedHalfLine s) (gaussianReal 0 1) := by
  exact integrable_tiltedHalfLine (r_pos s).le

theorem integral_centeredTiltedHalfLine (s : ℝ) :
    (∫ x, centeredTiltedHalfLine s x ∂gaussianReal 0 1) =
      Real.exp ((r s) ^ 2 / 2) * normalCDF s := by
  simpa only [centeredTiltedHalfLine, H] using
    integral_tiltedHalfLine (a := r s) (s := s) (r_pos s).le

theorem integral_centeredTiltedHalfLine_pos (s : ℝ) :
    0 < ∫ x, centeredTiltedHalfLine s x ∂gaussianReal 0 1 := by
  rw [integral_centeredTiltedHalfLine]
  exact mul_pos (Real.exp_pos _) (normalCDF_pos s)

theorem integral_mul_centeredTiltedHalfLine (s : ℝ) :
    (∫ x, x * centeredTiltedHalfLine s x ∂gaussianReal 0 1) = 0 := by
  rw [show centeredTiltedHalfLine s =
      tiltedHalfLine (r s) (s + r s) by
    funext x
    rfl,
    integral_mul_tiltedHalfLine]
  have hpdf : r s * normalCDF s = normalPDF s := by
    rw [r]
    field_simp [(normalCDF_pos s).ne']
  rw [hpdf]
  ring


end WeakSimplex
