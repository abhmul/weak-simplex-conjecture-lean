import WeakSimplexConjectureLean.Product.NormalizedSelfConvolution
import WeakSimplexConjectureLean.Tilt.TiltedHalfLine

/-!
# Normalized centered tilted half-lines

This module normalizes the adaptive tilted half-line factors and proves continuity of their
normalized self-convolutions by an explicit Gaussian interval formula.
-/

namespace WeakSimplex

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- The centered tilted half-line normalized to have standard Gaussian mass one. -/
def normalizedCenteredTiltedHalfLine (s x : ℝ) : ℝ :=
  (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ *
    centeredTiltedHalfLine s x

theorem measurable_normalizedCenteredTiltedHalfLine (s : ℝ) :
    Measurable (normalizedCenteredTiltedHalfLine s) := by
  exact measurable_const.mul (measurable_centeredTiltedHalfLine s)

theorem normalizedCenteredTiltedHalfLine_nonneg (s x : ℝ) :
    0 ≤ normalizedCenteredTiltedHalfLine s x := by
  exact mul_nonneg (inv_nonneg.mpr (integral_centeredTiltedHalfLine_pos s).le)
    (centeredTiltedHalfLine_nonneg s x)

theorem integrable_normalizedCenteredTiltedHalfLine (s : ℝ) :
    Integrable (normalizedCenteredTiltedHalfLine s) (gaussianReal 0 1) := by
  exact (integrable_centeredTiltedHalfLine s).const_mul
    (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹

theorem isBounded_range_normalizedCenteredTiltedHalfLine (s : ℝ) :
    Bornology.IsBounded (Set.range (normalizedCenteredTiltedHalfLine s)) := by
  let M := ∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1
  apply (Metric.isBounded_Icc (0 : ℝ) (M⁻¹ * Real.exp (r s * H s))).subset
  rintro y ⟨x, rfl⟩
  refine ⟨normalizedCenteredTiltedHalfLine_nonneg s x, ?_⟩
  have hMinv : 0 ≤ M⁻¹ := inv_nonneg.mpr (integral_centeredTiltedHalfLine_pos s).le
  apply mul_le_mul_of_nonneg_left _ hMinv
  by_cases hx : x ∈ Set.Iic (H s)
  · rw [centeredTiltedHalfLine, tiltedHalfLine, Set.indicator_of_mem hx]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (r_pos s).le)
  · simp [centeredTiltedHalfLine, tiltedHalfLine, hx, Real.exp_nonneg]

theorem isLogConcave_normalizedCenteredTiltedHalfLine (s : ℝ) :
    IsLogConcave
      (fun x ↦ ENNReal.ofReal (normalizedCenteredTiltedHalfLine s x)) := by
  let M := ∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1
  have hmain := (isLogConcave_const (E := ℝ) (ENNReal.ofReal M⁻¹)).mul
    (isLogConcave_centeredTiltedHalfLine s)
  convert hmain using 1
  funext x
  rw [Pi.mul_apply, normalizedCenteredTiltedHalfLine,
    ENNReal.ofReal_mul (inv_nonneg.mpr (integral_centeredTiltedHalfLine_pos s).le)]

theorem integral_normalizedCenteredTiltedHalfLine (s : ℝ) :
    (∫ x, normalizedCenteredTiltedHalfLine s x ∂gaussianReal 0 1) = 1 := by
  rw [show normalizedCenteredTiltedHalfLine s = fun x ↦
      (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ *
        centeredTiltedHalfLine s x by rfl,
    integral_const_mul, inv_mul_cancel₀ (integral_centeredTiltedHalfLine_pos s).ne']

theorem integral_mul_normalizedCenteredTiltedHalfLine (s : ℝ) :
    (∫ x, x * normalizedCenteredTiltedHalfLine s x ∂gaussianReal 0 1) = 0 := by
  rw [show (fun x ↦ x * normalizedCenteredTiltedHalfLine s x) = fun x ↦
      (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ *
        (x * centeredTiltedHalfLine s x) by
    funext x
    simp only [normalizedCenteredTiltedHalfLine]
    ring,
    integral_const_mul, integral_mul_centeredTiltedHalfLine, mul_zero]

private lemma integrable_normalPDF : Integrable normalPDF := by
  exact integrable_gaussianPDFReal 0 1

private lemma gaussianReal_Icc_eq_ofReal_normalCDF_sub {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1) (Set.Icc a b) =
      ENNReal.ofReal (normalCDF b - normalCDF a) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  congr 1
  calc
    (∫ x in Set.Icc a b, normalPDF x) =
        ∫ x in Set.Ioc a b, normalPDF x := integral_Icc_eq_integral_Ioc
    _ = ∫ x in a..b, normalPDF x :=
      (intervalIntegral.integral_of_le hab).symm
    _ = normalCDF b - normalCDF a :=
      (intervalIntegral.integral_Iic_sub_Iic
        integrable_normalPDF.integrableOn integrable_normalPDF.integrableOn).symm

/-- The product of two normalized centered tilted half-lines after the sum--difference
rotation is a positive scalar times a symmetric-interval indicator. -/
lemma normalizedCenteredTiltedHalfLine_product (s u v : ℝ) :
    normalizedCenteredTiltedHalfLine s ((u + v) / Real.sqrt 2) *
        normalizedCenteredTiltedHalfLine s ((u - v) / Real.sqrt 2) =
      (Set.Icc (u - Real.sqrt 2 * H s) (Real.sqrt 2 * H s - u)).indicator
        (fun _ ↦
          (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ ^ 2 *
            Real.exp (Real.sqrt 2 * r s * u)) v := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hplus : (u + v) / Real.sqrt 2 ≤ H s ↔
      v ≤ Real.sqrt 2 * H s - u := by
    rw [div_le_iff₀ hsqrt]
    constructor <;> intro h <;> nlinarith
  have hminus : (u - v) / Real.sqrt 2 ≤ H s ↔
      u - Real.sqrt 2 * H s ≤ v := by
    rw [div_le_iff₀ hsqrt]
    constructor <;> intro h <;> nlinarith
  have hexp : r s * ((u + v) / Real.sqrt 2) +
      r s * ((u - v) / Real.sqrt 2) = Real.sqrt 2 * r s * u := by
    field_simp [hsqrt.ne']
    rw [hsqrt_sq]
    ring
  by_cases hv : v ∈ Set.Icc (u - Real.sqrt 2 * H s) (Real.sqrt 2 * H s - u)
  · have hv' := hv
    rw [Set.mem_Icc] at hv'
    have hp : (u + v) / Real.sqrt 2 ∈ Set.Iic (H s) := hplus.2 hv'.2
    have hm : (u - v) / Real.sqrt 2 ∈ Set.Iic (H s) := hminus.2 hv'.1
    have hcp : centeredTiltedHalfLine s ((u + v) / Real.sqrt 2) =
        Real.exp (r s * ((u + v) / Real.sqrt 2)) := by
      simp [centeredTiltedHalfLine, tiltedHalfLine, hp]
    have hcm : centeredTiltedHalfLine s ((u - v) / Real.sqrt 2) =
        Real.exp (r s * ((u - v) / Real.sqrt 2)) := by
      simp [centeredTiltedHalfLine, tiltedHalfLine, hm]
    rw [Set.indicator_of_mem hv]
    simp only [normalizedCenteredTiltedHalfLine]
    rw [hcp, hcm]
    calc
      _ = (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ ^ 2 *
          (Real.exp (r s * ((u + v) / Real.sqrt 2)) *
            Real.exp (r s * ((u - v) / Real.sqrt 2))) := by ring
      _ = _ := by rw [← Real.exp_add, hexp]
  · rw [Set.indicator_of_notMem hv]
    simp only [Set.mem_Icc, not_and_or] at hv
    rcases hv with hv | hv
    · have hnot : ¬(u - v) / Real.sqrt 2 ≤ H s := by
        intro h
        exact hv (hminus.1 h)
      simp [normalizedCenteredTiltedHalfLine, centeredTiltedHalfLine, tiltedHalfLine, hnot]
    · have hnot : ¬(u + v) / Real.sqrt 2 ≤ H s := by
        intro h
        exact hv (hplus.1 h)
      simp [normalizedCenteredTiltedHalfLine, centeredTiltedHalfLine, tiltedHalfLine, hnot]

private lemma normalizedSelfConvolution_normalizedCenteredTiltedHalfLine_formula
    (s u : ℝ) :
    normalizedSelfConvolution (normalizedCenteredTiltedHalfLine s) u =
      if u ≤ Real.sqrt 2 * H s then
        (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ ^ 2 *
          Real.exp (Real.sqrt 2 * r s * u) *
            (normalCDF (Real.sqrt 2 * H s - u) -
              normalCDF (u - Real.sqrt 2 * H s))
      else 0 := by
  let C := (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ ^ 2 *
    Real.exp (Real.sqrt 2 * r s * u)
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hintegrand :
      (fun v ↦
        ENNReal.ofReal
            (normalizedCenteredTiltedHalfLine s ((u + v) / Real.sqrt 2)) *
          ENNReal.ofReal
            (normalizedCenteredTiltedHalfLine s ((u - v) / Real.sqrt 2))) =
        (Set.Icc (u - Real.sqrt 2 * H s)
            (Real.sqrt 2 * H s - u)).indicator
          (fun _ ↦ ENNReal.ofReal C) := by
    funext v
    rw [← ENNReal.ofReal_mul (normalizedCenteredTiltedHalfLine_nonneg s _),
      normalizedCenteredTiltedHalfLine_product]
    by_cases hv : v ∈
        Set.Icc (u - Real.sqrt 2 * H s) (Real.sqrt 2 * H s - u)
    · simp only [Set.indicator_of_mem hv, C]
    · simp only [Set.indicator_of_notMem hv, ENNReal.ofReal_zero]
  change (∫⁻ v,
      ENNReal.ofReal
          (normalizedCenteredTiltedHalfLine s ((u + v) / Real.sqrt 2)) *
        ENNReal.ofReal
          (normalizedCenteredTiltedHalfLine s ((u - v) / Real.sqrt 2))
      ∂gaussianReal 0 1).toReal = _
  rw [hintegrand]
  by_cases hu : u ≤ Real.sqrt 2 * H s
  · rw [if_pos hu, lintegral_indicator measurableSet_Icc, setLIntegral_const]
    have hab : u - Real.sqrt 2 * H s ≤ Real.sqrt 2 * H s - u := by
      linarith
    rw [gaussianReal_Icc_eq_ofReal_normalCDF_sub hab]
    have hmono : Monotone normalCDF :=
      (strictMono_of_hasDerivAt_pos hasDerivAt_normalCDF normalPDF_pos).monotone
    have hdiff : 0 ≤ normalCDF (Real.sqrt 2 * H s - u) -
        normalCDF (u - Real.sqrt 2 * H s) :=
      sub_nonneg.mpr (hmono hab)
    rw [← ENNReal.ofReal_mul hC, ENNReal.toReal_ofReal (mul_nonneg hC hdiff)]
  · rw [if_neg hu]
    have hba : Real.sqrt 2 * H s - u < u - Real.sqrt 2 * H s := by
      linarith
    rw [Set.Icc_eq_empty (not_le_of_gt hba), Set.indicator_empty, lintegral_zero,
      ENNReal.toReal_zero]

/-- The self-convolution of a normalized centered tilted half-line is continuous. -/
theorem continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine
    (s : ℝ) :
    Continuous
      (normalizedSelfConvolution (normalizedCenteredTiltedHalfLine s)) := by
  rw [show normalizedSelfConvolution (normalizedCenteredTiltedHalfLine s) =
      fun u ↦ if u ≤ Real.sqrt 2 * H s then
        (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ ^ 2 *
          Real.exp (Real.sqrt 2 * r s * u) *
            (normalCDF (Real.sqrt 2 * H s - u) -
              normalCDF (u - Real.sqrt 2 * H s))
      else 0 by
    funext u
    exact normalizedSelfConvolution_normalizedCenteredTiltedHalfLine_formula s u]
  have hCDF : Continuous normalCDF :=
    continuous_iff_continuousAt.2 fun x ↦ (hasDerivAt_normalCDF x).continuousAt
  apply Continuous.if_le
  · exact
      (continuous_const.mul
          (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).mul
        ((hCDF.comp (continuous_const.sub continuous_id)).sub
          (hCDF.comp (continuous_id.sub continuous_const)))
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const
  · intro u hu
    subst u
    ring_nf

end

end WeakSimplex
