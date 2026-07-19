import WeakSimplexConjectureLean.Core.Correlation
import WeakSimplexConjectureLean.Gaussian.Shift
import WeakSimplexConjectureLean.Tilt.EventShift

/-!
# Adaptive lower-orthant reduction

This module packages the endpoint algebra and Gaussian change of measure shared by non-strict and
strict adaptive lower-orthant comparisons.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace WeakSimplex

private def adaptiveEndpointSet
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : Set (Coord m) :=
  {x | ∀ i, x i ≤ H (w.s i)}

private def adaptiveEndpointIndicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) : ℝ :=
  (adaptiveEndpointSet w).indicator (fun _ ↦ 1) x

private theorem measurableSet_adaptiveEndpointSet
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    MeasurableSet (adaptiveEndpointSet w) := by
  rw [adaptiveEndpointSet, Set.setOf_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_le (by fun_prop) measurable_const

private theorem measurable_adaptiveEndpointIndicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    Measurable (adaptiveEndpointIndicator w) := by
  exact measurable_const.indicator (measurableSet_adaptiveEndpointSet w)

private theorem centeredTiltedHalfLine_le (s x : ℝ) :
    centeredTiltedHalfLine s x ≤ Real.exp (r s * H s) := by
  by_cases hx : x ≤ H s
  · simp only [centeredTiltedHalfLine, tiltedHalfLine, Set.mem_Iic, hx,
      Set.indicator_of_mem]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (r_pos s).le)
  · simp [centeredTiltedHalfLine, tiltedHalfLine, hx, Real.exp_nonneg]

private theorem adaptiveProduct_nonneg
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) :
    0 ≤ ∏ i, centeredTiltedHalfLine (w.s i) (x i) := by
  exact Finset.prod_nonneg fun i _ ↦ centeredTiltedHalfLine_nonneg (w.s i) (x i)

private theorem measurable_adaptiveProduct
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    Measurable (fun x : Coord m ↦
      ∏ i, centeredTiltedHalfLine (w.s i) (x i)) := by
  have hmeas : ∀ S : Finset (Fin m),
      Measurable (fun x : Coord m ↦
        ∏ i ∈ S, centeredTiltedHalfLine (w.s i) (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact measurable_const
    | @insert i S hi ih =>
        simpa only [Finset.prod_insert hi, Function.comp_apply] using
          ((measurable_centeredTiltedHalfLine (w.s i)).comp (by
            simpa only [EuclideanSpace.coe_proj] using
              (EuclideanSpace.proj (𝕜 := ℝ) i).measurable)).mul ih
  simpa using hmeas Finset.univ

private theorem integrable_adaptiveProduct
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    Integrable (fun x : Coord m ↦ ∏ i, centeredTiltedHalfLine (w.s i) (x i))
      (multivariateGaussian 0 R) := by
  apply Integrable.of_bound (C := ∏ i, Real.exp (r (w.s i) * H (w.s i)))
  · exact (measurable_adaptiveProduct w).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (adaptiveProduct_nonneg w x)]
    exact Finset.prod_le_prod
      (fun i _ ↦ centeredTiltedHalfLine_nonneg (w.s i) (x i))
      (fun i _ ↦ centeredTiltedHalfLine_le (w.s i) (x i))

private theorem adaptiveProduct_eq_exp_mul_indicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) :
    (∏ i, centeredTiltedHalfLine (w.s i) (x i)) =
      Real.exp ⟪w.a, x⟫_ℝ * adaptiveEndpointIndicator w x := by
  classical
  by_cases hx : x ∈ adaptiveEndpointSet w
  · have hxi : ∀ i, x i ≤ H (w.s i) := hx
    rw [adaptiveEndpointIndicator, Set.indicator_of_mem hx, mul_one]
    calc
      (∏ i, centeredTiltedHalfLine (w.s i) (x i)) =
          ∏ i, Real.exp (r (w.s i) * x i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [centeredTiltedHalfLine, tiltedHalfLine, hxi i]
      _ = Real.exp (∑ i, r (w.s i) * x i) :=
        (Real.exp_sum Finset.univ (fun i ↦ r (w.s i) * x i)).symm
      _ = Real.exp ⟪w.a, x⟫_ℝ := by
        congr 1
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp [w.a_eq_r, mul_comm]
  · obtain ⟨i, hi⟩ : ∃ i, ¬x i ≤ H (w.s i) := by
      simpa only [adaptiveEndpointSet, Set.mem_setOf_eq] using not_forall.mp hx
    rw [adaptiveEndpointIndicator, Set.indicator_of_notMem hx, mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [centeredTiltedHalfLine, tiltedHalfLine, hi]

private theorem lintegral_adaptiveIndicator_shift
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∫⁻ x, ENNReal.ofReal
        (adaptiveEndpointIndicator w (x + matrixMul R w.a))
      ∂multivariateGaussian 0 R) =
      (multivariateGaussian 0 R) (lowerOrthant c) := by
  calc
    (∫⁻ x, ENNReal.ofReal
          (adaptiveEndpointIndicator w (x + matrixMul R w.a))
        ∂multivariateGaussian 0 R) =
        ∫⁻ x, (lowerOrthant c).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
          ∂multivariateGaussian 0 R := by
      congr 1
      funext x
      by_cases hx : x ∈ lowerOrthant c
      · have hshift := (w.shift_le_H_iff x).2 hx
        have hmem : x + matrixMul R w.a ∈ adaptiveEndpointSet w := hshift
        rw [adaptiveEndpointIndicator, Set.indicator_of_mem hmem,
          Set.indicator_of_mem hx]
        norm_num
      · have hshift : ¬∀ i, (x + matrixMul R w.a) i ≤ H (w.s i) := by
          exact mt (w.shift_le_H_iff x).1 hx
        have hmem : x + matrixMul R w.a ∉ adaptiveEndpointSet w := hshift
        rw [adaptiveEndpointIndicator, Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem hx]
        norm_num
    _ = (multivariateGaussian 0 R) (lowerOrthant c) :=
      lintegral_indicator_one (measurableSet_lowerOrthant c)

private theorem lintegral_weighted_adaptiveIndicator
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∫⁻ x, ENNReal.ofReal
        (Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
          adaptiveEndpointIndicator w x)
      ∂multivariateGaussian 0 R) =
      ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R) := by
  let g : Coord m → ℝ := fun x ↦
    ∏ i, centeredTiltedHalfLine (w.s i) (x i)
  have hg_nonneg : ∀ x, 0 ≤ g x := adaptiveProduct_nonneg w
  have hg_int : Integrable g (multivariateGaussian 0 R) := integrable_adaptiveProduct w
  have hg_meas : Measurable g := measurable_adaptiveProduct w
  calc
    (∫⁻ x, ENNReal.ofReal
          (Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
            adaptiveEndpointIndicator w x)
        ∂multivariateGaussian 0 R) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (-qform R w.a / 2)) *
          ENNReal.ofReal (g x) ∂multivariateGaussian 0 R := by
      congr 1
      funext x
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        show Real.exp (-qform R w.a / 2) * g x =
            Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
              adaptiveEndpointIndicator w x by
          dsimp only [g]
          rw [adaptiveProduct_eq_exp_mul_indicator]
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring]
    _ = ENNReal.ofReal (Real.exp (-qform R w.a / 2)) *
        ∫⁻ x, ENNReal.ofReal (g x) ∂multivariateGaussian 0 R := by
      rw [lintegral_const_mul]
      exact hg_meas.ennreal_ofReal
    _ = ENNReal.ofReal (Real.exp (-qform R w.a / 2)) *
        ENNReal.ofReal (∫ x, g x ∂multivariateGaussian 0 R) := by
      rw [ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nonneg)]
    _ = ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R) := by
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem adaptiveProduct_mass_eq
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∏ i, ∫ x, centeredTiltedHalfLine (w.s i) x ∂gaussianReal 0 1) =
      Real.exp (⟪w.a, w.a⟫_ℝ / 2) * ∏ i, normalCDF (w.s i) := by
  simp_rw [integral_centeredTiltedHalfLine]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  rw [PiLp.inner_apply]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [w.a_eq_r]
  simp

theorem adaptiveValue_exp_bound
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    normalCDF c ^ m ≤
      Real.exp
        ((⟪w.a, w.a⟫_ℝ - ⟪w.a, matrixMul R w.a⟫_ℝ) / 2) *
        ∏ i, normalCDF (w.s i) := by
  have h := Real.exp_le_exp.mpr w.value_bound
  rw [Real.exp_add, Real.exp_sum] at h
  simp_rw [Real.exp_log (normalCDF_pos _)] at h
  have hc : Real.exp ((m : ℝ) * Real.log (normalCDF c)) = normalCDF c ^ m := by
    rw [show (m : ℝ) * Real.log (normalCDF c) =
        (m : ℕ) * Real.log (normalCDF c) by rfl,
      Real.exp_nat_mul, Real.exp_log (normalCDF_pos c)]
  rw [hc] at h
  simpa only [mul_comm] using h

/-- Rewrite a lower-orthant probability as an adaptively tilted product integral. -/
theorem lowerOrthant_eq_adaptiveProduct
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    (c : ℝ) (w : AdaptiveWitnesses R c) :
    (multivariateGaussian 0 R) (lowerOrthant c) =
      ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R) := by
  calc
    (multivariateGaussian 0 R) (lowerOrthant c) =
        ∫⁻ x, ENNReal.ofReal
            (adaptiveEndpointIndicator w (x + matrixMul R w.a))
          ∂multivariateGaussian 0 R :=
      (lintegral_adaptiveIndicator_shift w).symm
    _ = ∫⁻ x, ENNReal.ofReal
          (Real.exp (⟪w.a, x⟫_ℝ - qform R w.a / 2) *
            adaptiveEndpointIndicator w x)
        ∂multivariateGaussian 0 R := by
      exact (integral_exp_inner_sub_quadratic_mul hR w.a
        (measurable_adaptiveEndpointIndicator w)).symm
    _ = ENNReal.ofReal
        (Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R) :=
      lintegral_weighted_adaptiveIndicator w

end WeakSimplex
