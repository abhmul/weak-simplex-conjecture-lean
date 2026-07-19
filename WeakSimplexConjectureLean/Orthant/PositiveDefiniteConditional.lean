import WeakSimplexConjectureLean.Orthant.AdaptiveReduction
import WeakSimplexConjectureLean.Product.CenteredProperty

/-!
# Conditional positive-definite lower-orthant comparison

This module closes the adaptive branch under the explicit centered-product property that the
product branch will discharge.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace WeakSimplex

/-- A positive-definite weak-simplex covariance satisfies the lower-orthant comparison whenever its
centered product property holds. -/
theorem lowerOrthant_ge_iid_of_posDef_of_centeredProduct
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hpd : R.PosDef)
    (c : ℝ)
    (hcenteredProduct : CenteredProductProperty R) :
    (multivariateGaussian 0 R) (lowerOrthant c) ≥
      (gaussianReal 0 1) (Set.Iic c) ^ m := by
  obtain ⟨w⟩ := exists_adaptiveWitnesses hm R hpd hR.2 c
  let f : Fin m → ℝ → ℝ := fun i ↦ centeredTiltedHalfLine (w.s i)
  have hproduct :
      (∏ i, ∫ x, centeredTiltedHalfLine (w.s i) x ∂gaussianReal 0 1) ≤
        ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
          ∂multivariateGaussian 0 R := by
    apply hcenteredProduct f
    · exact fun i ↦ measurable_centeredTiltedHalfLine (w.s i)
    · exact fun i x ↦ centeredTiltedHalfLine_nonneg (w.s i) x
    · exact fun i ↦ isBounded_range_centeredTiltedHalfLine (w.s i)
    · exact fun i ↦ isLogConcave_centeredTiltedHalfLine (w.s i)
    · exact fun i ↦ integral_centeredTiltedHalfLine_pos (w.s i)
    · exact fun i ↦ integral_mul_centeredTiltedHalfLine (w.s i)
  have hreal :
      normalCDF c ^ m ≤
        Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R := by
    calc
      normalCDF c ^ m ≤
          Real.exp
              ((⟪w.a, w.a⟫_ℝ - ⟪w.a, matrixMul R w.a⟫_ℝ) / 2) *
            ∏ i, normalCDF (w.s i) := adaptiveValue_exp_bound w
      _ = Real.exp (-qform R w.a / 2) *
          (Real.exp (⟪w.a, w.a⟫_ℝ / 2) *
            ∏ i, normalCDF (w.s i)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        simp only [qform]
        ring
      _ = Real.exp (-qform R w.a / 2) *
          ∏ i, ∫ x, centeredTiltedHalfLine (w.s i) x
            ∂gaussianReal 0 1 := by
        rw [adaptiveProduct_mass_eq]
      _ ≤ Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R :=
        mul_le_mul_of_nonneg_left hproduct (Real.exp_nonneg _)
  rw [lowerOrthant_eq_adaptiveProduct R hpd.posSemidef c w,
    ← normalCDF_eq_measure_Iic,
    ← ENNReal.ofReal_pow (normalCDF_pos c).le]
  exact ENNReal.ofReal_le_ofReal hreal

end WeakSimplex
