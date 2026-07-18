import WeakSimplexConjectureLean.Core.Matrix
import WeakSimplexConjectureLean.Vendor.StatLean.GaussianMGFShift

/-!
# Gaussian exponential shift

This module wraps the selected StatLean Gaussian Esscher identity in project coordinates and
derives the corresponding lintegral change-of-measure formula.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace WeakSimplex

/-- Exponential tilting shifts a one-dimensional standard Gaussian by the tilt parameter. -/
theorem gaussianReal_withDensity_exp_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))) =
      gaussianReal a 1 :=
  Vendor.StatLean.ProbabilityTheory.gaussianReal_withDensity_exp_shift a

/-- Exponential tilting shifts a centered multivariate Gaussian by `R a`. -/
theorem multivariateGaussian_withDensity_exp_shift
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosSemidef) (a : Coord m) :
    (multivariateGaussian 0 R).withDensity
        (fun x ↦ ENNReal.ofReal
          (Real.exp (⟪a, x⟫_ℝ - qform R a / 2))) =
      multivariateGaussian (matrixMul R a) R := by
  simpa only [qform_eq_dotProduct, Coord.toFun, matrixMul] using
    Vendor.StatLean.ProbabilityTheory.multivariateGaussian_withDensity_exp_shift hR a

private theorem multivariateGaussian_eq_map_add
    {m : ℕ} (mu : Coord m) (R : Matrix (Fin m) (Fin m) ℝ) :
    multivariateGaussian mu R =
      Measure.map (fun x : Coord m ↦ x + mu) (multivariateGaussian 0 R) := by
  rw [multivariateGaussian, multivariateGaussian, Measure.map_map]
  · congr 1
    funext x
    simp only [Function.comp_apply, zero_add, add_comm]
  all_goals fun_prop

/-- Lintegral form of the multivariate Gaussian exponential-shift identity. -/
theorem integral_exp_inner_sub_quadratic_mul
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosSemidef) (a : Coord m)
    {F : Coord m → ℝ} (hF : Measurable F) :
    (∫⁻ x, ENNReal.ofReal
        (Real.exp (⟪a, x⟫_ℝ - qform R a / 2) * F x)
      ∂multivariateGaussian 0 R) =
      ∫⁻ x, ENNReal.ofReal (F (x + matrixMul R a))
        ∂multivariateGaussian 0 R := by
  let rho : Coord m → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (Real.exp (⟪a, x⟫_ℝ - qform R a / 2))
  have hrho : Measurable rho := by
    dsimp only [rho]
    fun_prop
  have hF' : Measurable (fun x ↦ ENNReal.ofReal (F x)) := by
    fun_prop
  calc
    (∫⁻ x, ENNReal.ofReal
          (Real.exp (⟪a, x⟫_ℝ - qform R a / 2) * F x)
        ∂multivariateGaussian 0 R) =
        ∫⁻ x, rho x * ENNReal.ofReal (F x)
          ∂multivariateGaussian 0 R := by
      congr 1
      funext x
      exact ENNReal.ofReal_mul (Real.exp_nonneg _)
    _ = ∫⁻ x, ENNReal.ofReal (F x)
          ∂(multivariateGaussian 0 R).withDensity rho := by
      exact (lintegral_withDensity_eq_lintegral_mul
        (multivariateGaussian 0 R) hrho hF').symm
    _ = ∫⁻ x, ENNReal.ofReal (F x)
          ∂multivariateGaussian (matrixMul R a) R := by
      rw [show (multivariateGaussian 0 R).withDensity rho =
          multivariateGaussian (matrixMul R a) R by
        simpa only [rho] using multivariateGaussian_withDensity_exp_shift hR a]
    _ = ∫⁻ x, ENNReal.ofReal (F (x + matrixMul R a))
          ∂multivariateGaussian 0 R := by
      rw [multivariateGaussian_eq_map_add]
      exact lintegral_map hF' (by fun_prop)

end WeakSimplex
