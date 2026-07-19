import WeakSimplexConjectureLean.Orthant.AdaptiveReduction
import WeakSimplexConjectureLean.Tilt.SingularWitnesses

/-!
# U09 strict lower-orthant spike

This file checks that U06 and U07 reduce the strict lower-orthant theorem to the single U08 strict
product theorem. It is scratch-only and deliberately takes that theorem as an explicit parameter.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace WeakSimplex

/-- The independent-covariance lower-orthant identity, exposed below the maxima layer. -/
theorem multivariateGaussian_one_lowerOrthant
    {m : ℕ} (c : ℝ) :
    (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ))
        (lowerOrthant c) =
      (gaussianReal 0 1) (Set.Iic c) ^ m := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]
  rw [Measure.map_apply (by fun_prop) (measurableSet_lowerOrthant c)]
  rw [show (WithLp.toLp 2) ⁻¹' lowerOrthant c =
      Set.pi Set.univ (fun _ : Fin m ↦ Set.Iic c) by
    ext x
    simp only [Set.mem_preimage, lowerOrthant, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Iic]]
  rw [Measure.pi_pi]
  exact Fin.prod_const m ((gaussianReal 0 1) (Set.Iic c))

/-- The frozen U08 statement, used as an explicit assumption in this spike. -/
def CenteredTiltedHalfLineStrictProductStatement : Prop :=
  ∀ {m : ℕ}, 0 < m →
    ∀ (R : Matrix (Fin m) (Fin m) ℝ),
      IsWeakSimplexCov R →
      R ≠ (1 : Matrix (Fin m) (Fin m) ℝ) →
      ∀ s : Coord m,
        (∏ i, ∫ z, centeredTiltedHalfLine (s i) z ∂gaussianReal 0 1) <
          ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
            ∂multivariateGaussian 0 R

/-- Strict lower-orthant comparison, conditional only on the frozen U08 theorem. -/
theorem lowerOrthant_gt_iid_of_ne_one_of_strictProduct
    (strictProduct : CenteredTiltedHalfLineStrictProductStatement)
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (c : ℝ) :
    (gaussianReal 0 1) (Set.Iic c) ^ m <
      (multivariateGaussian 0 R) (lowerOrthant c) := by
  obtain ⟨w⟩ := exists_adaptiveWitnesses_of_weakSimplexCov hm R hR c
  have hproduct :
      (∏ i, ∫ z, centeredTiltedHalfLine (w.s i) z ∂gaussianReal 0 1) <
        ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
          ∂multivariateGaussian 0 R :=
    strictProduct hm R hR hRne w.s
  have hmass :
      normalCDF c ^ m ≤
        Real.exp (-qform R w.a / 2) *
          ∏ i, ∫ z, centeredTiltedHalfLine (w.s i) z ∂gaussianReal 0 1 := by
    calc
      normalCDF c ^ m ≤
          Real.exp
              ((⟪w.a, w.a⟫_ℝ - ⟪w.a, matrixMul R w.a⟫_ℝ) / 2) *
            ∏ i, normalCDF (w.s i) :=
        adaptiveValue_exp_bound w
      _ = Real.exp (-qform R w.a / 2) *
          (Real.exp (⟪w.a, w.a⟫_ℝ / 2) * ∏ i, normalCDF (w.s i)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        simp only [qform]
        ring
      _ = Real.exp (-qform R w.a / 2) *
          ∏ i, ∫ z, centeredTiltedHalfLine (w.s i) z ∂gaussianReal 0 1 := by
        rw [adaptiveProduct_mass_eq]
  have hreal :
      normalCDF c ^ m <
        Real.exp (-qform R w.a / 2) *
          ∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
            ∂multivariateGaussian 0 R :=
    hmass.trans_lt (mul_lt_mul_of_pos_left hproduct (Real.exp_pos _))
  rw [lowerOrthant_eq_adaptiveProduct R hR.1.1 c w,
    ← normalCDF_eq_measure_Iic,
    ← ENNReal.ofReal_pow (normalCDF_pos c).le]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (pow_nonneg (normalCDF_pos c).le m)).2 hreal

/-- Equality at one finite threshold, conditional only on the frozen U08 theorem. -/
theorem lowerOrthant_eq_iid_iff_of_strictProduct
    (strictProduct : CenteredTiltedHalfLineStrictProductStatement)
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian 0 R) (lowerOrthant c) =
        (gaussianReal 0 1) (Set.Iic c) ^ m ↔
      R = (1 : Matrix (Fin m) (Fin m) ℝ) := by
  constructor
  · intro heq
    by_contra hRne
    have hlt := lowerOrthant_gt_iid_of_ne_one_of_strictProduct
      strictProduct hm R hR hRne c
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  · intro hRone
    subst R
    exact multivariateGaussian_one_lowerOrthant c

end WeakSimplex
