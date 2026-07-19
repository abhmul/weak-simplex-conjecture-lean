import WeakSimplexConjectureLean.Gaussian.Regularization
import WeakSimplexConjectureLean.Product.CenteredProduct

/-!
# Continuous-factor centered product inequality

This module extends the centered product comparison from positive-definite correlation matrices to
arbitrary correlation matrices when the factors are continuous.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace WeakSimplex

private theorem tendsto_integral_regularizedCovariance
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    (F : Coord m →ᵇ ℝ) :
    Tendsto
      (fun n ↦ ∫ x, F x ∂multivariateGaussian (0 : Coord m)
        (regularizedCovariance R (regularizationEpsilon n)))
      atTop
      (nhds (∫ x, F x ∂multivariateGaussian (0 : Coord m) R)) := by
  have hconv : TendstoInDistribution (fun _ : ℕ ↦ id) atTop id
      (fun n ↦ multivariateGaussian (0 : Coord m)
        (regularizedCovariance R (regularizationEpsilon n)))
      (multivariateGaussian (0 : Coord m) R) := by
    simpa only [regularizedCovariance, regularizationEpsilon] using
      tendstoInDistribution_regularized_multivariateGaussian R hR
  have ht :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv.tendsto) F
  simpa using ht

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
      ∫ x, ∏ i, f i (x i) ∂multivariateGaussian 0 R := by
  let factor : Fin m → Coord m →ᵇ ℝ := fun i ↦
    { toFun := fun x ↦ f i (x i)
      continuous_toFun := (hf_cont i).comp (EuclideanSpace.proj i).continuous
      map_bounded' := by
        obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (hf_bounded i)
        exact ⟨C, fun x y ↦ hC (Set.mem_range_self (x i)) (Set.mem_range_self (y i))⟩ }
  let F : Coord m →ᵇ ℝ := ∏ i, factor i
  have hF_apply (x : Coord m) : F x = ∏ i, f i (x i) := by
    simp [F, factor]
  have hineq (n : ℕ) :
      (∏ i, ∫ x, f i x ∂gaussianReal 0 1) ≤
        ∫ x, F x ∂multivariateGaussian (0 : Coord m)
          (regularizedCovariance R (regularizationEpsilon n)) := by
    have hε0 := regularizationEpsilon_pos n
    have hε1 := (regularizationEpsilon_lt_one n).le
    have hcorr := regularizedCovariance_isCorrelation R hR hε0 hε1
    have h := centered_product_of_posDef
      (regularizedCovariance R (regularizationEpsilon n))
      (regularizedCovariance_posDef R hR.1 hε0 hε1) hcorr.2
      f hf_meas hf_nonneg hf_bounded hf_lc hf_mass_pos hf_barycenter
    simpa only [hF_apply] using h
  have hlim := tendsto_integral_regularizedCovariance R hR.1 F
  simpa only [hF_apply] using
    ge_of_tendsto hlim (Filter.Eventually.of_forall hineq)

end WeakSimplex
