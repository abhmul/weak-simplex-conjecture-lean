import WeakSimplexConjectureLean.LogConcavity.Basic
import WeakSimplexConjectureLean.Core.QuadraticCoercivity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Indicator and Gaussian log-concavity

This module proves log-concavity for convex-set indicators and positive-semidefinite Gaussian
quadratic kernels.
-/

noncomputable section

open scoped ENNReal InnerProductSpace

namespace WeakSimplex

/-- The `ℝ≥0∞` indicator of a set. -/
def convexIndicator {E : Type*} (s : Set E) : E → ℝ≥0∞ :=
  s.indicator (fun _ ↦ 1)

/-- A measurable set has a measurable `ℝ≥0∞` indicator. -/
theorem measurable_convexIndicator
    {E : Type*} [MeasurableSpace E] {s : Set E}
    (hs : MeasurableSet s) : Measurable (convexIndicator s) := by
  exact measurable_const.indicator hs

/-- The indicator of a convex set is log-concave. -/
theorem isLogConcave_convexIndicator
    {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    (hs : Convex ℝ s) : IsLogConcave (convexIndicator s) := by
  intro t ht_pos ht_lt x y
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hxy := hs.lineMap_mem hy hx ⟨ht_pos.le, ht_lt.le⟩
      rw [AffineMap.lineMap_apply_module] at hxy
      have hxy' : t • x + (1 - t) • y ∈ s := by
        simpa only [add_comm] using hxy
      simp [convexIndicator, hx, hy, hxy']
    · simp [convexIndicator, hx, hy, ENNReal.zero_rpow_of_pos (sub_pos.mpr ht_lt)]
  · simp [convexIndicator, hx, ENNReal.zero_rpow_of_pos ht_pos]

private theorem qform_convexCombination_identity
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (x y : Coord m) :
    qform A (t • x + (1 - t) • y) + t * (1 - t) * qform A (x - y) =
      t * qform A x + (1 - t) * qform A y := by
  simp only [qform, matrixMul, map_add, map_sub, map_smul, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

private theorem qform_convexCombination_le
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le : t ≤ 1) (x y : Coord m) :
    qform A (t • x + (1 - t) • y) ≤
      t * qform A x + (1 - t) * qform A y := by
  have hrem : 0 ≤ t * (1 - t) * qform A (x - y) :=
    mul_nonneg (mul_nonneg ht_nonneg (sub_nonneg.mpr ht_le))
      (qform_nonneg_of_posSemidef hA (x - y))
  nlinarith [qform_convexCombination_identity A t x y]

/-- The unnormalized Gaussian kernel associated with a quadratic form. -/
def gaussianQuadraticKernel {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(qform A x) / 2))

/-- A Gaussian quadratic kernel is measurable. -/
theorem measurable_gaussianQuadraticKernel {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (gaussianQuadraticKernel A) := by
  have hq : Continuous (qform A) := by
    exact continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) A).continuous
  exact (hq.neg.div_const 2).rexp.measurable.ennreal_ofReal

/-- A positive-semidefinite Gaussian quadratic kernel is log-concave. -/
theorem isLogConcave_gaussianQuadraticKernel
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) :
    IsLogConcave (gaussianQuadraticKernel A) := by
  intro t ht_pos ht_lt x y
  rw [gaussianQuadraticKernel, gaussianQuadraticKernel, gaussianQuadraticKernel,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith [qform_convexCombination_le hA ht_pos.le ht_lt.le x y]

end WeakSimplex
