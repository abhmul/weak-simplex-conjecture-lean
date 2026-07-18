import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Matrix Jacobian on Euclidean coordinates

This isolates the transport from the pinned Pi-coordinate Jacobian to `EuclideanSpace`.
-/

noncomputable section

open MeasureTheory

namespace WP01Density

lemma map_toEuclideanCLM_volume_eq_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
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

#print axioms WP01Density.map_toEuclideanCLM_volume_eq_smul

end WP01Density
