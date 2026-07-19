import WeakSimplexConjectureLean.Maxima.StochasticOrder
import WeakSimplexConjectureLean.Orthant.Strict

/-!
# Strict stochastic order for Gaussian maxima

This module translates the strict equal-threshold lower-orthant theorem into a strict upper-tail
comparison for coordinatewise Gaussian maxima.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace WeakSimplex

private theorem coordinateMax_cdf_lt_iid_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (c : ℝ) :
    (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ))
        {x | coordinateMax hm x ≤ c} <
      (multivariateGaussian (0 : Coord m) R) {x | coordinateMax hm x ≤ c} := by
  have hset : {x : Coord m | coordinateMax hm x ≤ c} = lowerOrthant c := by
    ext x
    exact coordinateMax_le_iff_mem_lowerOrthant hm x c
  rw [hset, multivariateGaussian_one_lowerOrthant]
  exact lowerOrthant_gt_iid_of_ne_one hm R hR hRne c

/-- Strict upper-tail comparison away from identity. -/
theorem coordinateMax_tail_lt_iid_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (c : ℝ) :
    (multivariateGaussian 0 R) {x | c < coordinateMax hm x} <
      (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ))
        {x | c < coordinateMax hm x} := by
  let s : Set (Coord m) := {x | coordinateMax hm x ≤ c}
  have hs : MeasurableSet s :=
    measurableSet_le (continuous_coordinateMax hm).measurable measurable_const
  have htail : {x : Coord m | c < coordinateMax hm x} = sᶜ := by
    ext x
    simp [s]
  rw [htail]
  have hcdf := coordinateMax_cdf_lt_iid_of_ne_one hm R hR hRne c
  calc
    (multivariateGaussian (0 : Coord m) R) sᶜ <
        1 - (multivariateGaussian (0 : Coord m)
          (1 : Matrix (Fin m) (Fin m) ℝ)) s :=
      prob_compl_lt_one_sub_of_lt_prob hcdf hs
    _ = (multivariateGaussian (0 : Coord m)
          (1 : Matrix (Fin m) (Fin m) ℝ)) sᶜ := by
      rw [prob_compl_eq_one_sub hs]

end WeakSimplex
