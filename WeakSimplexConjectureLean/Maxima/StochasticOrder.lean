import WeakSimplexConjectureLean.Maxima.CoordinateMax
import WeakSimplexConjectureLean.Orthant.Singular

/-!
# Stochastic order for Gaussian maxima

This module translates the equal-threshold lower-orthant theorem into a strict upper-tail comparison
for coordinatewise Gaussian maxima.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace WeakSimplex

private theorem measurable_coordinateMax {m : ℕ} (hm : 0 < m) :
    Measurable (coordinateMax hm) :=
  (continuous_coordinateMax hm).measurable

private theorem multivariateGaussian_one_lowerOrthant
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

private theorem coordinateMax_cdf_ge_iid
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R) {x | coordinateMax hm x ≤ c} ≥
      (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ))
        {x | coordinateMax hm x ≤ c} := by
  have hset : {x : Coord m | coordinateMax hm x ≤ c} = lowerOrthant c := by
    ext x
    exact coordinateMax_le_iff_mem_lowerOrthant hm x c
  rw [hset, multivariateGaussian_one_lowerOrthant]
  exact lowerOrthant_ge_iid hm R hR c

/-- The lower-orthant theorem expressed as upper-tail domination for coordinate maxima. -/
theorem coordinateMax_tail_le_iid
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R) {x | c < coordinateMax hm x} ≤
      (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ))
        {x | c < coordinateMax hm x} := by
  let s : Set (Coord m) := {x | coordinateMax hm x ≤ c}
  have hs : MeasurableSet s :=
    measurableSet_le (measurable_coordinateMax hm) measurable_const
  have htail : {x : Coord m | c < coordinateMax hm x} = sᶜ := by
    ext x
    simp [s]
  rw [htail, prob_compl_eq_one_sub hs, prob_compl_eq_one_sub hs]
  exact tsub_le_tsub_left (coordinateMax_cdf_ge_iid hm R hR c) 1

end WeakSimplex
