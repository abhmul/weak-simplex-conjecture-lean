import WeakSimplexConjectureLean.Maxima.StochasticOrder

/-!
# U10 strict stochastic-order spike

This file checks the strict complement calculation conditional on the frozen U09 lower-orthant
theorem. It is scratch-only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace WeakSimplex

/-- The frozen U09 acceptance statement, used as an explicit assumption in this spike. -/
def StrictLowerOrthantStatement : Prop :=
  ∀ {m : ℕ}, 0 < m →
    ∀ (R : Matrix (Fin m) (Fin m) ℝ),
      IsWeakSimplexCov R →
      R ≠ (1 : Matrix (Fin m) (Fin m) ℝ) →
      ∀ c : ℝ,
        (gaussianReal 0 1) (Set.Iic c) ^ m <
          (multivariateGaussian 0 R) (lowerOrthant c)

private theorem multivariateGaussian_one_lowerOrthant_u10
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

private theorem coordinateMax_cdf_lt_iid_of_ne_one_of_strictOrthant
    (strictOrthant : StrictLowerOrthantStatement)
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
  rw [hset, multivariateGaussian_one_lowerOrthant_u10]
  exact strictOrthant hm R hR hRne c

/-- The frozen U10 tail theorem, conditional only on the frozen U09 theorem. -/
theorem coordinateMax_tail_lt_iid_of_ne_one_of_strictOrthant
    (strictOrthant : StrictLowerOrthantStatement)
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
  have hcdf := coordinateMax_cdf_lt_iid_of_ne_one_of_strictOrthant
    strictOrthant hm R hR hRne c
  calc
    (multivariateGaussian (0 : Coord m) R) sᶜ <
        1 - (multivariateGaussian (0 : Coord m)
          (1 : Matrix (Fin m) (Fin m) ℝ)) s :=
      prob_compl_lt_one_sub_of_lt_prob hcdf hs
    _ = (multivariateGaussian (0 : Coord m)
          (1 : Matrix (Fin m) (Fin m) ℝ)) sᶜ := by
      rw [prob_compl_eq_one_sub hs]

end WeakSimplex
