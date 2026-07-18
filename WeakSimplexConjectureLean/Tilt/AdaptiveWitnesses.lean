import WeakSimplexConjectureLean.Tilt.Stationarity

/-!
# Adaptive witnesses

This module packages a global adaptive-potential maximizer into the compatibility and value data
used by the lower-orthant comparison.
-/

namespace WeakSimplex

noncomputable section

open scoped BigOperators InnerProductSpace

/-- Coordinate and tilt data satisfying adaptive compatibility and the benchmark value bound. -/
structure AdaptiveWitnesses {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) where
  s : Coord m
  a : Coord m
  a_eq_r : ∀ i, a i = r (s i)
  a_pos : ∀ i, 0 < a i
  compatibility : s + a - matrixMul R a = c • allOnesVector m
  value_bound :
    (∑ i, Real.log (normalCDF (s i))) +
        (⟪a, a⟫_ℝ - ⟪a, matrixMul R a⟫_ℝ) / 2 ≥
      (m : ℝ) * Real.log (normalCDF c)

/-- Positive-definite rank-one domination produces adaptive witnesses at every threshold. -/
theorem exists_adaptiveWitnesses
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef)
    (hdom : (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef)
    (c : ℝ) :
    Nonempty (AdaptiveWitnesses R c) := by
  obtain ⟨s, hmax, hvalue⟩ :=
    exists_adaptivePotential_maximizer_with_value hm R hR hdom c
  let a : Coord m := coordinateMap r s
  refine ⟨{
    s := s
    a := a
    a_eq_r := fun i => rfl
    a_pos := fun i => r_pos (s i)
    compatibility := ?_
    value_bound := ?_
  }⟩
  · simpa only [a] using adaptivePotential_compatibility hR c s hmax
  · rw [adaptivePotential_value_identity hR c s hmax] at hvalue
    simpa only [a] using hvalue

end

end WeakSimplex
