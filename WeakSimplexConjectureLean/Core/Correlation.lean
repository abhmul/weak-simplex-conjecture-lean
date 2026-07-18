import WeakSimplexConjectureLean.Core.Matrix

/-!
# Correlation and admissible covariance predicates

This module records the transparent matrix predicates used at the analytic theorem boundary.
-/

namespace WeakSimplex

/-- A positive-semidefinite real matrix with unit diagonal. -/
def IsCorrelation {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  R.PosSemidef ∧ ∀ i, R i i = 1

/-- A correlation matrix satisfying the weak-simplex rank-one domination condition. -/
def IsWeakSimplexCov {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  IsCorrelation R ∧
    (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef

end WeakSimplex
