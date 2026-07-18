import WeakSimplexConjectureLean.LogConcavity.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Centered Gaussian product property

This module fixes the generic real-valued interface between the product and adaptive branches.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace WeakSimplex

/-- A centered product inequality for bounded nonnegative log-concave factors under covariance
`R`. -/
def CenteredProductProperty {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ (f : Fin m → ℝ → ℝ),
    (∀ i, Measurable (f i)) →
    (∀ i x, 0 ≤ f i x) →
    (∀ i, Bornology.IsBounded (Set.range (f i))) →
    (∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (f i x))) →
    (∀ i, 0 < ∫ x, f i x ∂gaussianReal 0 1) →
    (∀ i, ∫ x, x * f i x ∂gaussianReal 0 1 = 0) →
    (∏ i, ∫ x, f i x ∂gaussianReal 0 1) ≤
      ∫ x, ∏ i, f i (x i) ∂multivariateGaussian 0 R

end WeakSimplex
