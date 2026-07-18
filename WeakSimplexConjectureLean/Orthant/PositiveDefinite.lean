import WeakSimplexConjectureLean.Orthant.PositiveDefiniteConditional
import WeakSimplexConjectureLean.Product.CenteredProduct

noncomputable section

open MeasureTheory ProbabilityTheory

namespace WeakSimplex

/-- Positive-definite weak-simplex covariances satisfy the lower-orthant comparison. -/
theorem lowerOrthant_ge_iid_of_posDef
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hpd : R.PosDef)
    (c : ℝ) :
    (multivariateGaussian 0 R) (lowerOrthant c) ≥
      (gaussianReal 0 1) (Set.Iic c) ^ m := by
  exact lowerOrthant_ge_iid_of_posDef_of_centeredProduct hm R hR hpd c
    (centered_product_of_posDef R hpd hR.1.2)

end WeakSimplex
