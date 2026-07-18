import WeakSimplexConjectureLean.Coding.Gram
import WeakSimplexConjectureLean.Coding.Normalization

/-!
# Regular-simplex comparison

This module proves that the nonnegative moment-generating function of a Gaussian maximum is bounded
by the value associated with the regular-simplex Gram matrix.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace WeakSimplex

/-- Every correlation-matrix Gaussian maximum has no larger nonnegative MGF than the
regular-simplex Gaussian maximum. -/
theorem gramGaussianMax_mgf_le_regularSimplex
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    mgf (coordinateMax (Nat.zero_lt_of_lt hm)) (multivariateGaussian 0 G) lam ≤
      mgf (coordinateMax (Nat.zero_lt_of_lt hm))
        (multivariateGaussian 0 (regularSimplexGram m)) lam := by
  let α : ℝ := ((m : ℝ) - 1) / (m : ℝ)
  let mu : ℝ := lam / Real.sqrt α
  let R : Matrix (Fin m) (Fin m) ℝ :=
    α • G + (1 / (m : ℝ)) • allOnesMatrix m
  have hmatrix := gramNormalization hm G hG
  have hR : IsWeakSimplexCov R := by
    exact hmatrix.1
  have hsimplex : IsCorrelation (regularSimplexGram m) := hmatrix.2.1
  have hnormalizedSimplex :
      α • regularSimplexGram m + (1 / (m : ℝ)) • allOnesMatrix m = 1 := by
    exact hmatrix.2.2
  have hmu : 0 ≤ mu := by
    exact div_nonneg hlam (Real.sqrt_nonneg α)
  have hcomparison :
      mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 R) mu ≤
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu := by
    exact gaussianMax_mgf_le_regularSimplex
      (Nat.zero_lt_of_lt hm) R hR mu hmu
  have hscaledComparison :
      Real.exp (-mu ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 R) mu ≤
        Real.exp (-mu ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu := by
    exact mul_le_mul_of_nonneg_left hcomparison (Real.exp_pos _).le
  have hnormalizationG :=
    gramMgf_normalization_identity hm G hG lam
  have hnormalizationSimplex :=
    gramMgf_normalization_identity hm
      (regularSimplexGram m) hsimplex lam
  have hprefactored :
      Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 G) lam ≤
        Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (regularSimplexGram m)) lam := by
    calc
      Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 G) lam =
          Real.exp (-mu ^ 2 / 2) *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 R) mu := by
                simpa only [α, mu, R] using hnormalizationG
      _ ≤ Real.exp (-mu ^ 2 / 2) *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu :=
        hscaledComparison
      _ = Real.exp (-lam ^ 2 / 2) *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (regularSimplexGram m)) lam := by
                symm
                simpa only [α, mu, hnormalizedSimplex] using
                  hnormalizationSimplex
  exact le_of_mul_le_mul_left hprefactored (Real.exp_pos (-lam ^ 2 / 2))

end WeakSimplex
