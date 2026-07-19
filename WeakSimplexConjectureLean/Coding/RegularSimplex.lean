import WeakSimplexConjectureLean.Coding.Gram
import WeakSimplexConjectureLean.Coding.Normalization
import WeakSimplexConjectureLean.Maxima.StrictExponentialMoments

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

/-- Every non-simplex correlation-matrix Gaussian maximum has strictly smaller positive MGF than
the regular-simplex Gaussian maximum. -/
theorem gramGaussianMax_mgf_lt_regularSimplex
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G)
    (hGne : G ≠ regularSimplexGram m)
    (lam : ℝ) (hlam : 0 < lam) :
    mgf (coordinateMax (Nat.zero_lt_of_lt hm))
        (multivariateGaussian 0 G) lam <
      mgf (coordinateMax (Nat.zero_lt_of_lt hm))
        (multivariateGaussian 0 (regularSimplexGram m)) lam := by
  let α : ℝ := ((m : ℝ) - 1) / (m : ℝ)
  let mu : ℝ := lam / Real.sqrt α
  let R : Matrix (Fin m) (Fin m) ℝ :=
    α • G + (1 / (m : ℝ)) • allOnesMatrix m
  have hm0 : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hm1 : 0 < (m : ℝ) - 1 := by
    have hmR : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hα : 0 < α := by
    exact div_pos hm1 hm0
  have hsqrtα : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hmatrix := gramNormalization hm G hG
  have hR : IsWeakSimplexCov R := hmatrix.1
  have hsimplex : IsCorrelation (regularSimplexGram m) := hmatrix.2.1
  have hnormalizedSimplex :
      α • regularSimplexGram m + (1 / (m : ℝ)) • allOnesMatrix m = 1 := by
    exact hmatrix.2.2
  have hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ) := by
    intro hRone
    apply hGne
    exact (gramNormalization_eq_one_iff hm G).mp hRone
  have hmu : 0 < mu := div_pos hlam hsqrtα
  have hcomparison :
      mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 R) mu <
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu := by
    exact gaussianMax_mgf_lt_regularSimplex
      (Nat.zero_lt_of_lt hm) R hR hRne mu hmu
  have hscaledComparison :
      Real.exp (-mu ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 R) mu <
        Real.exp (-mu ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu := by
    exact mul_lt_mul_of_pos_left hcomparison (Real.exp_pos _)
  have hnormalizationG := gramMgf_normalization_identity hm G hG lam
  have hnormalizationSimplex :=
    gramMgf_normalization_identity hm (regularSimplexGram m) hsimplex lam
  have hprefactored :
      Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 G) lam <
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
      _ < Real.exp (-mu ^ 2 / 2) *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu :=
        hscaledComparison
      _ = Real.exp (-lam ^ 2 / 2) *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (regularSimplexGram m)) lam := by
                symm
                simpa only [α, mu, hnormalizedSimplex] using hnormalizationSimplex
  exact lt_of_mul_lt_mul_left hprefactored (Real.exp_pos _).le

/-- Equality of one positive Gram-level MGF characterizes the regular simplex. -/
theorem gramGaussianMax_mgf_eq_regularSimplex_iff
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G)
    (lam : ℝ) (hlam : 0 < lam) :
    mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 G) lam =
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian 0 (regularSimplexGram m)) lam ↔
      G = regularSimplexGram m := by
  constructor
  · intro heq
    by_contra hGne
    have hlt := gramGaussianMax_mgf_lt_regularSimplex hm G hG hGne lam hlam
    exact (ne_of_lt hlt) heq
  · rintro rfl
    rfl

end WeakSimplex
