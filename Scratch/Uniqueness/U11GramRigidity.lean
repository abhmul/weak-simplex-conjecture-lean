import WeakSimplexConjectureLean.Coding.RegularSimplex

/-!
# U11 Gram-rigidity spike

This scratch file checks the frozen Gram normalization equality and the strict/equality MGF
transfers conditional on the frozen U10 strict Gaussian-maximum theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace WeakSimplex

/-- The normalization equals identity exactly at the regular-simplex Gram matrix. -/
theorem gramNormalization_eq_one_iff
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) :
    ((((m : ℝ) - 1) / (m : ℝ)) • G +
        (1 / (m : ℝ)) • allOnesMatrix m =
      (1 : Matrix (Fin m) (Fin m) ℝ)) ↔
      G = regularSimplexGram m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have hmR : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  constructor
  · intro hnormalization
    ext i j
    have hij := congr_fun (congr_fun hnormalization i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
      Matrix.one_apply] at hij
    simp only [regularSimplexGram, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      allOnesMatrix_apply, smul_eq_mul]
    field_simp at hij ⊢
    linarith
  · rintro rfl
    ext i j
    simp only [regularSimplexGram, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, allOnesMatrix_apply, smul_eq_mul]
    field_simp
    ring

/-- The exact frozen U10 strict-MGF interface, packaged as one scratch hypothesis. -/
def StrictGaussianMaxMgfStatement : Prop :=
  ∀ {m : ℕ} (hm : 0 < m),
    ∀ (R : Matrix (Fin m) (Fin m) ℝ),
      IsWeakSimplexCov R →
      R ≠ (1 : Matrix (Fin m) (Fin m) ℝ) →
      ∀ (mu : ℝ), 0 < mu →
        mgf (coordinateMax hm) (multivariateGaussian 0 R) mu <
          mgf (coordinateMax hm)
            (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) mu

/-- The frozen U11 strict theorem, conditional only on the frozen U10 strict theorem. -/
theorem gramGaussianMax_mgf_lt_regularSimplex_of_strictGaussianMax
    (strictGaussianMax : StrictGaussianMaxMgfStatement)
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
    exact strictGaussianMax (Nat.zero_lt_of_lt hm) R hR hRne mu hmu
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

/-- The frozen U11 equality theorem, conditional only on the frozen U10 strict theorem. -/
theorem gramGaussianMax_mgf_eq_regularSimplex_iff_of_strictGaussianMax
    (strictGaussianMax : StrictGaussianMaxMgfStatement)
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
    have hlt := gramGaussianMax_mgf_lt_regularSimplex_of_strictGaussianMax
      strictGaussianMax hm G hG hGne lam hlam
    exact (ne_of_lt hlt) heq
  · rintro rfl
    rfl

end WeakSimplex
