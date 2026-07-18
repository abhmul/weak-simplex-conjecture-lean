import WeakSimplexConjectureLean.Coding.MLDecoder
import WeakSimplexConjectureLean.Coding.RegularSimplex

/-!
# Weak Simplex Conjecture

This module reduces maximum-likelihood decoding success to the Gaussian maximum comparison and
states the final weak-simplex theorems, including arbitrary measurable score-maximizing ties.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace WeakSimplex

/-- The matrix-defined regular-simplex Bayes comparison value. -/
def regularSimplexBayesValue {m : ℕ} (hm : 1 < m) (lam : ℝ) : ℝ :=
  (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) *
    mgf (coordinateMax (Nat.zero_lt_of_lt hm))
      (multivariateGaussian 0 (regularSimplexGram m)) lam

private theorem unit_norm_of_codeGram_eq_regularSimplexGram
    {m n : ℕ} (hm : 1 < m) (simplex : Fin m → Coord n)
    (hgram : codeGram simplex = regularSimplexGram m) :
    ∀ i, ‖simplex i‖ = 1 := by
  have hOne : IsCorrelation (1 : Matrix (Fin m) (Fin m) ℝ) :=
    ⟨Matrix.PosSemidef.one, fun i ↦ by simp⟩
  have hregular : IsCorrelation (regularSimplexGram m) :=
    (gramNormalization hm 1 hOne).2.1
  intro i
  have hsquare : ‖simplex i‖ ^ 2 = 1 := by
    have hdiag := hregular.2 i
    rw [← hgram] at hdiag
    simpa only [codeGram, Matrix.gram_apply, real_inner_self_eq_norm_sq] using hdiag
  nlinarith [norm_nonneg (simplex i)]

private theorem bayesValue_le_regularSimplexBayesValue
    {m n : ℕ} (hm : 1 < m)
    (code : Fin m → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    bayesValue (Nat.zero_lt_of_lt hm) code lam ≤
      regularSimplexBayesValue hm lam := by
  have hG : IsCorrelation (codeGram code) := codeGram_isCorrelation code hunit
  have hmgf := gramGaussianMax_mgf_le_regularSimplex
    hm (codeGram code) hG lam hlam
  have hfactor : 0 ≤ (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) := by
    exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _)) (Real.exp_pos _).le
  calc
    bayesValue (Nat.zero_lt_of_lt hm) code lam =
        (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (codeGram code)) lam :=
      bayesValue_eq_gramMgf (Nat.zero_lt_of_lt hm) code hunit lam hlam
    _ ≤ (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (regularSimplexGram m)) lam := by
      exact mul_le_mul_of_nonneg_left hmgf hfactor
    _ = regularSimplexBayesValue hm lam := rfl

/-- A code with regular-simplex Gram matrix has the matrix-defined regular-simplex value. -/
theorem bayesValue_eq_regularSimplexBayesValue_of_codeGram
    {m n : ℕ} (hm : 1 < m) (simplex : Fin m → Coord n)
    (hgram : codeGram simplex = regularSimplexGram m)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    bayesValue (Nat.zero_lt_of_lt hm) simplex lam =
      regularSimplexBayesValue hm lam := by
  have hunit := unit_norm_of_codeGram_eq_regularSimplexGram hm simplex hgram
  calc
    bayesValue (Nat.zero_lt_of_lt hm) simplex lam =
        (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (codeGram simplex)) lam :=
      bayesValue_eq_gramMgf (Nat.zero_lt_of_lt hm) simplex hunit lam hlam
    _ = (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (regularSimplexGram m)) lam := by rw [hgram]
    _ = regularSimplexBayesValue hm lam := rfl

/-- Every unit code has Bayes value at most that of every regular-simplex realization. -/
theorem bayesValue_le_regularSimplex
    {m n k : ℕ} (hm : 1 < m)
    (code : Fin m → Coord n) (simplex : Fin m → Coord k)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram m)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    bayesValue (Nat.zero_lt_of_lt hm) code lam ≤
      bayesValue (Nat.zero_lt_of_lt hm) simplex lam := by
  calc
    bayesValue (Nat.zero_lt_of_lt hm) code lam ≤
        regularSimplexBayesValue hm lam :=
      bayesValue_le_regularSimplexBayesValue hm code hunit lam hlam
    _ = bayesValue (Nat.zero_lt_of_lt hm) simplex lam := by
      symm
      simpa using bayesValue_eq_regularSimplexBayesValue_of_codeGram
        hm simplex hsimplex lam hlam

/-- Operational weak-simplex theorem for the deterministic tie-safe ML decoder. -/
theorem weak_simplex
    {n : ℕ} (hn : 0 < n)
    (code simplex : Fin (n + 1) → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram (n + 1))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    decoderSuccess (Nat.succ_pos n) code lam ≤
      decoderSuccess (Nat.succ_pos n) simplex lam := by
  rw [mlDecoder_success_eq_bayesValue, mlDecoder_success_eq_bayesValue]
  exact bayesValue_le_regularSimplex
    (Nat.succ_lt_succ hn) code simplex hunit hsimplex lam hlam

/-- Operational weak-simplex theorem for arbitrary measurable score-maximizing
tie-breaking rules. -/
theorem weak_simplex_of_scoreMaximizingDecoders
    {n : ℕ} (hn : 0 < n)
    (code simplex : Fin (n + 1) → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram (n + 1))
    (lam : ℝ) (hlam : 0 ≤ lam)
    (decoder simplexDecoder : Coord n → Fin (n + 1))
    (hdecoder_meas : Measurable decoder)
    (hdecoder_max : IsScoreMaximizingDecoder code decoder)
    (hsimplexDecoder_meas : Measurable simplexDecoder)
    (hsimplexDecoder_max : IsScoreMaximizingDecoder simplex simplexDecoder) :
    decoderSuccessOf code lam decoder ≤
      decoderSuccessOf simplex lam simplexDecoder := by
  have hsimplexUnit :=
    unit_norm_of_codeGram_eq_regularSimplexGram (Nat.succ_lt_succ hn) simplex hsimplex
  rw [decoderSuccessOf_eq_bayesValue (Nat.succ_pos n) code lam decoder
      hdecoder_meas (hdecoder_max.isLikelihoodMaximizing hunit hlam),
    decoderSuccessOf_eq_bayesValue (Nat.succ_pos n) simplex lam simplexDecoder
      hsimplexDecoder_meas
      (hsimplexDecoder_max.isLikelihoodMaximizing hsimplexUnit hlam)]
  exact bayesValue_le_regularSimplex
    (Nat.succ_lt_succ hn) code simplex hunit hsimplex lam hlam

end WeakSimplex
