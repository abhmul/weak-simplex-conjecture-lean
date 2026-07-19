import WeakSimplexConjectureLean.Coding.WeakSimplex

/-!
# U12 operational-uniqueness spike

This scratch file checks the frozen U12 Bayes and decoder interfaces, conditional on the frozen
U11 strict and equality characterizations for Gram-level Gaussian-maximum MGFs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace WeakSimplex

/-- The exact frozen U11 strict Gram-MGF interface, packaged as a scratch hypothesis. -/
def StrictGramGaussianMaxMgfStatement : Prop :=
  ∀ {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ),
    IsCorrelation G →
      G ≠ regularSimplexGram m →
      ∀ (lam : ℝ), 0 < lam →
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 G) lam <
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (regularSimplexGram m)) lam

/-- The exact frozen U11 Gram-MGF equality interface, packaged as a scratch hypothesis. -/
def GramGaussianMaxMgfEqualityStatement : Prop :=
  ∀ {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ),
    IsCorrelation G →
      ∀ (lam : ℝ), 0 < lam →
        (mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 G) lam =
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (regularSimplexGram m)) lam ↔
          G = regularSimplexGram m)

private theorem unit_norm_of_codeGram_eq_regularSimplexGram_u12
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

/-- The frozen U12 strict Bayes theorem, conditional on the frozen U11 strict theorem. -/
theorem bayesValue_lt_regularSimplex_conditional
    (hgramStrict : StrictGramGaussianMaxMgfStatement)
    {m n k : ℕ} (hm : 1 < m)
    (code : Fin m → Coord n) (simplex : Fin m → Coord k)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram m)
    (hcode_ne : codeGram code ≠ regularSimplexGram m)
    (lam : ℝ) (hlam : 0 < lam) :
    bayesValue (Nat.zero_lt_of_lt hm) code lam <
      bayesValue (Nat.zero_lt_of_lt hm) simplex lam := by
  let factor : ℝ := (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2)
  have hm0 : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hfactor : 0 < factor := by
    exact mul_pos (one_div_pos.mpr hm0) (Real.exp_pos _)
  have hcodeCorrelation : IsCorrelation (codeGram code) :=
    codeGram_isCorrelation code hunit
  have hsimplexUnit :=
    unit_norm_of_codeGram_eq_regularSimplexGram_u12 hm simplex hsimplex
  have hmgf := hgramStrict hm (codeGram code) hcodeCorrelation hcode_ne lam hlam
  calc
    bayesValue (Nat.zero_lt_of_lt hm) code lam =
        factor *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (codeGram code)) lam := by
      simpa only [factor] using
        bayesValue_eq_gramMgf (Nat.zero_lt_of_lt hm) code hunit lam hlam.le
    _ < factor *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (regularSimplexGram m)) lam :=
      mul_lt_mul_of_pos_left hmgf hfactor
    _ = bayesValue (Nat.zero_lt_of_lt hm) simplex lam := by
      symm
      simpa only [factor, hsimplex] using
        bayesValue_eq_gramMgf
          (Nat.zero_lt_of_lt hm) simplex hsimplexUnit lam hlam.le

/-- The frozen U12 Bayes equality theorem, conditional on the frozen U11 equality theorem. -/
theorem bayesValue_eq_regularSimplex_iff_conditional
    (hgramEquality : GramGaussianMaxMgfEqualityStatement)
    {m n k : ℕ} (hm : 1 < m)
    (code : Fin m → Coord n) (simplex : Fin m → Coord k)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram m)
    (lam : ℝ) (hlam : 0 < lam) :
    bayesValue (Nat.zero_lt_of_lt hm) code lam =
        bayesValue (Nat.zero_lt_of_lt hm) simplex lam ↔
      codeGram code = regularSimplexGram m := by
  let factor : ℝ := (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2)
  have hm0 : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hfactor : 0 < factor := by
    exact mul_pos (one_div_pos.mpr hm0) (Real.exp_pos _)
  have hcodeCorrelation : IsCorrelation (codeGram code) :=
    codeGram_isCorrelation code hunit
  have hsimplexUnit :=
    unit_norm_of_codeGram_eq_regularSimplexGram_u12 hm simplex hsimplex
  have hcodeValue :=
    bayesValue_eq_gramMgf (Nat.zero_lt_of_lt hm) code hunit lam hlam.le
  have hsimplexValue :=
    bayesValue_eq_gramMgf
      (Nat.zero_lt_of_lt hm) simplex hsimplexUnit lam hlam.le
  constructor
  · intro hvalue
    apply (hgramEquality hm (codeGram code) hcodeCorrelation lam hlam).mp
    apply mul_left_cancel₀ hfactor.ne'
    calc
      factor *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (codeGram code)) lam =
          bayesValue (Nat.zero_lt_of_lt hm) code lam := by
        symm
        simpa only [factor] using hcodeValue
      _ = bayesValue (Nat.zero_lt_of_lt hm) simplex lam := hvalue
      _ = factor *
          mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian 0 (regularSimplexGram m)) lam := by
        simpa only [factor, hsimplex] using hsimplexValue
  · intro hcode
    calc
      bayesValue (Nat.zero_lt_of_lt hm) code lam =
          factor *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (codeGram code)) lam := by
        simpa only [factor] using hcodeValue
      _ = factor *
            mgf (coordinateMax (Nat.zero_lt_of_lt hm))
              (multivariateGaussian 0 (regularSimplexGram m)) lam := by
        rw [hcode]
      _ = bayesValue (Nat.zero_lt_of_lt hm) simplex lam := by
        symm
        simpa only [factor, hsimplex] using hsimplexValue

/-- The frozen deterministic strict decoder theorem, conditional on the frozen U11 theorem. -/
theorem weak_simplex_strict_conditional
    (hgramStrict : StrictGramGaussianMaxMgfStatement)
    {n : ℕ} (hn : 0 < n)
    (code simplex : Fin (n + 1) → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram (n + 1))
    (hcode_ne : codeGram code ≠ regularSimplexGram (n + 1))
    (lam : ℝ) (hlam : 0 < lam) :
    decoderSuccess (Nat.succ_pos n) code lam <
      decoderSuccess (Nat.succ_pos n) simplex lam := by
  rw [mlDecoder_success_eq_bayesValue, mlDecoder_success_eq_bayesValue]
  exact bayesValue_lt_regularSimplex_conditional
    hgramStrict (Nat.succ_lt_succ hn) code simplex hunit hsimplex hcode_ne lam hlam

/-- The frozen deterministic decoder equality theorem, conditional on the frozen U11 theorem. -/
theorem weak_simplex_eq_iff_codeGram_eq_conditional
    (hgramEquality : GramGaussianMaxMgfEqualityStatement)
    {n : ℕ} (hn : 0 < n)
    (code simplex : Fin (n + 1) → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram (n + 1))
    (lam : ℝ) (hlam : 0 < lam) :
    decoderSuccess (Nat.succ_pos n) code lam =
        decoderSuccess (Nat.succ_pos n) simplex lam ↔
      codeGram code = regularSimplexGram (n + 1) := by
  rw [mlDecoder_success_eq_bayesValue, mlDecoder_success_eq_bayesValue]
  exact bayesValue_eq_regularSimplex_iff_conditional
    hgramEquality (Nat.succ_lt_succ hn) code simplex hunit hsimplex lam hlam

/-- The frozen arbitrary-decoder strict theorem, conditional on the frozen U11 theorem. -/
theorem weak_simplex_strict_of_scoreMaximizingDecoders_conditional
    (hgramStrict : StrictGramGaussianMaxMgfStatement)
    {n : ℕ} (hn : 0 < n)
    (code simplex : Fin (n + 1) → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram (n + 1))
    (hcode_ne : codeGram code ≠ regularSimplexGram (n + 1))
    (lam : ℝ) (hlam : 0 < lam)
    (decoder simplexDecoder : Coord n → Fin (n + 1))
    (hdecoder_meas : Measurable decoder)
    (hdecoder_max : IsScoreMaximizingDecoder code decoder)
    (hsimplexDecoder_meas : Measurable simplexDecoder)
    (hsimplexDecoder_max : IsScoreMaximizingDecoder simplex simplexDecoder) :
    decoderSuccessOf code lam decoder <
      decoderSuccessOf simplex lam simplexDecoder := by
  have hsimplexUnit :=
    unit_norm_of_codeGram_eq_regularSimplexGram_u12
      (Nat.succ_lt_succ hn) simplex hsimplex
  rw [decoderSuccessOf_eq_bayesValue (Nat.succ_pos n) code lam decoder
      hdecoder_meas (hdecoder_max.isLikelihoodMaximizing hunit hlam.le),
    decoderSuccessOf_eq_bayesValue (Nat.succ_pos n) simplex lam simplexDecoder
      hsimplexDecoder_meas
      (hsimplexDecoder_max.isLikelihoodMaximizing hsimplexUnit hlam.le)]
  exact bayesValue_lt_regularSimplex_conditional
    hgramStrict (Nat.succ_lt_succ hn) code simplex hunit hsimplex hcode_ne lam hlam

/-- The frozen arbitrary-decoder equality theorem, conditional on the frozen U11 theorem. -/
theorem weak_simplex_eq_iff_codeGram_eq_of_scoreMaximizingDecoders_conditional
    (hgramEquality : GramGaussianMaxMgfEqualityStatement)
    {n : ℕ} (hn : 0 < n)
    (code simplex : Fin (n + 1) → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1)
    (hsimplex : codeGram simplex = regularSimplexGram (n + 1))
    (lam : ℝ) (hlam : 0 < lam)
    (decoder simplexDecoder : Coord n → Fin (n + 1))
    (hdecoder_meas : Measurable decoder)
    (hdecoder_max : IsScoreMaximizingDecoder code decoder)
    (hsimplexDecoder_meas : Measurable simplexDecoder)
    (hsimplexDecoder_max : IsScoreMaximizingDecoder simplex simplexDecoder) :
    decoderSuccessOf code lam decoder =
        decoderSuccessOf simplex lam simplexDecoder ↔
      codeGram code = regularSimplexGram (n + 1) := by
  have hsimplexUnit :=
    unit_norm_of_codeGram_eq_regularSimplexGram_u12
      (Nat.succ_lt_succ hn) simplex hsimplex
  rw [decoderSuccessOf_eq_bayesValue (Nat.succ_pos n) code lam decoder
      hdecoder_meas (hdecoder_max.isLikelihoodMaximizing hunit hlam.le),
    decoderSuccessOf_eq_bayesValue (Nat.succ_pos n) simplex lam simplexDecoder
      hsimplexDecoder_meas
      (hsimplexDecoder_max.isLikelihoodMaximizing hsimplexUnit hlam.le)]
  exact bayesValue_eq_regularSimplex_iff_conditional
    hgramEquality (Nat.succ_lt_succ hn) code simplex hunit hsimplex lam hlam

end WeakSimplex
