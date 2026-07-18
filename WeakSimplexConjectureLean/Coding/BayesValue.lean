import WeakSimplexConjectureLean.Maxima.ExponentialMoments
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Codebook Gram matrices and the Bayes value

This module defines class likelihood ratios relative to standard Gaussian noise and the
uniform-prior Bayes value as the integral of their pointwise finite maximum. It identifies the
Gaussian score-vector law with the codebook Gram matrix and proves the resulting exact MGF
identity for unit codewords.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace WeakSimplex

/-- The Gram matrix of a finite codebook. -/
def codeGram {m n : ℕ} (code : Fin m → Coord n) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.gram ℝ code

/-- A codebook Gram matrix is positive semidefinite. -/
theorem codeGram_posSemidef {m n : ℕ} (code : Fin m → Coord n) :
    (codeGram code).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ code

/-- The Gram matrix of unit codewords is a correlation matrix. -/
theorem codeGram_isCorrelation
    {m n : ℕ} (code : Fin m → Coord n) (hunit : ∀ i, ‖code i‖ = 1) :
    IsCorrelation (codeGram code) := by
  refine ⟨codeGram_posSemidef code, fun i ↦ ?_⟩
  rw [codeGram, Matrix.gram_apply, real_inner_self_eq_norm_sq, hunit i]
  norm_num

private def scoreCLM {m n : ℕ} (code : Fin m → Coord n) : Coord n →L[ℝ] Coord m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (code i))

private theorem scoreCLM_apply
    {m n : ℕ} (code : Fin m → Coord n) (y : Coord n) (i : Fin m) :
    scoreCLM code y i = ⟪code i, y⟫_ℝ :=
  rfl

private theorem map_scoreCLM_stdGaussian
    {m n : ℕ} (code : Fin m → Coord n) :
    Measure.map (scoreCLM code) (stdGaussian (Coord n)) =
      multivariateGaussian 0 (codeGram code) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp only [integral_id_stdGaussian, map_zero, integral_id_multivariateGaussian]
    · exact IsGaussian.integrable_id
  · ext x y
    have hmem (i : Fin m) :
        MemLp (fun z : Coord n ↦ ⟪code i, z⟫_ℝ) 2 (stdGaussian (Coord n)) := by
      exact IsGaussian.memLp_two_id.continuousLinearMap_comp (innerSL ℝ (code i))
    change covarianceBilin
        ((stdGaussian (Coord n)).map
          (fun z ↦ WithLp.toLp 2 (fun i ↦ ⟪code i, z⟫_ℝ))) x y = _
    rw [covarianceBilin_apply_pi hmem,
      covarianceBilin_multivariateGaussian (codeGram_posSemidef code)]
    have hcov (i j : Fin m) :
        cov[fun z : Coord n ↦ ⟪code i, z⟫_ℝ,
          fun z : Coord n ↦ ⟪code j, z⟫_ℝ; stdGaussian (Coord n)] =
          ⟪code i, code j⟫_ℝ := by
      rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
        covarianceBilin_stdGaussian]
      rfl
    simp_rw [hcov]
    simp only [codeGram, Matrix.gram_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
    simp only [mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The vector of inner-product scores has the Gaussian law determined by the code Gram matrix. -/
theorem map_codeScore_stdGaussian
    {m n : ℕ} (code : Fin m → Coord n) :
    Measure.map
        (fun y : Coord n ↦ Coord.ofFun (fun i ↦ ⟪code i, y⟫_ℝ))
        (stdGaussian (Coord n)) =
      multivariateGaussian 0 (codeGram code) := by
  change Measure.map (scoreCLM code) (stdGaussian (Coord n)) = _
  exact map_scoreCLM_stdGaussian code

/-- Likelihood ratio of one Gaussian-shifted class against standard Gaussian noise. -/
def classLikelihood
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) (y : Coord n) : ℝ :=
  Real.exp
    (⟪lam • code i, y⟫_ℝ -
      qform (1 : Matrix (Fin n) (Fin n) ℝ) (lam • code i) / 2)

/-- The class likelihood written as the usual linear score minus its quadratic correction. -/
theorem classLikelihood_eq_exp_score
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) (y : Coord n) :
    classLikelihood code lam i y =
      Real.exp (lam * ⟪code i, y⟫_ℝ - lam ^ 2 * ‖code i‖ ^ 2 / 2) := by
  have hnorm : ‖lam‖ ^ 2 = lam ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  simp only [classLikelihood, real_inner_smul_left, qform, matrixMul, map_one, map_smul,
    one_apply_eq_self, inner_self_eq_norm_sq_to_K, norm_smul, Real.norm_eq_abs,
    RCLike.ofReal_real_eq_id, id_eq, Real.exp_eq_exp, sub_right_inj, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj']
  rw [← Real.norm_eq_abs, mul_pow, hnorm]

/-- Pointwise finite maximum of the class likelihood ratios. -/
def classLikelihoodMax
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) (y : Coord n) : ℝ :=
  Finset.univ.sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm))
    (fun i ↦ classLikelihood code lam i y)

/-- Uniform-prior Bayes value, defined at the density-maximum boundary. -/
def bayesValue
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) : ℝ :=
  (1 / (m : ℝ)) *
    ∫ y, classLikelihoodMax hm code lam y ∂stdGaussian (Coord n)

/-- Each class likelihood is measurable. -/
theorem measurable_classLikelihood
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) :
    Measurable (classLikelihood code lam i) := by
  unfold classLikelihood
  fun_prop

private theorem classLikelihood_pos
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) (y : Coord n) :
    0 < classLikelihood code lam i y := by
  unfold classLikelihood
  exact Real.exp_pos _

/-- The finite maximum of the class likelihoods is measurable. -/
theorem measurable_classLikelihoodMax
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) :
    Measurable (classLikelihoodMax hm code lam) := by
  unfold classLikelihoodMax
  let hne : Finset.univ.Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
  have h := Finset.measurable_sup' hne
    (fun i (_ : i ∈ Finset.univ) ↦ measurable_classLikelihood code lam i)
  have heq :
      (Finset.univ.sup' hne fun i ↦ classLikelihood code lam i) =
        fun y ↦ Finset.univ.sup' hne fun i ↦ classLikelihood code lam i y := by
    funext y
    exact Finset.sup'_apply hne (fun i ↦ classLikelihood code lam i) y
  rw [← heq]
  exact h

private theorem measurePreserving_scoreCLM
    {m n : ℕ} (code : Fin m → Coord n) :
    MeasurePreserving (scoreCLM code) (stdGaussian (Coord n))
      (multivariateGaussian 0 (codeGram code)) := by
  exact ⟨(scoreCLM code).measurable, map_scoreCLM_stdGaussian code⟩

/-- Each class likelihood is integrable against standard Gaussian noise. -/
theorem integrable_classLikelihood
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) :
    Integrable (classLikelihood code lam i) (stdGaussian (Coord n)) := by
  have heval := measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord m)) (codeGram_posSemidef code) (i := i)
  have hcoord : Integrable (fun x : Coord m ↦ Real.exp (lam * x i))
      (multivariateGaussian 0 (codeGram code)) := by
    have h := heval.integrable_comp_of_integrable
      (integrable_exp_mul_gaussianReal
        (μ := 0) (v := (codeGram code i i).toNNReal) lam)
    change Integrable
      ((fun x : ℝ ↦ Real.exp (lam * x)) ∘ fun x : Coord m ↦ x i)
      (multivariateGaussian 0 (codeGram code))
    exact h
  have hscore : Integrable
      (fun y : Coord n ↦ Real.exp (lam * scoreCLM code y i))
      (stdGaussian (Coord n)) := by
    have h := (measurePreserving_scoreCLM code).integrable_comp_of_integrable hcoord
    change Integrable
      ((fun x : Coord m ↦ Real.exp (lam * x i)) ∘ scoreCLM code)
      (stdGaussian (Coord n))
    exact h
  let c : ℝ := lam ^ 2 * ‖code i‖ ^ 2 / 2
  have heq : classLikelihood code lam i =
      fun y ↦ Real.exp (-c) * Real.exp (lam * scoreCLM code y i) := by
    funext y
    rw [classLikelihood_eq_exp_score, scoreCLM_apply]
    simp only [c, sub_eq_add_neg, Real.exp_add]
    ring
  rw [heq]
  exact hscore.const_mul (Real.exp (-c))

/-- The density maximum is explicitly integrable; the Bayes integral does not rely on the
Bochner-integral-zero convention. -/
theorem integrable_classLikelihoodMax
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) :
    Integrable (classLikelihoodMax hm code lam) (stdGaussian (Coord n)) := by
  have hsum : Integrable (fun y : Coord n ↦
      ∑ i : Fin m, classLikelihood code lam i y) (stdGaussian (Coord n)) := by
    exact integrable_finsetSum Finset.univ fun i _ ↦
      integrable_classLikelihood code lam i
  apply hsum.mono_nonneg
  · exact (measurable_classLikelihoodMax hm code lam).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y ↦ by
      unfold classLikelihoodMax
      obtain ⟨i, hi⟩ :=
        Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
      calc
        0 ≤ classLikelihood code lam i y :=
          (classLikelihood_pos code lam i y).le
        _ ≤ _ := Finset.le_sup'
          (fun i : Fin m ↦ classLikelihood code lam i y)
          hi
  · exact Filter.Eventually.of_forall fun y ↦ by
      unfold classLikelihoodMax
      apply Finset.sup'_le
      intro i hi
      exact Finset.single_le_sum
        (fun j _ ↦ (classLikelihood_pos code lam j y).le) hi

private theorem classLikelihood_of_unit
    {m n : ℕ} (code : Fin m → Coord n) (hunit : ∀ i, ‖code i‖ = 1)
    (lam : ℝ) (i : Fin m) (y : Coord n) :
    classLikelihood code lam i y =
      Real.exp (-lam ^ 2 / 2) * Real.exp (lam * scoreCLM code y i) := by
  rw [classLikelihood_eq_exp_score, scoreCLM_apply, hunit i]
  simp only [one_pow, mul_one, sub_eq_add_neg, Real.exp_add]
  ring_nf

private theorem classLikelihoodMax_of_unit
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1) (lam : ℝ) (hlam : 0 ≤ lam) (y : Coord n) :
    classLikelihoodMax hm code lam y =
      Real.exp (-lam ^ 2 / 2) *
        Real.exp (lam * coordinateMax hm (scoreCLM code y)) := by
  let hne : Finset.univ.Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
  have hmono : Monotone (fun t : ℝ ↦ Real.exp (lam * t)) := by
    intro a b hab
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hlam)
  have htransport :
      Real.exp (lam * Finset.univ.sup' hne (fun i ↦ scoreCLM code y i)) =
        Finset.univ.sup' hne (fun i ↦ Real.exp (lam * scoreCLM code y i)) := by
    simpa only [Function.comp_apply] using
      Finset.apply_sup'_eq_sup'_comp hne (fun t : ℝ ↦ Real.exp (lam * t))
        (fun _ _ ↦ hmono.map_max)
  calc
    classLikelihoodMax hm code lam y =
        Finset.univ.sup' hne (fun i ↦
          Real.exp (-lam ^ 2 / 2) * Real.exp (lam * scoreCLM code y i)) := by
      unfold classLikelihoodMax
      apply Finset.sup'_congr hne rfl
      intro i _
      exact classLikelihood_of_unit code hunit lam i y
    _ = Real.exp (-lam ^ 2 / 2) *
        Finset.univ.sup' hne (fun i ↦ Real.exp (lam * scoreCLM code y i)) := by
      exact (Finset.mul₀_sup' (Real.exp_pos _).le
        (fun i ↦ Real.exp (lam * scoreCLM code y i)) Finset.univ hne).symm
    _ = Real.exp (-lam ^ 2 / 2) *
        Real.exp (lam * Finset.univ.sup' hne (fun i ↦ scoreCLM code y i)) := by
      rw [htransport]
    _ = Real.exp (-lam ^ 2 / 2) *
        Real.exp (lam * coordinateMax hm (scoreCLM code y)) := by
      rfl

private theorem integral_exp_coordinateMax_score_eq_mgf
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) :
    (∫ y, Real.exp (lam * coordinateMax hm (scoreCLM code y))
      ∂stdGaussian (Coord n)) =
      mgf (coordinateMax hm) (multivariateGaussian 0 (codeGram code)) lam := by
  rw [mgf, ← map_scoreCLM_stdGaussian code]
  rw [integral_map (scoreCLM code).measurable.aemeasurable
    ((((continuous_coordinateMax hm).measurable.const_mul lam).exp).aestronglyMeasurable)]

/-- The density-maximum Bayes value is the prefactored Gaussian-maximum MGF determined by the
codebook Gram matrix. -/
theorem bayesValue_eq_gramMgf
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n)
    (hunit : ∀ i, ‖code i‖ = 1) (lam : ℝ) (hlam : 0 ≤ lam) :
    bayesValue hm code lam =
      (1 / (m : ℝ)) * Real.exp (-lam ^ 2 / 2) *
        mgf (coordinateMax hm) (multivariateGaussian 0 (codeGram code)) lam := by
  have hpoint :
      (fun y : Coord n ↦ classLikelihoodMax hm code lam y) =
        fun y ↦ Real.exp (-lam ^ 2 / 2) *
          Real.exp (lam * coordinateMax hm (scoreCLM code y)) := by
    funext y
    exact classLikelihoodMax_of_unit hm code hunit lam hlam y
  rw [bayesValue, hpoint, integral_const_mul,
    integral_exp_coordinateMax_score_eq_mgf hm code lam]
  ring

end WeakSimplex
