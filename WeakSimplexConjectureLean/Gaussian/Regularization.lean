import WeakSimplexConjectureLean.Core.Correlation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian covariance regularization

This module packages the covariance regularization and Gaussian coupling shared by singular-limit
arguments. It contains no orthant- or rigidity-specific result.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology

namespace WeakSimplex

/-- Couple a covariance with an independent standard Gaussian at weight `ε`. -/
def gaussianRegularizationMap {m : ℕ} (ε : ℝ) :
    Coord m × Coord m → Coord m :=
  fun p ↦ Real.sqrt (1 - ε) • p.1 + Real.sqrt ε • p.2

private def weightedSumCLM {m : ℕ} (a b : ℝ) :
    Coord m × Coord m →L[ℝ] Coord m :=
  a • ContinuousLinearMap.fst ℝ (Coord m) (Coord m) +
    b • ContinuousLinearMap.snd ℝ (Coord m) (Coord m)

@[simp]
private theorem weightedSumCLM_apply {m : ℕ} (a b : ℝ) (p : Coord m × Coord m) :
    weightedSumCLM a b p = a • p.1 + b • p.2 := by
  rfl

private theorem covariance_weightedCoords
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    (a b : ℝ) (i j : Fin m) :
    cov[fun p : Coord m × Coord m ↦ a * p.1 i + b * p.2 i,
        fun p : Coord m × Coord m ↦ a * p.1 j + b * p.2 j;
        (multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))] =
      a ^ 2 * R i j + b ^ 2 * if i = j then 1 else 0 := by
  let μ := multivariateGaussian (0 : Coord m) R
  let ν := stdGaussian (Coord m)
  have hRi : MemLp (fun x : Coord m ↦ x i) 2 μ := by
    simpa [μ] using IsGaussian.memLp_dual μ (EuclideanSpace.proj i) 2 (by simp)
  have hRj : MemLp (fun x : Coord m ↦ x j) 2 μ := by
    simpa [μ] using IsGaussian.memLp_dual μ (EuclideanSpace.proj j) 2 (by simp)
  have hZi : MemLp (fun x : Coord m ↦ x i) 2 ν := by
    simpa [ν] using IsGaussian.memLp_dual ν (EuclideanSpace.proj i) 2 (by simp)
  have hZj : MemLp (fun x : Coord m ↦ x j) 2 ν := by
    simpa [ν] using IsGaussian.memLp_dual ν (EuclideanSpace.proj j) 2 (by simp)
  have hRia : MemLp (fun p : Coord m × Coord m ↦ a * p.1 i) 2 (μ.prod ν) :=
    (hRi.comp_fst ν).const_mul a
  have hRja : MemLp (fun p : Coord m × Coord m ↦ a * p.1 j) 2 (μ.prod ν) :=
    (hRj.comp_fst ν).const_mul a
  have hZib : MemLp (fun p : Coord m × Coord m ↦ b * p.2 i) 2 (μ.prod ν) :=
    (hZi.comp_snd μ).const_mul b
  have hZjb : MemLp (fun p : Coord m × Coord m ↦ b * p.2 j) 2 (μ.prod ν) :=
    (hZj.comp_snd μ).const_mul b
  have hRR :
      cov[fun p : Coord m × Coord m ↦ p.1 i, fun p ↦ p.1 j; μ.prod ν] =
        cov[fun x : Coord m ↦ x i, fun x ↦ x j; μ] := by
    exact (measurePreserving_fst (μ := μ) (ν := ν)).hasLaw.covariance_fun_comp
      (f := fun x : Coord m ↦ x i) (g := fun x : Coord m ↦ x j)
      (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  have hZZ :
      cov[fun p : Coord m × Coord m ↦ p.2 i, fun p ↦ p.2 j; μ.prod ν] =
        cov[fun x : Coord m ↦ x i, fun x ↦ x j; ν] := by
    exact (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw.covariance_fun_comp
      (f := fun x : Coord m ↦ x i) (g := fun x : Coord m ↦ x j)
      (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  have hRZ :
      cov[fun p : Coord m × Coord m ↦ p.1 i, fun p ↦ p.2 j; μ.prod ν] = 0 :=
    covariance_fst_snd_prod hRi hZj
  have hZR :
      cov[fun p : Coord m × Coord m ↦ p.2 i, fun p ↦ p.1 j; μ.prod ν] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod hRj hZi
  have hcovR : cov[fun x : Coord m ↦ x i, fun x ↦ x j; μ] = R i j := by
    exact covariance_eval_multivariateGaussian hR i j
  have hcovOne :
      cov[fun x : Coord m ↦ x i, fun x ↦ x j; ν] =
        if i = j then 1 else 0 := by
    change cov[fun x : Coord m ↦ x i, fun x ↦ x j; stdGaussian (Coord m)] = _
    rw [← multivariateGaussian_zero_one]
    rw [covariance_eval_multivariateGaussian Matrix.PosSemidef.one]
    exact Matrix.one_apply
  change cov[(fun p : Coord m × Coord m ↦ a * p.1 i) +
        (fun p ↦ b * p.2 i),
      (fun p ↦ a * p.1 j) + (fun p ↦ b * p.2 j); μ.prod ν] = _
  rw [covariance_add_left hRia hZib (hRja.add hZjb),
    covariance_add_right hRia hRja hZjb,
    covariance_add_right hZib hRja hZjb]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    hRR, hZZ, hRZ, hZR, hcovR, hcovOne]
  ring

private theorem map_weightedGaussianSum
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) (a b : ℝ) :
    Measure.map (fun p : Coord m × Coord m ↦ a • p.1 + b • p.2)
        ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) =
      multivariateGaussian (0 : Coord m)
        (a ^ 2 • R + b ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  have hS :
      (a ^ 2 • R + b ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    (hR.smul (sq_nonneg a)).add (Matrix.PosSemidef.one.smul (sq_nonneg b))
  change Measure.map (weightedSumCLM a b)
      ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) = _
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map]
    · have hInt :
          Integrable (fun x : Coord m × Coord m ↦ x)
            ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) := by
        exact IsGaussian.integrable_fun_id
      rw [← (weightedSumCLM a b).integral_comp_comm hInt]
      rw [integral_continuousLinearMap_prod]
      · simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
          weightedSumCLM_apply, smul_zero, zero_add, add_zero]
        rw [integral_smul, integral_smul, integral_id_multivariateGaussian,
          integral_id_stdGaussian]
        simp
      · exact IsGaussian.integrable_fun_id
      · exact IsGaussian.integrable_fun_id
    · exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hi :
        (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis i) u) ∘
            weightedSumCLM a b =
          fun p : Coord m × Coord m ↦ a * p.1 i + b * p.2 i := by
      ext p
      simp [PiLp.inner_apply]
    have hj :
        (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis j) u) ∘
            weightedSumCLM a b =
          fun p : Coord m × Coord m ↦ a * p.1 j + b * p.2 j := by
      ext p
      simp [PiLp.inner_apply]
    rw [hi, hj, covariance_weightedCoords R hR a b i j,
      covarianceBilin_multivariateGaussian hS]
    simp [Matrix.one_apply]
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

/-- The Gaussian regularization coupling has the convexly regularized covariance. -/
theorem map_gaussianRegularization_eq_multivariateGaussian
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    Measure.map (gaussianRegularizationMap ε)
        ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) =
      multivariateGaussian (0 : Coord m) ((1 - ε) • R + ε • 1) := by
  change Measure.map
      (fun p : Coord m × Coord m ↦
        Real.sqrt (1 - ε) • p.1 + Real.sqrt ε • p.2) _ = _
  simpa only [Real.sq_sqrt (sub_nonneg.mpr hε₁),
    Real.sq_sqrt hε₀] using
    map_weightedGaussianSum R hR (Real.sqrt (1 - ε)) (Real.sqrt ε)

/-- The dyadic positive regularization sequence used by covariance limits. -/
def regularizationEpsilon (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1)

/-- Every dyadic regularization parameter is positive. -/
theorem regularizationEpsilon_pos (n : ℕ) :
    0 < regularizationEpsilon n := by
  simp only [regularizationEpsilon]
  positivity

/-- Every dyadic regularization parameter is strictly below one. -/
theorem regularizationEpsilon_lt_one (n : ℕ) :
    regularizationEpsilon n < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

/-- The dyadic regularization parameters tend to zero. -/
theorem tendsto_regularizationEpsilon :
    Tendsto regularizationEpsilon atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  change Tendsto ((fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) ∘ fun n ↦ n + 1) atTop (nhds 0)
  exact h.comp (tendsto_add_atTop_nat 1)

/-- The coupled regularized vector converges pointwise to its first component. -/
theorem tendsto_gaussianRegularizationMap
    {m : ℕ} (p : Coord m × Coord m) :
    Tendsto (fun n ↦ gaussianRegularizationMap (regularizationEpsilon n) p)
      atTop (nhds p.1) := by
  have hsqrtOne :
      Tendsto (fun n ↦ Real.sqrt (1 - regularizationEpsilon n)) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using (hone.sub tendsto_regularizationEpsilon).sqrt
  have hsqrtZero :
      Tendsto (fun n ↦ Real.sqrt (regularizationEpsilon n)) atTop (nhds 0) := by
    simpa using tendsto_regularizationEpsilon.sqrt
  simpa [gaussianRegularizationMap] using
    (hsqrtOne.smul_const p.1).add (hsqrtZero.smul_const p.2)

/-- Dyadically regularized Gaussian laws converge in distribution to the original law. -/
theorem tendstoInDistribution_regularized_multivariateGaussian
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) :
    TendstoInDistribution (fun _ : ℕ ↦ id) atTop id
      (fun n ↦ multivariateGaussian (0 : Coord m)
        ((1 - (1 / 2 : ℝ) ^ (n + 1)) • R + (1 / 2 : ℝ) ^ (n + 1) • 1))
      (multivariateGaussian (0 : Coord m) R) := by
  let P := (multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))
  have hcouple : TendstoInDistribution
      (fun n ↦ gaussianRegularizationMap (regularizationEpsilon n)) atTop Prod.fst
      (fun _ ↦ P) P := by
    apply tendstoInDistribution_of_ae_tendsto
    · exact fun n ↦
        (weightedSumCLM (Real.sqrt (1 - regularizationEpsilon n))
          (Real.sqrt (regularizationEpsilon n))).measurable.aemeasurable
    · exact measurable_fst.aemeasurable
    · exact Filter.Eventually.of_forall tendsto_gaussianRegularizationMap
  have hlaw (n : ℕ) :
      P.map (gaussianRegularizationMap (regularizationEpsilon n)) =
        multivariateGaussian (0 : Coord m)
          ((1 - regularizationEpsilon n) • R + regularizationEpsilon n • 1) := by
    dsimp only [P]
    exact map_gaussianRegularization_eq_multivariateGaussian R hR _
      (regularizationEpsilon_pos n).le (regularizationEpsilon_lt_one n).le
  have hfstLaw : P.map Prod.fst = multivariateGaussian (0 : Coord m) R := by
    dsimp only [P]
    exact measurePreserving_fst.map_eq
  refine ⟨fun _ ↦ measurable_id.aemeasurable, measurable_id.aemeasurable, ?_⟩
  have ht := hcouple.tendsto
  simp only [hlaw, hfstLaw] at ht
  simpa only [Measure.map_id, regularizationEpsilon] using ht

private theorem centeredIdentity_posSemidef {m : ℕ} (hm : 0 < m) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) -
      (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub Matrix.isHermitian_one ?_
    apply Matrix.IsHermitian.smul
    · ext i j
      simp [allOnesMatrix]
    · simp
  · intro x
    have hrewrite :
        star x ⬝ᵥ (((1 : Matrix (Fin m) (Fin m) ℝ) -
          (1 / (m : ℝ)) • allOnesMatrix m).mulVec x) =
          (∑ i, x i ^ 2) - (1 / (m : ℝ)) * (∑ i, x i) ^ 2 := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply]
      calc
        (∑ i, x i * ∑ j,
          ((if i = j then 1 else 0) - (1 / (m : ℝ)) * 1) * x j) =
            ∑ i, x i * (x i - (1 / (m : ℝ)) * ∑ j, x j) := by
              apply Finset.sum_congr rfl
              intro i _
              congr 1
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
              simp only [mul_one]
              rw [show (∑ j, (if i = j then 1 else 0) * x j) = x i by simp]
              rw [← Finset.mul_sum]
        _ = (∑ i, x i ^ 2) - (1 / (m : ℝ)) * (∑ i, x i) ^ 2 := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              congr 1
              · simp only [pow_two]
              · rw [← Finset.sum_mul]
                ring
    rw [hrewrite]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hcs : (∑ i, x i) ^ 2 ≤ (m : ℝ) * ∑ i, x i ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
    have hdiv : (∑ i, x i) ^ 2 / (m : ℝ) ≤ ∑ i, x i ^ 2 :=
      (div_le_iff₀ hmR).2 (by simpa [mul_comm] using hcs)
    rw [sub_nonneg]
    simpa [div_eq_inv_mul, mul_comm] using hdiv

/-- Convexly regularize a covariance matrix toward the identity. -/
def regularizedCovariance {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 - ε) • R + ε • 1

/-- Positive regularization of a positive-semidefinite matrix is positive-definite. -/
theorem regularizedCovariance_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (regularizedCovariance R ε).PosDef := by
  have hleft : ((1 - ε) • R).PosSemidef := hR.smul (by linarith)
  have hright : (ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hε0
  exact Matrix.PosDef.posSemidef_add hleft hright

/-- Regularization preserves the correlation-matrix predicate. -/
theorem regularizedCovariance_isCorrelation
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsCorrelation R) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    IsCorrelation (regularizedCovariance R ε) := by
  have hpd := regularizedCovariance_posDef R hR.1 hε0 hε1
  refine ⟨hpd.posSemidef, ?_⟩
  intro i
  simp [regularizedCovariance, hR.2 i]

/-- Regularization preserves the weak-simplex covariance predicate. -/
theorem regularizedCovariance_isWeakSimplexCov
    {m : ℕ} (hm : 0 < m) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    IsWeakSimplexCov (regularizedCovariance R ε) := by
  refine ⟨regularizedCovariance_isCorrelation R hR.1 hε0 hε1, ?_⟩
  have hrewrite :
        regularizedCovariance R ε - (1 / (m : ℝ)) • allOnesMatrix m =
          (1 - ε) • (R - (1 / (m : ℝ)) • allOnesMatrix m) +
            ε • ((1 : Matrix (Fin m) (Fin m) ℝ) -
              (1 / (m : ℝ)) • allOnesMatrix m) := by
        ext i j
        simp [regularizedCovariance]
        ring
  rw [hrewrite]
  exact (hR.2.smul (by linarith)).add
    ((centeredIdentity_posSemidef hm).smul hε0.le)

end WeakSimplex
