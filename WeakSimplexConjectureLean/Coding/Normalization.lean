import WeakSimplexConjectureLean.Maxima.ExponentialMoments
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology

namespace WeakSimplex

private def normalizationAlpha (m : ℕ) : ℝ :=
  ((m : ℝ) - 1) / (m : ℝ)

private def commonGaussianVariance {m : ℕ} (hm : 1 < m) : NNReal :=
  ⟨1 / ((m : ℝ) - 1), by
    have hm' : (1 : ℝ) < m := by exact_mod_cast hm
    positivity⟩

private def normalizedGramCovariance {m : ℕ}
    (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  normalizationAlpha m • G + (1 / (m : ℝ)) • allOnesMatrix m

private theorem normalizationAlpha_pos {m : ℕ} (hm : 1 < m) :
    0 < normalizationAlpha m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  unfold normalizationAlpha
  positivity

private theorem normalizationAlpha_mul_commonGaussianVariance
    {m : ℕ} (hm : 1 < m) :
    normalizationAlpha m * (commonGaussianVariance hm : ℝ) = 1 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast hm
    linarith
  change (((m : ℝ) - 1) / (m : ℝ)) * (1 / ((m : ℝ) - 1)) = 1 / (m : ℝ)
  field_simp

private theorem one_div_normalizationAlpha_sub_commonGaussianVariance
    {m : ℕ} (hm : 1 < m) :
    1 / normalizationAlpha m - (commonGaussianVariance hm : ℝ) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast hm
    linarith
  change 1 / (((m : ℝ) - 1) / (m : ℝ)) - 1 / ((m : ℝ) - 1) = 1
  field_simp

private theorem normalizationAlpha_add_one_div
    {m : ℕ} (hm : 1 < m) :
    normalizationAlpha m + 1 / (m : ℝ) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  unfold normalizationAlpha
  field_simp
  ring

private theorem allOnesMatrix_posSemidef (m : ℕ) :
    (allOnesMatrix m).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin m ↦ (1 : ℝ))
  convert h using 1
  ext i j
  simp [allOnesMatrix, Matrix.vecMulVec]

private theorem normalizedGramCovariance_posSemidef
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) :
    (normalizedGramCovariance G).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact hG.1.smul (normalizationAlpha_pos hm).le
  · exact (allOnesMatrix_posSemidef m).smul (by positivity)

private theorem normalizedGramCovariance_diag
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (i : Fin m) :
    normalizedGramCovariance G i i = 1 := by
  simp only [normalizedGramCovariance, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hG.2 i, allOnesMatrix_apply, mul_one]
  exact normalizationAlpha_add_one_div hm

private theorem coordinateMax_add_common
    {m : ℕ} (hm : 0 < m) (x : Coord m) (b : ℝ) :
    coordinateMax hm (x + b • allOnesVector m) = coordinateMax hm x + b := by
  let hu : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
  unfold coordinateMax
  simpa only [PiLp.add_apply, PiLp.smul_apply, allOnesVector_apply, smul_eq_mul, mul_one] using
    (Finset.sup'_add Finset.univ (fun i : Fin m ↦ x i) b hu).symm

private theorem coordinateMax_smul_of_nonneg
    {m : ℕ} (hm : 0 < m) (a : ℝ) (ha : 0 ≤ a) (x : Coord m) :
    coordinateMax hm (a • x) = a * coordinateMax hm x := by
  let hu : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
  unfold coordinateMax
  simpa only [PiLp.smul_apply, smul_eq_mul] using
    (Finset.mul₀_sup' ha (fun i : Fin m ↦ x i) Finset.univ hu).symm

private def commonGaussianCLM {m : ℕ} (a : ℝ) :
    Coord m × ℝ →L[ℝ] Coord m :=
  a • ContinuousLinearMap.fst ℝ (Coord m) ℝ +
    a • (ContinuousLinearMap.snd ℝ (Coord m) ℝ).smulRight (allOnesVector m)

@[simp]
private theorem commonGaussianCLM_apply {m : ℕ} (a : ℝ) (p : Coord m × ℝ) :
    commonGaussianCLM a p = a • p.1 + a • (p.2 • allOnesVector m) := by
  rfl

private theorem covariance_commonGaussianCoords
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G)
    (i j : Fin m) :
    cov[fun p : Coord m × ℝ ↦
          Real.sqrt (normalizationAlpha m) * p.1 i +
            Real.sqrt (normalizationAlpha m) * p.2,
        fun p : Coord m × ℝ ↦
          Real.sqrt (normalizationAlpha m) * p.1 j +
            Real.sqrt (normalizationAlpha m) * p.2;
        (multivariateGaussian (0 : Coord m) G).prod
          (gaussianReal 0 (commonGaussianVariance hm))] =
      normalizedGramCovariance G i j := by
  let p := multivariateGaussian (0 : Coord m) G
  let q := gaussianReal 0 (commonGaussianVariance hm)
  let a := Real.sqrt (normalizationAlpha m)
  have hXi : MemLp (fun x : Coord m ↦ x i) 2 p := by
    simpa [p] using IsGaussian.memLp_dual p (EuclideanSpace.proj i) 2 (by simp)
  have hXj : MemLp (fun x : Coord m ↦ x j) 2 p := by
    simpa [p] using IsGaussian.memLp_dual p (EuclideanSpace.proj j) 2 (by simp)
  have hB : MemLp (fun b : ℝ ↦ b) 2 q := by
    change MemLp id 2 q
    exact IsGaussian.memLp_two_id
  have hXia : MemLp (fun z : Coord m × ℝ ↦ a * z.1 i) 2 (p.prod q) :=
    (hXi.comp_fst q).const_mul a
  have hXja : MemLp (fun z : Coord m × ℝ ↦ a * z.1 j) 2 (p.prod q) :=
    (hXj.comp_fst q).const_mul a
  have hBa : MemLp (fun z : Coord m × ℝ ↦ a * z.2) 2 (p.prod q) :=
    (hB.comp_snd p).const_mul a
  have hXX :
      cov[fun z : Coord m × ℝ ↦ z.1 i, fun z ↦ z.1 j; p.prod q] =
        cov[fun x : Coord m ↦ x i, fun x ↦ x j; p] := by
    exact (measurePreserving_fst (μ := p) (ν := q)).hasLaw.covariance_fun_comp
      (f := fun x : Coord m ↦ x i) (g := fun x : Coord m ↦ x j)
      (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  have hBB :
      cov[fun z : Coord m × ℝ ↦ z.2, fun z ↦ z.2; p.prod q] =
        cov[fun b : ℝ ↦ b, fun b ↦ b; q] := by
    exact (measurePreserving_snd (μ := p) (ν := q)).hasLaw.covariance_fun_comp
      (f := fun b : ℝ ↦ b) (g := fun b : ℝ ↦ b)
      (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  have hXB :
      cov[fun z : Coord m × ℝ ↦ z.1 i, fun z ↦ z.2; p.prod q] = 0 :=
    covariance_fst_snd_prod hXi hB
  have hBX :
      cov[fun z : Coord m × ℝ ↦ z.2, fun z ↦ z.1 j; p.prod q] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod hXj hB
  have hcovG : cov[fun x : Coord m ↦ x i, fun x ↦ x j; p] = G i j := by
    exact covariance_eval_multivariateGaussian hG.1 i j
  have hcovB :
      cov[fun b : ℝ ↦ b, fun b ↦ b; q] =
        (commonGaussianVariance hm : ℝ) := by
    rw [covariance_self (by fun_prop)]
    exact variance_fun_id_gaussianReal
  change cov[(fun z : Coord m × ℝ ↦ a * z.1 i) + (fun z ↦ a * z.2),
      (fun z ↦ a * z.1 j) + (fun z ↦ a * z.2); p.prod q] = _
  rw [covariance_add_left hXia hBa (hXja.add hBa),
    covariance_add_right hXia hXja hBa,
    covariance_add_right hBa hXja hBa]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    hXX, hBB, hXB, hBX, hcovG, hcovB, mul_zero]
  have ha : a ^ 2 = normalizationAlpha m := by
    simpa [a] using Real.sq_sqrt (normalizationAlpha_pos hm).le
  calc
    a * (a * G i j) + 0 + (0 + a * (a * (commonGaussianVariance hm : ℝ))) =
        a ^ 2 * G i j + a ^ 2 * (commonGaussianVariance hm : ℝ) := by ring
    _ = normalizedGramCovariance G i j := by
      rw [ha, normalizationAlpha_mul_commonGaussianVariance hm]
      simp [normalizedGramCovariance, allOnesMatrix]

private theorem map_commonGaussianCLM_eq_multivariateGaussian
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) :
    Measure.map (commonGaussianCLM (Real.sqrt (normalizationAlpha m)))
        ((multivariateGaussian (0 : Coord m) G).prod
          (gaussianReal 0 (commonGaussianVariance hm))) =
      multivariateGaussian (0 : Coord m) (normalizedGramCovariance G) := by
  have hS := normalizedGramCovariance_posSemidef hm G hG
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map]
    · have hInt : Integrable (fun x : Coord m × ℝ ↦ x)
          ((multivariateGaussian (0 : Coord m) G).prod
            (gaussianReal 0 (commonGaussianVariance hm))) := by
        exact IsGaussian.integrable_fun_id
      rw [← (commonGaussianCLM (Real.sqrt (normalizationAlpha m))).integral_comp_comm hInt]
      rw [integral_continuousLinearMap_prod]
      · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          ContinuousLinearMap.inr_apply, commonGaussianCLM_apply, smul_zero, zero_smul,
          zero_add, add_zero]
        rw [integral_smul, integral_smul, integral_smul_const,
          integral_id_multivariateGaussian, integral_id_gaussianReal]
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
            commonGaussianCLM (Real.sqrt (normalizationAlpha m)) =
          fun p : Coord m × ℝ ↦
            Real.sqrt (normalizationAlpha m) * p.1 i +
              Real.sqrt (normalizationAlpha m) * p.2 := by
      ext z
      simp [PiLp.inner_apply]
    have hj :
        (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis j) u) ∘
            commonGaussianCLM (Real.sqrt (normalizationAlpha m)) =
          fun p : Coord m × ℝ ↦
            Real.sqrt (normalizationAlpha m) * p.1 j +
              Real.sqrt (normalizationAlpha m) * p.2 := by
      ext z
      simp [PiLp.inner_apply]
    rw [hi, hj, covariance_commonGaussianCoords hm G hG i j,
      covarianceBilin_multivariateGaussian hS]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

private theorem map_commonGaussian_eq_multivariateGaussian
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) :
    Measure.map
        (fun p : Coord m × ℝ ↦
          Real.sqrt (normalizationAlpha m) •
            (p.1 + p.2 • allOnesVector m))
        ((multivariateGaussian (0 : Coord m) G).prod
          (gaussianReal 0 (commonGaussianVariance hm))) =
      multivariateGaussian (0 : Coord m) (normalizedGramCovariance G) := by
  rw [show (fun p : Coord m × ℝ ↦
      Real.sqrt (normalizationAlpha m) • (p.1 + p.2 • allOnesVector m)) =
      commonGaussianCLM (Real.sqrt (normalizationAlpha m)) by
    funext p
    simp [smul_add]]
  exact map_commonGaussianCLM_eq_multivariateGaussian hm G hG

private theorem exp_mul_coordinateMax_le_sum
    {m : ℕ} (hm : 0 < m) (t : ℝ) (x : Coord m) :
    Real.exp (t * coordinateMax hm x) ≤ ∑ i : Fin m, Real.exp (t * x i) := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm))
    (fun i : Fin m ↦ x i)
  rw [coordinateMax, hmax]
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (t * x j)).le) hi

private theorem integrable_exp_mul_coordinate
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (t : ℝ) (i : Fin m) :
    Integrable (fun x : Coord m ↦ Real.exp (t * x i))
      (multivariateGaussian (0 : Coord m) R) := by
  have hmap := measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord m)) hR (i := i)
  have hmapOne : MeasurePreserving (fun x : Coord m ↦ x i)
      (multivariateGaussian (0 : Coord m) R) (gaussianReal 0 1) := by
    simpa [hdiag i] using hmap
  have hint := hmapOne.integrable_comp_of_integrable
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t)
  simpa [Function.comp_def] using hint

private theorem integrable_exp_mul_coordinateMax
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (t : ℝ) :
    Integrable (fun x : Coord m ↦ Real.exp (t * coordinateMax hm x))
      (multivariateGaussian (0 : Coord m) R) := by
  have hsum : Integrable (fun x : Coord m ↦ ∑ i : Fin m, Real.exp (t * x i))
      (multivariateGaussian (0 : Coord m) R) := by
    exact integrable_finsetSum Finset.univ fun i _ ↦
      integrable_exp_mul_coordinate R hR hdiag t i
  apply hsum.mono_nonneg
  · exact (((continuous_coordinateMax hm).measurable.const_mul t).exp).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall fun x ↦ exp_mul_coordinateMax_le_sum hm t x

private theorem integrable_exp_mul_gramCoordinateMax
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (t : ℝ) :
    Integrable
        (fun x : Coord m ↦
          Real.exp (t * coordinateMax (Nat.zero_lt_of_lt hm) x))
        (multivariateGaussian (0 : Coord m) G) :=
  integrable_exp_mul_coordinateMax (Nat.zero_lt_of_lt hm) G hG.1 hG.2 t

private theorem integrable_exp_mul_normalizedCoordinateMax
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (t : ℝ) :
    Integrable
        (fun x : Coord m ↦
          Real.exp (t * coordinateMax (Nat.zero_lt_of_lt hm) x))
        (multivariateGaussian (0 : Coord m) (normalizedGramCovariance G)) :=
  integrable_exp_mul_coordinateMax (Nat.zero_lt_of_lt hm)
    (normalizedGramCovariance G) (normalizedGramCovariance_posSemidef hm G hG)
    (normalizedGramCovariance_diag hm G hG) t

private theorem integrable_exp_mul_commonGaussianProduct
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (t : ℝ) :
    Integrable
        (fun p : Coord m × ℝ ↦
          Real.exp (t * coordinateMax (Nat.zero_lt_of_lt hm) p.1) *
            Real.exp (t * p.2))
        ((multivariateGaussian (0 : Coord m) G).prod
          (gaussianReal 0 (commonGaussianVariance hm))) :=
  (integrable_exp_mul_gramCoordinateMax hm G hG t).mul_prod
    (integrable_exp_mul_gaussianReal t)

private theorem coordinateMax_commonGaussianMap
    {m : ℕ} (hm : 1 < m) (x : Coord m) (b : ℝ) :
    coordinateMax (Nat.zero_lt_of_lt hm)
        (Real.sqrt (normalizationAlpha m) • (x + b • allOnesVector m)) =
      Real.sqrt (normalizationAlpha m) *
        (coordinateMax (Nat.zero_lt_of_lt hm) x + b) := by
  rw [coordinateMax_smul_of_nonneg _ _ (Real.sqrt_nonneg _) _,
    coordinateMax_add_common]

private theorem mgf_normalizedGramCovariance_eq
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (lambda : ℝ) :
    mgf (coordinateMax (Nat.zero_lt_of_lt hm))
        (multivariateGaussian (0 : Coord m) (normalizedGramCovariance G))
        (lambda / Real.sqrt (normalizationAlpha m)) =
      mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m) G) lambda *
        Real.exp ((commonGaussianVariance hm : ℝ) * lambda ^ 2 / 2) := by
  let T : Coord m × ℝ → Coord m := fun p ↦
    Real.sqrt (normalizationAlpha m) • (p.1 + p.2 • allOnesVector m)
  let P := (multivariateGaussian (0 : Coord m) G).prod
    (gaussianReal 0 (commonGaussianVariance hm))
  have hmap : Measure.map T P =
      multivariateGaussian (0 : Coord m) (normalizedGramCovariance G) := by
    exact map_commonGaussian_eq_multivariateGaussian hm G hG
  have hsqrt : 0 < Real.sqrt (normalizationAlpha m) :=
    Real.sqrt_pos.2 (normalizationAlpha_pos hm)
  rw [← hmap]
  rw [mgf_map (by fun_prop)
    (((continuous_coordinateMax (Nat.zero_lt_of_lt hm)).measurable.const_mul
      (lambda / Real.sqrt (normalizationAlpha m))).exp.aestronglyMeasurable)]
  simp only [mgf, Function.comp_apply]
  have hpoint : ∀ p : Coord m × ℝ,
      lambda / Real.sqrt (normalizationAlpha m) *
          coordinateMax (Nat.zero_lt_of_lt hm) (T p) =
        lambda * coordinateMax (Nat.zero_lt_of_lt hm) p.1 + lambda * p.2 := by
    intro p
    rw [show coordinateMax (Nat.zero_lt_of_lt hm) (T p) =
        Real.sqrt (normalizationAlpha m) *
          (coordinateMax (Nat.zero_lt_of_lt hm) p.1 + p.2) by
      exact coordinateMax_commonGaussianMap hm p.1 p.2]
    field_simp
  simp_rw [hpoint, Real.exp_add]
  have hint : Integrable
      (fun p : Coord m × ℝ ↦
        Real.exp (lambda * coordinateMax (Nat.zero_lt_of_lt hm) p.1) *
          Real.exp (lambda * p.2)) P := by
    exact integrable_exp_mul_commonGaussianProduct hm G hG lambda
  rw [integral_prod _ hint]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  rw [show (∫ b, Real.exp (lambda * b) ∂gaussianReal 0 (commonGaussianVariance hm)) =
      Real.exp ((commonGaussianVariance hm : ℝ) * lambda ^ 2 / 2) by
    simpa [mgf] using congrFun
      (mgf_id_gaussianReal (μ := 0) (v := commonGaussianVariance hm)) lambda]

private theorem gramMgf_normalization_identity_aux
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (lambda : ℝ) :
    Real.exp (-lambda ^ 2 / 2) *
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m) G) lambda =
      Real.exp (-(lambda / Real.sqrt (normalizationAlpha m)) ^ 2 / 2) *
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m) (normalizedGramCovariance G))
          (lambda / Real.sqrt (normalizationAlpha m)) := by
  rw [mgf_normalizedGramCovariance_eq hm G hG lambda]
  symm
  have hsquare : Real.sqrt (normalizationAlpha m) ^ 2 = normalizationAlpha m :=
    Real.sq_sqrt (normalizationAlpha_pos hm).le
  have hexponent :
      -(lambda / Real.sqrt (normalizationAlpha m)) ^ 2 / 2 +
          (commonGaussianVariance hm : ℝ) * lambda ^ 2 / 2 =
        -lambda ^ 2 / 2 := by
    rw [div_pow, hsquare]
    have hcoeff := one_div_normalizationAlpha_sub_commonGaussianVariance hm
    calc
      -(lambda ^ 2 / normalizationAlpha m) / 2 +
          (commonGaussianVariance hm : ℝ) * lambda ^ 2 / 2 =
          -(lambda ^ 2 / 2) *
            (1 / normalizationAlpha m - (commonGaussianVariance hm : ℝ)) := by ring
      _ = -lambda ^ 2 / 2 := by rw [hcoeff]; ring
  calc
    Real.exp (-(lambda / Real.sqrt (normalizationAlpha m)) ^ 2 / 2) *
        (mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian (0 : Coord m) G) lambda *
          Real.exp ((commonGaussianVariance hm : ℝ) * lambda ^ 2 / 2)) =
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
            (multivariateGaussian (0 : Coord m) G) lambda *
          (Real.exp (-(lambda / Real.sqrt (normalizationAlpha m)) ^ 2 / 2) *
            Real.exp ((commonGaussianVariance hm : ℝ) * lambda ^ 2 / 2)) := by ring
    _ = mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m) G) lambda *
        Real.exp (-lambda ^ 2 / 2) := by rw [← Real.exp_add, hexponent]
    _ = Real.exp (-lambda ^ 2 / 2) *
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m) G) lambda := by ring

/-- Common-Gaussian normalization preserves the prefactored MGF of the coordinate maximum. -/
theorem gramMgf_normalization_identity
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) (lambda : ℝ) :
    Real.exp (-lambda ^ 2 / 2) *
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m) G) lambda =
      Real.exp
          (-(lambda / Real.sqrt (((m : ℝ) - 1) / (m : ℝ))) ^ 2 / 2) *
        mgf (coordinateMax (Nat.zero_lt_of_lt hm))
          (multivariateGaussian (0 : Coord m)
            ((((m : ℝ) - 1) / (m : ℝ)) • G +
              (1 / (m : ℝ)) • allOnesMatrix m))
          (lambda / Real.sqrt (((m : ℝ) - 1) / (m : ℝ))) := by
  simpa only [normalizationAlpha, normalizedGramCovariance] using
    gramMgf_normalization_identity_aux hm G hG lambda


end WeakSimplex
