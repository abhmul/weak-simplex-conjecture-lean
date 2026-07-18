import WeakSimplexConjectureLean.Coding.BayesValue
import WeakSimplexConjectureLean.Gaussian.Shift
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace WeakSimplex

section FiniteSelector

variable {X : Type*}

private def finiteScoreMax
    {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm))
    (fun i ↦ score i x)

private def IsScoreMaximizer
    {m : ℕ} (score : Fin m → X → ℝ) (x : X) (i : Fin m) : Prop :=
  ∀ j, score j x ≤ score i x

private theorem exists_isScoreMaximizer
    {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ) (x : X) :
    ∃ i, IsScoreMaximizer score x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm))
    (fun i : Fin m ↦ score i x)
  exact ⟨i, fun j ↦ hi ▸ Finset.le_sup' (fun k : Fin m ↦ score k x) (Finset.mem_univ j)⟩

private def firstMaximizer
    {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ) (x : X) : Fin m := by
  classical
  exact Fin.find (IsScoreMaximizer score x) (exists_isScoreMaximizer hm score x)

private theorem firstMaximizer_maximizes
    {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ) (x : X) (j : Fin m) :
    score j x ≤ score (firstMaximizer hm score x) x := by
  classical
  unfold firstMaximizer
  exact Fin.find_spec (exists_isScoreMaximizer hm score x) j

private theorem firstMaximizer_le_of_maximizes
    {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ) (x : X) (i : Fin m)
    (hi : ∀ j, score j x ≤ score i x) :
    firstMaximizer hm score x ≤ i := by
  classical
  unfold firstMaximizer
  exact Fin.find_le_of_pos (exists_isScoreMaximizer hm score x) hi

private theorem score_firstMaximizer_eq_max
    {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ) (x : X) :
    score (firstMaximizer hm score x) x = finiteScoreMax hm score x := by
  apply le_antisymm
  · exact Finset.le_sup' (fun i : Fin m ↦ score i x) (Finset.mem_univ _)
  · exact Finset.sup'_le _ _ fun i _ ↦ firstMaximizer_maximizes hm score x i

private theorem measurableSet_isScoreMaximizer
    [MeasurableSpace X] {m : ℕ} (score : Fin m → X → ℝ)
    (hscore : ∀ i, Measurable (score i))
    (i : Fin m) : MeasurableSet {x | IsScoreMaximizer score x i} := by
  simpa only [IsScoreMaximizer, Set.setOf_forall] using
    (MeasurableSet.iInter fun j ↦ measurableSet_le (hscore j) (hscore i))

private theorem measurable_firstMaximizer
    [MeasurableSpace X] {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ)
    (hscore : ∀ i, Measurable (score i)) :
    Measurable (firstMaximizer hm score) := by
  classical
  refine measurable_to_countable' fun i ↦ ?_
  rw [show firstMaximizer hm score ⁻¹' {i} =
      {x | IsScoreMaximizer score x i} ∩
        ⋂ j, ⋂ (_h : j < i), {x | ¬ IsScoreMaximizer score x j} by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter]
    exact Fin.find_eq_iff (exists_isScoreMaximizer hm score x)]
  exact (measurableSet_isScoreMaximizer score hscore i).inter <|
    MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_isScoreMaximizer score hscore j).compl

private theorem sum_withDensity_firstMaximizer_eq_integral_max
    [MeasurableSpace X] {m : ℕ} (hm : 0 < m) (score : Fin m → X → ℝ)
    (hscore : ∀ i, Measurable (score i)) (hnonneg : ∀ i x, 0 ≤ score i x)
    (mu : Measure X) (hscore_int : ∀ i, Integrable (score i) mu) :
    ∑ i, ((mu.withDensity fun x ↦ ENNReal.ofReal (score i x))
          {x | firstMaximizer hm score x = i}).toReal =
      ∫ x, finiteScoreMax hm score x ∂mu := by
  classical
  have hdecoder : Measurable (firstMaximizer hm score) :=
    measurable_firstMaximizer hm score hscore
  have hcell : ∀ i, MeasurableSet {x | firstMaximizer hm score x = i} := by
    intro i
    rw [show {x | firstMaximizer hm score x = i} =
        firstMaximizer hm score ⁻¹' {i} by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]]
    exact hdecoder (measurableSet_singleton i)
  calc
    ∑ i, ((mu.withDensity fun x ↦ ENNReal.ofReal (score i x))
          {x | firstMaximizer hm score x = i}).toReal =
        ∑ i, ∫ x in {x | firstMaximizer hm score x = i}, score i x ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show ((mu.withDensity fun x ↦ ENNReal.ofReal (score i x))
          {x | firstMaximizer hm score x = i}).toReal =
          (mu.withDensity fun x ↦ ENNReal.ofReal (score i x)).real
            {x | firstMaximizer hm score x = i} by rfl,
        ← setIntegral_one_eq_measureReal,
        setIntegral_withDensity_eq_setIntegral_toReal_smul]
      · apply integral_congr_ae
        filter_upwards with x
        simp only [ENNReal.toReal_ofReal (hnonneg i x), smul_eq_mul, mul_one]
      · exact (hscore i).ennreal_ofReal
      · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
      · exact hcell i
    _ = ∑ i, ∫ x, {x | firstMaximizer hm score x = i}.indicator (score i) x ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_indicator (hcell i)).symm
    _ = ∫ x, ∑ i, {x | firstMaximizer hm score x = i}.indicator (score i) x ∂mu := by
      rw [integral_finsetSum]
      intro i _
      exact (hscore_int i).integrableOn.integrable_indicator (hcell i)
    _ = ∫ x, finiteScoreMax hm score x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.sum_eq_single (firstMaximizer hm score x)]
      · simp only [Set.mem_setOf_eq, Set.indicator_of_mem, score_firstMaximizer_eq_max]
      · intro i _ hi
        rw [Set.indicator_of_notMem]
        exact Ne.symm hi
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end FiniteSelector

open ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- The deterministic least-index maximum-likelihood decoder. -/
def mlDecoder
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) (y : Coord n) : Fin m :=
  firstMaximizer hm (classLikelihood code lam) y

/-- The selected class has likelihood at least that of every class. -/
theorem mlDecoder_maximizes
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ)
    (y : Coord n) (j : Fin m) :
    classLikelihood code lam j y ≤ classLikelihood code lam (mlDecoder hm code lam y) y :=
  firstMaximizer_maximizes hm (classLikelihood code lam) y j

/-- Among all likelihood maximizers, the decoder chooses the least index. -/
theorem mlDecoder_le_of_maximizes
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ)
    (y : Coord n) (i : Fin m)
    (hi : ∀ j, classLikelihood code lam j y ≤ classLikelihood code lam i y) :
    mlDecoder hm code lam y ≤ i :=
  firstMaximizer_le_of_maximizes hm (classLikelihood code lam) y i hi

/-- The selected likelihood is exactly the pointwise likelihood maximum, including on ties. -/
theorem classLikelihood_mlDecoder_eq_max
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) (y : Coord n) :
    classLikelihood code lam (mlDecoder hm code lam y) y =
      classLikelihoodMax hm code lam y := by
  simpa only [mlDecoder, finiteScoreMax, classLikelihoodMax] using
    score_firstMaximizer_eq_max hm (classLikelihood code lam) y

private theorem measurable_classLikelihood_local
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) :
    Measurable (classLikelihood code lam i) := by
  unfold classLikelihood
  fun_prop

/-- The deterministic ML decoder is measurable into the discrete measurable space on `Fin m`. -/
theorem measurable_mlDecoder
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) :
    Measurable (mlDecoder hm code lam) :=
  measurable_firstMaximizer hm (classLikelihood code lam) fun i ↦
    measurable_classLikelihood_local code lam i

private theorem matrixMul_one {n : ℕ} (x : Coord n) :
    matrixMul (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  rw [← Coord.ofFun_toFun x, matrixMul_ofFun, Matrix.one_mulVec]

private theorem stdGaussian_withDensity_classLikelihood
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) :
    (stdGaussian (Coord n)).withDensity
        (fun y ↦ ENNReal.ofReal (classLikelihood code lam i y)) =
      multivariateGaussian (lam • code i) (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← multivariateGaussian_zero_one]
  simpa only [classLikelihood, matrixMul_one] using
    multivariateGaussian_withDensity_exp_shift
      (R := (1 : Matrix (Fin n) (Fin n) ℝ)) Matrix.PosSemidef.one (lam • code i)

private theorem integrable_classLikelihood_local
    {m n : ℕ} (code : Fin m → Coord n) (lam : ℝ) (i : Fin m) :
    Integrable (classLikelihood code lam i) (stdGaussian (Coord n)) := by
  let rho : Coord n → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (classLikelihood code lam i y)
  have hrho : Measurable rho := (measurable_classLikelihood_local code lam i).ennreal_ofReal
  have hmass : ∫⁻ y, rho y ∂stdGaussian (Coord n) = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply rho MeasurableSet.univ]
    rw [show (stdGaussian (Coord n)).withDensity rho =
        multivariateGaussian (lam • code i) (1 : Matrix (Fin n) (Fin n) ℝ) by
      simpa only [rho] using stdGaussian_withDensity_classLikelihood code lam i]
    simp only [measure_univ]
  have hrho_int : Integrable (fun y ↦ (rho y).toReal) (stdGaussian (Coord n)) :=
    integrable_toReal_of_lintegral_ne_top hrho.aemeasurable
      (by rw [hmass]; exact ENNReal.one_ne_top)
  have hrho_toReal : (fun y ↦ (rho y).toReal) = classLikelihood code lam i := by
    funext y
    simp only [rho, classLikelihood, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [← hrho_toReal]
  exact hrho_int

/-- Uniform-prior success probability of the deterministic ML decoder under shifted classes. -/
def decoderSuccess
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) : ℝ :=
  (1 / (m : ℝ)) *
    ∑ i, (multivariateGaussian (lam • code i) (1 : Matrix (Fin n) (Fin n) ℝ)
      {y | mlDecoder hm code lam y = i}).toReal

/-- The tie-safe operational ML success equals the density-maximum Bayes value. -/
theorem mlDecoder_success_eq_bayesValue
    {m n : ℕ} (hm : 0 < m) (code : Fin m → Coord n) (lam : ℝ) :
    decoderSuccess hm code lam = bayesValue hm code lam := by
  have hpartition := sum_withDensity_firstMaximizer_eq_integral_max
    hm (classLikelihood code lam)
    (fun i ↦ measurable_classLikelihood_local code lam i)
    (fun _ _ ↦ Real.exp_nonneg _)
    (stdGaussian (Coord n))
    (fun i ↦ integrable_classLikelihood_local code lam i)
  have hpartition' :
      ∑ i, (((stdGaussian (Coord n)).withDensity
            fun y ↦ ENNReal.ofReal (classLikelihood code lam i y))
          {y | mlDecoder hm code lam y = i}).toReal =
        ∫ y, classLikelihoodMax hm code lam y ∂stdGaussian (Coord n) := by
    simpa only [mlDecoder, finiteScoreMax, classLikelihoodMax] using hpartition
  unfold decoderSuccess bayesValue
  congr 1
  calc
    ∑ i, (multivariateGaussian (lam • code i) (1 : Matrix (Fin n) (Fin n) ℝ)
          {y | mlDecoder hm code lam y = i}).toReal =
        ∑ i, (((stdGaussian (Coord n)).withDensity
              fun y ↦ ENNReal.ofReal (classLikelihood code lam i y))
            {y | mlDecoder hm code lam y = i}).toReal := by
      apply Finset.sum_congr rfl
      intro i _
      rw [stdGaussian_withDensity_classLikelihood code lam i]
    _ = ∫ y, classLikelihoodMax hm code lam y ∂stdGaussian (Coord n) := hpartition'

end WeakSimplex
