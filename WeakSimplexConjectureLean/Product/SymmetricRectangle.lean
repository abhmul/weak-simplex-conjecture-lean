import WeakSimplexConjectureLean.LogConcavity.Indicators
import WeakSimplexConjectureLean.LogConcavity.Prekopa
import WeakSimplexConjectureLean.Vendor.StatLean.PiGaussian
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace WeakSimplex

def symmetricRectangle {m : ℕ} (r : Fin m → ℝ) : Set (Coord m) :=
  {x | ∀ i, x i ∈ Set.Icc (-r i) (r i)}

private def symmetricRectanglePi {m : ℕ} (r : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-r i) (r i)}

theorem measurableSet_symmetricRectangle {m : ℕ} (r : Fin m → ℝ) :
    MeasurableSet (symmetricRectangle r) := by
  rw [symmetricRectangle, Set.setOf_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact measurableSet_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

private theorem measurableSet_symmetricRectanglePi {m : ℕ} (r : Fin m → ℝ) :
    MeasurableSet (symmetricRectanglePi r) := by
  rw [symmetricRectanglePi, Set.setOf_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Icc.preimage (measurable_pi_apply i)

private theorem convex_symmetricRectangle {m : ℕ} (r : Fin m → ℝ) :
    Convex ℝ (symmetricRectangle r) := by
  intro x hx y hy a b ha hb hab i
  have hi := (convex_Icc (-r i) (r i)) (hx i) (hy i) ha hb hab
  simpa using hi

private theorem convex_symmetricRectanglePi {m : ℕ} (r : Fin m → ℝ) :
    Convex ℝ (symmetricRectanglePi r) := by
  intro x hx y hy a b ha hb hab i
  have hi := (convex_Icc (-r i) (r i)) (hx i) (hy i) ha hb hab
  simpa using hi

private theorem neg_mem_symmetricRectanglePi_iff
    {m : ℕ} {r : Fin m → ℝ} {x : Fin m → ℝ} :
    -x ∈ symmetricRectanglePi r ↔ x ∈ symmetricRectanglePi r := by
  constructor <;> intro hx i <;> constructor
  · simpa using neg_le_neg (hx i).2
  · simpa using neg_le_neg (hx i).1
  · simpa using neg_le_neg (hx i).2
  · simpa using neg_le_neg (hx i).1

private theorem neg_mem_symmetricRectangle_iff {m : ℕ} {r : Fin m → ℝ} {x : Coord m} :
    -x ∈ symmetricRectangle r ↔ x ∈ symmetricRectangle r := by
  constructor
  · intro hx i
    constructor
    · have := (hx i).2
      simpa using (neg_le_neg this)
    · have := (hx i).1
      simpa using (neg_le_neg this)
  · intro hx i
    constructor
    · have := (hx i).2
      simpa using (neg_le_neg this)
    · have := (hx i).1
      simpa using (neg_le_neg this)

private def gaussianShiftCLM {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) : (ℝ × (Fin k → ℝ)) →L[ℝ] (Fin n → ℝ) :=
  L.comp (ContinuousLinearMap.snd ℝ ℝ (Fin k → ℝ)) +
    (ContinuousLinearMap.fst ℝ ℝ (Fin k → ℝ)).smulRight b

private theorem convexIndicator_neg_eq
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_neg : ∀ x, -x ∈ C ↔ x ∈ C) (x : Fin n → ℝ) :
    convexIndicator C (-x) = convexIndicator C x := by
  by_cases hx : x ∈ C
  · have hnx : -x ∈ C := (hC_neg x).2 hx
    simp [convexIndicator, hx, hnx]
  · have hnx : -x ∉ C := fun h ↦ hx ((hC_neg x).1 h)
    simp [convexIndicator, hx, hnx]

private def gaussianKernelOne (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(x ^ 2) / 2))

private theorem measurable_gaussianKernelOne : Measurable gaussianKernelOne := by
  exact ((continuous_id.pow 2).neg.div_const 2).rexp.measurable.ennreal_ofReal

private theorem isLogConcave_gaussianKernelOne : IsLogConcave gaussianKernelOne := by
  intro t ht_pos ht_lt x y
  rw [gaussianKernelOne, gaussianKernelOne, gaussianKernelOne,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simp only [smul_eq_mul]
  have hrem : 0 ≤ t * (1 - t) * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg ht_pos.le (sub_nonneg.mpr ht_lt.le)) (sq_nonneg _)
  nlinarith

private theorem gaussianPDF_zero_one_eq_const_mul_kernel (x : ℝ) :
    gaussianPDF 0 1 x =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * gaussianKernelOne x := by
  rw [gaussianPDF, gaussianPDFReal_def, gaussianKernelOne]
  norm_num

private theorem isLogConcave_gaussianPDF_zero_one : IsLogConcave (gaussianPDF 0 1) := by
  have hEq : gaussianPDF 0 1 = fun x ↦
      ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * gaussianKernelOne x := by
    funext x
    exact gaussianPDF_zero_one_eq_const_mul_kernel x
  rw [hEq]
  change IsLogConcave
    ((fun _ : ℝ ↦ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹) * gaussianKernelOne)
  exact (isLogConcave_const (E := ℝ)
    (ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹)).mul isLogConcave_gaussianKernelOne

private theorem isLogConcave_finset_prod
    {ι E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset ι) {f : ι → E → ℝ≥0∞}
    (hf : ∀ i ∈ s, IsLogConcave (f i)) :
    IsLogConcave (fun x ↦ ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isLogConcave_const (E := E) 1)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      change IsLogConcave (f i * fun x ↦ ∏ j ∈ s, f j x)
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

private theorem isLogConcave_piGaussianDensity {m : ℕ} :
    IsLogConcave (fun x : Fin m → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) := by
  apply isLogConcave_finset_prod Finset.univ
  intro i hi t ht_pos ht_lt x y
  simpa using isLogConcave_gaussianPDF_zero_one ht_pos ht_lt (x i) (y i)

private def piGaussianDensity {m : ℕ} (x : Fin m → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

private theorem measurable_piGaussianDensity {m : ℕ} :
    Measurable (piGaussianDensity (m := m)) := by
  exact Finset.measurable_prod _ fun i _ ↦
    (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)

private theorem isLogConcave_piGaussianDensity' {m : ℕ} :
    IsLogConcave (piGaussianDensity (m := m)) :=
  isLogConcave_piGaussianDensity

@[simp]
private theorem gaussianPDF_zero_one_neg (x : ℝ) : gaussianPDF 0 1 (-x) = gaussianPDF 0 1 x := by
  simp [gaussianPDF, gaussianPDFReal_def]

@[simp]
private theorem piGaussianDensity_neg {m : ℕ} (x : Fin m → ℝ) :
    piGaussianDensity (-x) = piGaussianDensity x := by
  simp [piGaussianDensity]

private def piGaussianShiftMass {k n : ℕ}
    (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (C : Set (Fin n → ℝ)) (b : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x

private theorem measurable_isLogConcave_piGaussianShiftMass
    {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC_meas : MeasurableSet C) (hC_conv : Convex ℝ C)
    (b : Fin n → ℝ) :
    Measurable (piGaussianShiftMass L C b) ∧ IsLogConcave (piGaussianShiftMass L C b) := by
  change Measurable (fun t ↦
      ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x) ∧
    IsLogConcave (fun t ↦
      ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x)
  let F : ℝ → (Fin k → ℝ) → ℝ≥0∞ := fun t x ↦
    convexIndicator C (L x + t • b) * piGaussianDensity x
  have hF_meas : Measurable (Function.uncurry F) :=
    ((measurable_convexIndicator hC_meas).comp (gaussianShiftCLM L b).measurable).mul
      (measurable_piGaussianDensity.comp measurable_snd)
  have hF_lc : IsLogConcave (fun p : ℝ × (Fin k → ℝ) ↦ F p.1 p.2) :=
    ((isLogConcave_convexIndicator hC_conv).comp_affineMap
      (gaussianShiftCLM L b).toLinearMap.toAffineMap).mul
        (isLogConcave_piGaussianDensity'.comp_affineMap
          (ContinuousLinearMap.snd ℝ ℝ (Fin k → ℝ)).toLinearMap.toAffineMap)
  simpa only [F] using measurable_isLogConcave_lintegral_right hF_meas hF_lc

private theorem piGaussianShiftMass_even
    {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC_meas : MeasurableSet C)
    (hC_neg : ∀ x, -x ∈ C ↔ x ∈ C) (b : Fin n → ℝ) (t : ℝ) :
    piGaussianShiftMass L C b (-t) = piGaussianShiftMass L C b t := by
  let f : (Fin k → ℝ) → ℝ≥0∞ := fun x ↦
    convexIndicator C (L x + (-t) • b) * piGaussianDensity x
  have hf : Measurable f :=
    ((measurable_convexIndicator hC_meas).comp (L.measurable.add_const ((-t) • b))).mul
      measurable_piGaussianDensity
  have hneg := Measure.measurePreserving_neg (volume : Measure (Fin k → ℝ))
  change (∫⁻ x, f x) =
    ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x
  calc
    (∫⁻ x, f x) = ∫⁻ x, f (-x) := (hneg.lintegral_comp hf).symm
    _ = ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x := by
      apply lintegral_congr
      intro x
      have harg : L (-x) + (-t) • b = -(L x + t • b) := by simp [add_comm]
      simp only [f, harg, convexIndicator_neg_eq hC_neg, piGaussianDensity_neg]

private theorem piGaussianShiftMass_eq_measure
    {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC_meas : MeasurableSet C)
    (b : Fin n → ℝ) (t : ℝ)
    (hpi : Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity piGaussianDensity) :
    piGaussianShiftMass L C b t =
      Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) {x | L x + t • b ∈ C} := by
  have hS : MeasurableSet {x | L x + t • b ∈ C} :=
    (L.measurable.add_const (t • b)) hC_meas
  rw [piGaussianShiftMass, hpi, withDensity_apply piGaussianDensity hS,
    ← lintegral_indicator hS]
  apply lintegral_congr
  intro x
  by_cases hx : L x + t • b ∈ C
  · simp [convexIndicator, hx]
  · simp [convexIndicator, hx]

private def regressionResidualCLM {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Coord (n + 1) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    EuclideanSpace.proj (Fin.castSucc i) -
      R (Fin.castSucc i) (Fin.last n) • EuclideanSpace.proj (Fin.last n)

private def regressionSlope {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin n → ℝ :=
  fun i ↦ R (Fin.castSucc i) (Fin.last n)

private def regressionLastCLM {n : ℕ} : Coord (n + 1) →L[ℝ] (Unit → ℝ) :=
  ContinuousLinearMap.pi fun _ ↦ EuclideanSpace.proj (Fin.last n)

private def firstFunCLM {n : ℕ} : Coord (n + 1) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ EuclideanSpace.proj (Fin.castSucc i)

private def firstCoordCLM {n : ℕ} : Coord (n + 1) →L[ℝ] Coord n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp firstFunCLM

@[simp]
private theorem firstCoordCLM_apply {n : ℕ} (x : Coord (n + 1)) (i : Fin n) :
    firstCoordCLM x i = x (Fin.castSucc i) :=
  rfl

private theorem regression_reconstruct_first {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Coord (n + 1)) :
    regressionResidualCLM R x + x (Fin.last n) • regressionSlope R = firstFunCLM x := by
  ext i
  simp [regressionResidualCLM, regressionSlope, firstFunCLM]
  ring

private theorem mem_symmetricRectangle_succ_iff
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r : Fin (n + 1) → ℝ) (x : Coord (n + 1)) :
    x ∈ symmetricRectangle r ↔
      regressionResidualCLM R x + x (Fin.last n) • regressionSlope R ∈
          symmetricRectanglePi (fun i ↦ r (Fin.castSucc i)) ∧
        x (Fin.last n) ∈ Set.Icc (-r (Fin.last n)) (r (Fin.last n)) := by
  rw [regression_reconstruct_first]
  change (∀ i, x i ∈ Set.Icc (-r i) (r i)) ↔
    (∀ i : Fin n, x (Fin.castSucc i) ∈
      Set.Icc (-r (Fin.castSucc i)) (r (Fin.castSucc i))) ∧
      x (Fin.last n) ∈ Set.Icc (-r (Fin.last n)) (r (Fin.last n))
  exact Fin.forall_fin_succ'

private theorem map_firstCoord_multivariateGaussian_zero
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) :
    Measure.map firstCoordCLM (multivariateGaussian (0 : Coord (n + 1)) R) =
      multivariateGaussian (0 : Coord n) (R.submatrix Fin.castSucc Fin.castSucc) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
    · simp
    · exact IsGaussian.integrable_id
        (μ := multivariateGaussian (0 : Coord (n + 1)) R)
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hi : (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) u) ∘
        firstCoordCLM = fun u : Coord (n + 1) ↦ u (Fin.castSucc i) := by
      ext u
      simp [PiLp.inner_apply]
    have hj : (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j) u) ∘
        firstCoordCLM = fun u : Coord (n + 1) ↦ u (Fin.castSucc j) := by
      ext u
      simp [PiLp.inner_apply]
    rw [hi, hj, covariance_eval_multivariateGaussian hR,
      covarianceBilin_multivariateGaussian (hR.submatrix Fin.castSucc)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

private def multivariateGaussianSourceCLM {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] Coord (n + 1) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)).comp
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap

private def regressionSourceCLM {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (regressionResidualCLM R).comp (multivariateGaussianSourceCLM R)

private theorem map_regressionResidual_multivariateGaussian_zero
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Measure.map (regressionResidualCLM R)
      (multivariateGaussian (0 : Coord (n + 1)) R) =
    Measure.map (regressionSourceCLM R)
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) := by
  rw [multivariateGaussian]
  simp only [zero_add]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

private def regressionShiftMass {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Measure.map (regressionResidualCLM R)
    (multivariateGaussian (0 : Coord (n + 1)) R))
      {y | y + t • regressionSlope R ∈ symmetricRectanglePi r}

private theorem regressionShiftMass_eq_piGaussianShiftMass
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ)
    (t : ℝ)
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity) :
    regressionShiftMass R r t =
      piGaussianShiftMass (regressionSourceCLM R) (symmetricRectanglePi r)
        (regressionSlope R) t := by
  have hS : MeasurableSet {y | y + t • regressionSlope R ∈ symmetricRectanglePi r} :=
    (measurable_id.add_const (t • regressionSlope R))
      (measurableSet_symmetricRectanglePi r)
  rw [regressionShiftMass, map_regressionResidual_multivariateGaussian_zero R,
    Measure.map_apply (regressionSourceCLM R).measurable hS]
  exact (piGaussianShiftMass_eq_measure (regressionSourceCLM R)
    (measurableSet_symmetricRectanglePi r) (regressionSlope R) t hpi).symm

private theorem measurable_isLogConcave_regressionShiftMass
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ)
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity) :
    Measurable (regressionShiftMass R r) ∧ IsLogConcave (regressionShiftMass R r) := by
  have heq : regressionShiftMass R r =
      piGaussianShiftMass (regressionSourceCLM R) (symmetricRectanglePi r)
        (regressionSlope R) := by
    funext t
    exact regressionShiftMass_eq_piGaussianShiftMass R r t hpi
  rw [heq]
  exact measurable_isLogConcave_piGaussianShiftMass (regressionSourceCLM R)
    (measurableSet_symmetricRectanglePi r) (convex_symmetricRectanglePi r)
    (regressionSlope R)

private theorem regressionShiftMass_even
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ)
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity)
    (t : ℝ) : regressionShiftMass R r (-t) = regressionShiftMass R r t := by
  rw [regressionShiftMass_eq_piGaussianShiftMass R r (-t) hpi,
    regressionShiftMass_eq_piGaussianShiftMass R r t hpi]
  exact piGaussianShiftMass_even (regressionSourceCLM R)
    (measurableSet_symmetricRectanglePi r)
    (fun x ↦ neg_mem_symmetricRectanglePi_iff) (regressionSlope R) t

private theorem prod_shift_inter_eq_setLIntegral
    {n : ℕ} (ν : Measure (Fin n → ℝ)) [SFinite ν] (γ : Measure ℝ) [SFinite γ]
    {C : Set (Fin n → ℝ)} (hC : MeasurableSet C) (b : Fin n → ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ν.prod γ {p | p.1 + p.2 • b ∈ C ∧ p.2 ∈ A} =
      ∫⁻ t in A, ν {y | y + t • b ∈ C} ∂γ := by
  have hshift : Measurable (fun p : (Fin n → ℝ) × ℝ ↦ p.1 + p.2 • b) := by
    fun_prop
  have hS : MeasurableSet {p : (Fin n → ℝ) × ℝ |
      p.1 + p.2 • b ∈ C ∧ p.2 ∈ A} :=
    (hC.preimage hshift).inter (hA.preimage measurable_snd)
  rw [Measure.prod_apply_symm hS, ← lintegral_indicator hA]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ A
  · rw [Set.indicator_of_mem ht]
    congr 1
    ext y
    simp [ht]
  · rw [Set.indicator_of_notMem ht]
    simp [ht]

private theorem regressionResidual_indep_last
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    IndepFun (regressionResidualCLM R) regressionLastCLM
      (multivariateGaussian (0 : Coord (n + 1)) R) := by
  let μ := multivariateGaussian (0 : Coord (n + 1)) R
  have hId : HasGaussianLaw (id : Coord (n + 1) → Coord (n + 1)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hPair := hId.map ((regressionResidualCLM R).prod regressionLastCLM)
  apply hPair.indepFun_of_covariance_eval
  intro i j
  have hcoord (k : Fin (n + 1)) : MemLp (fun x : Coord (n + 1) ↦ x k) 2 μ := by
    simpa only [Function.comp_id, EuclideanSpace.coe_proj] using
      (hId.map (EuclideanSpace.proj k)).memLp_two
  change cov[
      (fun x : Coord (n + 1) ↦
        x (Fin.castSucc i) - R (Fin.castSucc i) (Fin.last n) * x (Fin.last n)),
      (fun x : Coord (n + 1) ↦ x (Fin.last n)); μ] = 0
  rw [covariance_fun_sub_left (hcoord _) ((hcoord _).const_mul _) (hcoord _),
    covariance_const_mul_left, covariance_eval_multivariateGaussian hR,
    covariance_eval_multivariateGaussian hR, hdiag]
  ring

private theorem regressionResidual_indep_lastScalar
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    IndepFun (regressionResidualCLM R) (fun x : Coord (n + 1) ↦ x (Fin.last n))
      (multivariateGaussian (0 : Coord (n + 1)) R) := by
  have h := (regressionResidual_indep_last hR hdiag).comp
    measurable_id (measurable_pi_apply ())
  simpa [Function.comp_def, regressionLastCLM] using h

private theorem map_last_multivariateGaussian_zero
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    Measure.map (fun x : Coord (n + 1) ↦ x (Fin.last n))
      (multivariateGaussian (0 : Coord (n + 1)) R) = gaussianReal 0 1 := by
  have h := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord (n + 1))) hR (i := Fin.last n)).map_eq
  simpa [hdiag] using h

private theorem map_regressionResidual_last_eq_prod
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    Measure.map
      (fun x : Coord (n + 1) ↦ (regressionResidualCLM R x, x (Fin.last n)))
      (multivariateGaussian (0 : Coord (n + 1)) R) =
    (Measure.map (regressionResidualCLM R)
      (multivariateGaussian (0 : Coord (n + 1)) R)).prod (gaussianReal 0 1) := by
  have h := (regressionResidual_indep_lastScalar hR hdiag).map_prod_eq_prod_map_map
    (regressionResidualCLM R).measurable.aemeasurable
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable.aemeasurable
  have hlast : Measure.map (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n))
      (multivariateGaussian (0 : Coord (n + 1)) R) = gaussianReal 0 1 := by
    simpa only [EuclideanSpace.coe_proj] using
      map_last_multivariateGaussian_zero hR hdiag
  rw [hlast] at h
  simpa only [EuclideanSpace.coe_proj] using h

private theorem multivariateGaussian_symmetricRectangle_eq_setLIntegral_regressionShiftMass
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (r : Fin (n + 1) → ℝ) :
    multivariateGaussian (0 : Coord (n + 1)) R (symmetricRectangle r) =
      ∫⁻ t in Set.Icc (-r (Fin.last n)) (r (Fin.last n)),
        regressionShiftMass R (fun i ↦ r (Fin.castSucc i)) t ∂gaussianReal 0 1 := by
  let μ := multivariateGaussian (0 : Coord (n + 1)) R
  let ν := Measure.map (regressionResidualCLM R) μ
  let A := Set.Icc (-r (Fin.last n)) (r (Fin.last n))
  let C := symmetricRectanglePi (fun i : Fin n ↦ r (Fin.castSucc i))
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 + p.2 • regressionSlope R ∈ C ∧ p.2 ∈ A}
  let J : Coord (n + 1) → (Fin n → ℝ) × ℝ := fun x ↦
    (regressionResidualCLM R x, x (Fin.last n))
  have hJ : Measurable J := by
    exact (regressionResidualCLM R).measurable.prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable
  have hS : MeasurableSet S := by
    exact ((measurableSet_symmetricRectanglePi _).preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage measurable_snd)
  have hpre : J ⁻¹' S = symmetricRectangle r := by
    ext x
    simpa only [J, S, C, A, Set.mem_preimage, Set.mem_setOf_eq] using
      (mem_symmetricRectangle_succ_iff R r x).symm
  calc
    μ (symmetricRectangle r) = μ (J ⁻¹' S) := by rw [hpre]
    _ = Measure.map J μ S := (Measure.map_apply hJ hS).symm
    _ = ν.prod (gaussianReal 0 1) S := by
      simpa only [μ, ν, J] using congrArg
        (fun m : Measure ((Fin n → ℝ) × ℝ) ↦ m S)
        (map_regressionResidual_last_eq_prod hR hdiag)
    _ = ∫⁻ t in A, ν {y | y + t • regressionSlope R ∈ C} ∂gaussianReal 0 1 := by
      exact prod_shift_inter_eq_setLIntegral ν (gaussianReal 0 1)
        (measurableSet_symmetricRectanglePi _) (regressionSlope R) measurableSet_Icc
    _ = ∫⁻ t in Set.Icc (-r (Fin.last n)) (r (Fin.last n)),
        regressionShiftMass R (fun i ↦ r (Fin.castSucc i)) t ∂gaussianReal 0 1 := by
      rfl

private theorem lintegral_regressionShiftMass_eq_marginal_symmetricRectangle
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (r : Fin n → ℝ) :
    (∫⁻ t, regressionShiftMass R r t ∂gaussianReal 0 1) =
      multivariateGaussian (0 : Coord n) (R.submatrix Fin.castSucc Fin.castSucc)
        (symmetricRectangle r) := by
  let μ := multivariateGaussian (0 : Coord (n + 1)) R
  let ν := Measure.map (regressionResidualCLM R) μ
  let C := symmetricRectanglePi r
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 + p.2 • regressionSlope R ∈ C}
  let J : Coord (n + 1) → (Fin n → ℝ) × ℝ := fun x ↦
    (regressionResidualCLM R x, x (Fin.last n))
  have hJ : Measurable J := by
    exact (regressionResidualCLM R).measurable.prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable
  have hS : MeasurableSet S := by
    exact (measurableSet_symmetricRectanglePi _).preimage (by fun_prop)
  have hpre : J ⁻¹' S = firstCoordCLM ⁻¹' symmetricRectangle r := by
    ext x
    change regressionResidualCLM R x + x (Fin.last n) • regressionSlope R ∈
        symmetricRectanglePi r ↔ firstCoordCLM x ∈ symmetricRectangle r
    rw [regression_reconstruct_first]
    rfl
  have hSuniv :
      {p : (Fin n → ℝ) × ℝ |
          p.1 + p.2 • regressionSlope R ∈ C ∧ p.2 ∈ Set.univ} = S := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true, S]
  calc
    (∫⁻ t, regressionShiftMass R r t ∂gaussianReal 0 1) =
        ∫⁻ t in Set.univ, ν {y | y + t • regressionSlope R ∈ C}
          ∂gaussianReal 0 1 := by
      simp only [Measure.restrict_univ, regressionShiftMass, ν, μ, C]
    _ = ν.prod (gaussianReal 0 1)
        {p | p.1 + p.2 • regressionSlope R ∈ C ∧ p.2 ∈ Set.univ} := by
      exact (prod_shift_inter_eq_setLIntegral ν (gaussianReal 0 1)
        (measurableSet_symmetricRectanglePi _) (regressionSlope R)
        MeasurableSet.univ).symm
    _ = ν.prod (gaussianReal 0 1) S := by rw [hSuniv]
    _ = Measure.map J μ S := by
      simpa only [μ, ν, J] using congrArg
        (fun m : Measure ((Fin n → ℝ) × ℝ) ↦ m S)
        (map_regressionResidual_last_eq_prod hR hdiag).symm
    _ = μ (J ⁻¹' S) := Measure.map_apply hJ hS
    _ = μ (firstCoordCLM ⁻¹' symmetricRectangle r) := by rw [hpre]
    _ = Measure.map firstCoordCLM μ (symmetricRectangle r) :=
      (Measure.map_apply firstCoordCLM.measurable
        (measurableSet_symmetricRectangle r)).symm
    _ = multivariateGaussian (0 : Coord n)
        (R.submatrix Fin.castSucc Fin.castSucc) (symmetricRectangle r) := by
      simpa only [μ] using congrArg
        (fun m : Measure (Coord n) ↦ m (symmetricRectangle r))
        (map_firstCoord_multivariateGaussian_zero hR)

private theorem measure_mul_lintegral_le_setLIntegral_of_threshold
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {A : Set α} (hA : MeasurableSet A) {q : α → ℝ≥0∞} (hq : Measurable q)
    {c : ℝ≥0∞} (hinside : ∀ x ∈ A, c ≤ q x)
    (houtside : ∀ x ∉ A, q x ≤ c) :
    μ A * (∫⁻ x, q x ∂μ) ≤ ∫⁻ x in A, q x ∂μ := by
  have hI : c * μ A ≤ ∫⁻ x in A, q x ∂μ := by
    simpa using setLIntegral_mono hq hinside
  have hJ : (∫⁻ x in Aᶜ, q x ∂μ) ≤ c * μ Aᶜ := by
    simpa using setLIntegral_mono measurable_const
      (fun x hx ↦ houtside x (by simpa using hx))
  rw [← lintegral_add_compl q hA]
  calc
    μ A * ((∫⁻ x in A, q x ∂μ) + ∫⁻ x in Aᶜ, q x ∂μ) =
        μ A * (∫⁻ x in A, q x ∂μ) + μ A * (∫⁻ x in Aᶜ, q x ∂μ) :=
      mul_add _ _ _
    _ ≤ μ A * (∫⁻ x in A, q x ∂μ) + μ A * (c * μ Aᶜ) := by
      gcongr
    _ = μ A * (∫⁻ x in A, q x ∂μ) + (c * μ A) * μ Aᶜ := by
      ac_rfl
    _ ≤ μ A * (∫⁻ x in A, q x ∂μ) + (∫⁻ x in A, q x ∂μ) * μ Aᶜ := by
      gcongr
    _ = (∫⁻ x in A, q x ∂μ) * (μ A + μ Aᶜ) := by
      rw [mul_add]
      ac_rfl
    _ = ∫⁻ x in A, q x ∂μ := by
      rw [measure_add_measure_compl hA, measure_univ, mul_one]

private theorem IsLogConcave.antitoneOn_nonneg_of_even
    {q : ℝ → ℝ≥0∞} (hq : IsLogConcave q) (heven : ∀ x, q (-x) = q x) :
    AntitoneOn q (Set.Ici 0) := by
  intro x hx y hy hxy
  by_cases hxy' : x = y
  · simp [hxy']
  have hxy_strict : x < y := lt_of_le_of_ne hxy hxy'
  have hy_pos : 0 < y := lt_of_le_of_lt hx hxy_strict
  let a : ℝ := (1 + x / y) / 2
  have hratio_nonneg : 0 ≤ x / y := div_nonneg hx hy_pos.le
  have hratio_lt : x / y < 1 := (div_lt_one hy_pos).mpr hxy_strict
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_lt : a < 1 := by
    dsimp [a]
    linarith
  have hcomb : a • y + (1 - a) • (-y) = x := by
    dsimp [a]
    field_simp [ne_of_gt hy_pos]
    all_goals ring
  have h := hq ha_pos ha_lt y (-y)
  rw [heven] at h
  have hpow : q y ^ a * q y ^ (1 - a) = q y := by
    rw [← ENNReal.rpow_add_of_nonneg a (1 - a) ha_pos.le (sub_nonneg.mpr ha_lt.le)]
    norm_num
  rw [hpow, hcomb] at h
  exact h

private theorem measure_Icc_mul_lintegral_le_setLIntegral_of_even_logConcave
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ → ℝ≥0∞}
    (hq_meas : Measurable q) (hq_lc : IsLogConcave q)
    (hq_even : ∀ x, q (-x) = q x) {r : ℝ} (hr : 0 ≤ r) :
    μ (Set.Icc (-r) r) * (∫⁻ x, q x ∂μ) ≤
      ∫⁻ x in Set.Icc (-r) r, q x ∂μ := by
  have hanti := hq_lc.antitoneOn_nonneg_of_even hq_even
  have habs (x : ℝ) : q |x| = q x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos (le_of_not_ge hx), hq_even]
  apply measure_mul_lintegral_le_setLIntegral_of_threshold μ measurableSet_Icc hq_meas
    (c := q r)
  · intro x hx
    rw [← habs x]
    exact hanti (abs_nonneg x) hr ((abs_le).2 hx)
  · intro x hx
    rw [← habs x]
    have hnot : ¬ |x| ≤ r := fun h ↦ hx ((abs_le).1 h)
    exact hanti hr (abs_nonneg x) (lt_of_not_ge hnot).le

private theorem symmetricRectangle_step
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (r : Fin (n + 1) → ℝ) (hrlast : 0 ≤ r (Fin.last n))
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity) :
    gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) *
        multivariateGaussian (0 : Coord n) (R.submatrix Fin.castSucc Fin.castSucc)
          (symmetricRectangle (fun i ↦ r (Fin.castSucc i))) ≤
      multivariateGaussian (0 : Coord (n + 1)) R (symmetricRectangle r) := by
  let q := regressionShiftMass R (fun i ↦ r (Fin.castSucc i))
  have hq := measurable_isLogConcave_regressionShiftMass R
    (fun i ↦ r (Fin.castSucc i)) hpi
  have hineq := measure_Icc_mul_lintegral_le_setLIntegral_of_even_logConcave
    (gaussianReal 0 1) hq.1 hq.2
      (regressionShiftMass_even R (fun i ↦ r (Fin.castSucc i)) hpi) hrlast
  change gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) *
      (∫⁻ t, q t ∂gaussianReal 0 1) ≤
        ∫⁻ t in Set.Icc (-r (Fin.last n)) (r (Fin.last n)),
          q t ∂gaussianReal 0 1 at hineq
  rw [lintegral_regressionShiftMass_eq_marginal_symmetricRectangle hR hdiag] at hineq
  rw [← multivariateGaussian_symmetricRectangle_eq_setLIntegral_regressionShiftMass
    hR hdiag r] at hineq
  exact hineq

private theorem symmetricRectangle_ge_iid_of_posDef_conditional
    (hpi : ∀ k : ℕ, Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity piGaussianDensity)
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (∏ i, gaussianReal 0 1 (Set.Icc (-r i) (r i))) ≤
      multivariateGaussian (0 : Coord m) R (symmetricRectangle r) := by
  induction m with
  | zero =>
      have hrect : symmetricRectangle r = Set.univ := by
        ext x
        simp [symmetricRectangle]
      rw [hrect, measure_univ]
      simp
  | succ n ih =>
      let R' := R.submatrix Fin.castSucc Fin.castSucc
      let r' : Fin n → ℝ := fun i ↦ r (Fin.castSucc i)
      have hR' : R'.PosDef := hR.submatrix (Fin.castSucc_injective n)
      have hdiag' : ∀ i, R' i i = 1 := fun i ↦ hdiag (Fin.castSucc i)
      have hr' : ∀ i, 0 ≤ r' i := fun i ↦ hr (Fin.castSucc i)
      have hind := ih R' hR' hdiag' r' hr'
      have hstep := symmetricRectangle_step hR.posSemidef hdiag r
        (hr (Fin.last n)) (hpi (n + 1))
      rw [Fin.prod_univ_castSucc]
      calc
        (∏ i : Fin n, gaussianReal 0 1 (Set.Icc (-r (Fin.castSucc i))
              (r (Fin.castSucc i)))) *
            gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) =
            gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) *
              (∏ i : Fin n, gaussianReal 0 1
                (Set.Icc (-r' i) (r' i))) := by
          simp only [r']
          ac_rfl
        _ ≤ gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) *
              multivariateGaussian (0 : Coord n) R' (symmetricRectangle r') :=
          by gcongr
        _ ≤ multivariateGaussian (0 : Coord (n + 1)) R
              (symmetricRectangle r) := by
          simpa only [R', r'] using hstep

theorem symmetricRectangle_ge_iid_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (∏ i, gaussianReal 0 1 (Set.Icc (-r i) (r i))) ≤
      multivariateGaussian (0 : Coord m) R (symmetricRectangle r) := by
  apply symmetricRectangle_ge_iid_of_posDef_conditional
    (fun k ↦ ?_) R hR hdiag r hr
  change Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) =
    (volume : Measure (Fin k → ℝ)).withDensity
      (fun x ↦ ∏ i, gaussianPDF 0 1 (x i))
  exact WeakSimplex.Vendor.StatLean.AsymptoticStatistics.pi_gaussianReal_eq_withDensity


end WeakSimplex
