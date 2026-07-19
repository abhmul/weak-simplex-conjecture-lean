import WeakSimplexConjectureLean.Orthant.Singular
import WeakSimplexConjectureLean.Product.ContinuousCenteredProduct
import WeakSimplexConjectureLean.Product.SumDifference
import WeakSimplexConjectureLean.Product.SymmetricRectangle
import WeakSimplexConjectureLean.Tilt.NormalizedTiltedHalfLine
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Strict product comparison for adaptive half-lines

This module applies strict symmetric-rectangle comparison inside the sum--difference rotation and
uses the continuous-factor centered product theorem for the resulting self-convolutions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace WeakSimplex

private def tiltedRadius (s u : ℝ) : ℝ :=
  Real.sqrt 2 * H s - u

private def tiltedAmplitude (s u : ℝ) : ℝ :=
  (∫ z, centeredTiltedHalfLine s z ∂gaussianReal 0 1)⁻¹ ^ 2 *
    Real.exp (Real.sqrt 2 * r s * u)

private lemma tiltedAmplitude_pos (s u : ℝ) :
    0 < tiltedAmplitude s u := by
  exact mul_pos (pow_pos (inv_pos.mpr (integral_centeredTiltedHalfLine_pos s)) 2)
    (Real.exp_pos _)

private lemma fixedAverageFactor_normalizedCenteredTiltedHalfLine
    (s u v : ℝ) :
    fixedAverageFactor (normalizedCenteredTiltedHalfLine s) u v =
      (Set.Icc (-(tiltedRadius s u)) (tiltedRadius s u)).indicator
        (fun _ ↦ tiltedAmplitude s u) v := by
  simpa only [fixedAverageFactor, tiltedRadius, tiltedAmplitude, neg_sub] using
    normalizedCenteredTiltedHalfLine_product s u v

private lemma sumDifferenceProduct_normalizedCenteredTiltedHalfLine
    {m : ℕ} (s : Coord m) (u v : Coord m) :
    sumDifferenceProduct (fun i ↦ normalizedCenteredTiltedHalfLine (s i)) (u, v) =
      (symmetricRectangle (fun i ↦ tiltedRadius (s i) (u i))).indicator
        (fun _ ↦ ∏ i, tiltedAmplitude (s i) (u i)) v := by
  classical
  by_cases hv : v ∈ symmetricRectangle (fun i ↦ tiltedRadius (s i) (u i))
  · rw [Set.indicator_of_mem hv]
    simp only [sumDifferenceProduct]
    apply Finset.prod_congr rfl
    intro i hi
    rw [fixedAverageFactor_normalizedCenteredTiltedHalfLine,
      Set.indicator_of_mem (hv i)]
  · rw [Set.indicator_of_notMem hv]
    simp only [sumDifferenceProduct]
    simp only [symmetricRectangle, Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨i, hi⟩ := hv
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [fixedAverageFactor_normalizedCenteredTiltedHalfLine,
      Set.indicator_of_notMem hi]

private lemma integral_fixedAverageFactor_normalizedCenteredTiltedHalfLine
    (s u : ℝ) :
    (∫ v, fixedAverageFactor (normalizedCenteredTiltedHalfLine s) u v
        ∂gaussianReal 0 1) =
      (gaussianReal 0 1 (Set.Icc (-(tiltedRadius s u)) (tiltedRadius s u))).toReal *
        tiltedAmplitude s u := by
  rw [show fixedAverageFactor (normalizedCenteredTiltedHalfLine s) u =
      (Set.Icc (-(tiltedRadius s u)) (tiltedRadius s u)).indicator
        (fun _ ↦ tiltedAmplitude s u) by
    funext v
    exact fixedAverageFactor_normalizedCenteredTiltedHalfLine s u v]
  simpa only [measureReal_def, smul_eq_mul] using
    integral_indicator_const (μ := gaussianReal 0 1) (tiltedAmplitude s u)
      measurableSet_Icc

private lemma integral_sumDifferenceProduct_normalizedCenteredTiltedHalfLine
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (s u : Coord m) :
    (∫ v, sumDifferenceProduct (fun i ↦ normalizedCenteredTiltedHalfLine (s i)) (u, v)
        ∂multivariateGaussian (0 : Coord m) R) =
      (multivariateGaussian (0 : Coord m) R
          (symmetricRectangle (fun i ↦ tiltedRadius (s i) (u i)))).toReal *
        ∏ i, tiltedAmplitude (s i) (u i) := by
  rw [show (fun v ↦
      sumDifferenceProduct (fun i ↦ normalizedCenteredTiltedHalfLine (s i)) (u, v)) =
      (symmetricRectangle (fun i ↦ tiltedRadius (s i) (u i))).indicator
        (fun _ ↦ ∏ i, tiltedAmplitude (s i) (u i)) by
    funext v
    exact sumDifferenceProduct_normalizedCenteredTiltedHalfLine s u v]
  simpa only [measureReal_def, smul_eq_mul] using
    integral_indicator_const (μ := multivariateGaussian (0 : Coord m) R)
      (∏ i, tiltedAmplitude (s i) (u i))
      (measurableSet_symmetricRectangle fun i ↦ tiltedRadius (s i) (u i))

private lemma fixedAverage_pointwise_le
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R)
    (s u : Coord m) :
    (∏ i, normalizedSelfConvolution (normalizedCenteredTiltedHalfLine (s i)) (u i)) ≤
      ∫ v, sumDifferenceProduct (fun i ↦ normalizedCenteredTiltedHalfLine (s i))
        (u, v) ∂multivariateGaussian (0 : Coord m) R := by
  classical
  let rad : Fin m → ℝ := fun i ↦ tiltedRadius (s i) (u i)
  let amp : Fin m → ℝ := fun i ↦ tiltedAmplitude (s i) (u i)
  by_cases hrad : ∀ i, 0 ≤ rad i
  · have hrect := symmetricRectangle_ge_iid R hR rad hrad
    have hreal :
        (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))).toReal ≤
          (multivariateGaussian (0 : Coord m) R (symmetricRectangle rad)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hrect
    have hamp_nonneg : 0 ≤ ∏ i, amp i :=
      (Finset.prod_pos fun i _ ↦ tiltedAmplitude_pos (s i) (u i)).le
    calc
      (∏ i, normalizedSelfConvolution
          (normalizedCenteredTiltedHalfLine (s i)) (u i)) =
          ∏ i, ∫ v,
            fixedAverageFactor (normalizedCenteredTiltedHalfLine (s i)) (u i) v
              ∂gaussianReal 0 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (integral_fixedAverageFactor_eq_normalizedSelfConvolution
          (measurable_normalizedCenteredTiltedHalfLine (s i))
          (normalizedCenteredTiltedHalfLine_nonneg (s i))
          (isBounded_range_normalizedCenteredTiltedHalfLine (s i)) (u i)).symm
      _ = ∏ i, (gaussianReal 0 1 (Set.Icc (-rad i) (rad i))).toReal * amp i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact integral_fixedAverageFactor_normalizedCenteredTiltedHalfLine (s i) (u i)
      _ = (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))).toReal *
          ∏ i, amp i := by
        rw [ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
      _ ≤ (multivariateGaussian (0 : Coord m) R (symmetricRectangle rad)).toReal *
          ∏ i, amp i := mul_le_mul_of_nonneg_right hreal hamp_nonneg
      _ = ∫ v, sumDifferenceProduct
          (fun i ↦ normalizedCenteredTiltedHalfLine (s i)) (u, v)
            ∂multivariateGaussian (0 : Coord m) R := by
        exact (integral_sumDifferenceProduct_normalizedCenteredTiltedHalfLine R s u).symm
  · simp only [not_forall] at hrad
    obtain ⟨i, hi⟩ := hrad
    have hirad : rad i < -rad i := by linarith
    have hzero : normalizedSelfConvolution
        (normalizedCenteredTiltedHalfLine (s i)) (u i) = 0 := by
      rw [← integral_fixedAverageFactor_eq_normalizedSelfConvolution
        (measurable_normalizedCenteredTiltedHalfLine (s i))
        (normalizedCenteredTiltedHalfLine_nonneg (s i))
        (isBounded_range_normalizedCenteredTiltedHalfLine (s i)) (u i),
        integral_fixedAverageFactor_normalizedCenteredTiltedHalfLine,
        Set.Icc_eq_empty (not_le_of_gt hirad), measure_empty, ENNReal.toReal_zero,
        zero_mul]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
    exact integral_nonneg fun v ↦ Finset.prod_nonneg fun j _ ↦
      mul_nonneg
        (normalizedCenteredTiltedHalfLine_nonneg (s j) ((u j + v j) / Real.sqrt 2))
        (normalizedCenteredTiltedHalfLine_nonneg (s j) ((u j - v j) / Real.sqrt 2))

private lemma fixedAverage_pointwise_lt
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ)) (s u : Coord m)
    (hrad : ∀ i, 0 < tiltedRadius (s i) (u i)) :
    (∏ i, normalizedSelfConvolution (normalizedCenteredTiltedHalfLine (s i)) (u i)) <
      ∫ v, sumDifferenceProduct (fun i ↦ normalizedCenteredTiltedHalfLine (s i))
        (u, v) ∂multivariateGaussian (0 : Coord m) R := by
  classical
  let rad : Fin m → ℝ := fun i ↦ tiltedRadius (s i) (u i)
  let amp : Fin m → ℝ := fun i ↦ tiltedAmplitude (s i) (u i)
  have hrect := symmetricRectangle_gt_iid_of_ne_one R hR hRne rad hrad
  have hleft_ne_top : (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))) ≠ ∞ := by
    exact ENNReal.prod_ne_top fun i hi ↦ measure_ne_top _ _
  have hreal :
      (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))).toReal <
        (multivariateGaussian (0 : Coord m) R (symmetricRectangle rad)).toReal :=
    (ENNReal.toReal_lt_toReal hleft_ne_top (measure_ne_top _ _)).2 hrect
  have hamp_pos : 0 < ∏ i, amp i :=
    Finset.prod_pos fun i _ ↦ tiltedAmplitude_pos (s i) (u i)
  calc
    (∏ i, normalizedSelfConvolution
        (normalizedCenteredTiltedHalfLine (s i)) (u i)) =
        ∏ i, ∫ v,
          fixedAverageFactor (normalizedCenteredTiltedHalfLine (s i)) (u i) v
            ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (integral_fixedAverageFactor_eq_normalizedSelfConvolution
        (measurable_normalizedCenteredTiltedHalfLine (s i))
        (normalizedCenteredTiltedHalfLine_nonneg (s i))
        (isBounded_range_normalizedCenteredTiltedHalfLine (s i)) (u i)).symm
    _ = ∏ i, (gaussianReal 0 1 (Set.Icc (-rad i) (rad i))).toReal * amp i := by
      apply Finset.prod_congr rfl
      intro i hi
      exact integral_fixedAverageFactor_normalizedCenteredTiltedHalfLine (s i) (u i)
    _ = (∏ i, gaussianReal 0 1 (Set.Icc (-rad i) (rad i))).toReal *
        ∏ i, amp i := by
      rw [ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
    _ < (multivariateGaussian (0 : Coord m) R (symmetricRectangle rad)).toReal *
        ∏ i, amp i := mul_lt_mul_of_pos_right hreal hamp_pos
    _ = ∫ v, sumDifferenceProduct
        (fun i ↦ normalizedCenteredTiltedHalfLine (s i)) (u, v)
          ∂multivariateGaussian (0 : Coord m) R := by
      exact (integral_sumDifferenceProduct_normalizedCenteredTiltedHalfLine R s u).symm

private def strictAverageSet {m : ℕ} (s : Coord m) : Set (Coord m) :=
  {u | ∀ i, 0 < tiltedRadius (s i) (u i)}

private lemma measure_strictAverageSet_pos
    {m : ℕ} (hm : 0 < m) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (s : Coord m) :
    0 < multivariateGaussian (0 : Coord m) R (strictAverageSet s) := by
  have hsub : lowerOrthant (m := m) 0 ⊆ strictAverageSet s := by
    intro u hu i
    have hthreshold : 0 < Real.sqrt 2 * H (s i) :=
      mul_pos (Real.sqrt_pos.2 (by norm_num)) (H_pos (s i))
    exact sub_pos.mpr (lt_of_le_of_lt (hu i) hthreshold)
  have hiid : 0 < (gaussianReal 0 1) (Set.Iic 0) ^ m := by
    rw [← normalCDF_eq_measure_Iic]
    rw [pos_iff_ne_zero]
    exact pow_ne_zero m (ENNReal.ofReal_ne_zero_iff.2 (normalCDF_pos 0))
  exact hiid.trans_le ((lowerOrthant_ge_iid hm R hR 0).trans
    (measure_mono hsub))

private lemma integrable_coordinateProduct
    {m : ℕ} {μ : Measure (Coord m)} [IsFiniteMeasure μ]
    (f : Fin m → ℝ → ℝ) (hf_meas : ∀ i, Measurable (f i))
    (hf_bounded : ∀ i, Bornology.IsBounded (Set.range (f i))) :
    Integrable (fun x : Coord m ↦ ∏ i, f i (x i)) μ := by
  classical
  choose C hC using fun i ↦ (hf_bounded i).exists_norm_le
  have hcoord_meas (i : Fin m) : Measurable (fun x : Coord m ↦ f i (x i)) :=
    (hf_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable
  have hcoord_bound (i : Fin m) : ∀ x : Coord m, ‖f i (x i)‖ ≤ C i :=
    fun x ↦ hC i (f i (x i)) (Set.mem_range_self (x i))
  have hproduct_int_finset (t : Finset (Fin m)) :
      Integrable (fun x : Coord m ↦ ∏ i ∈ t, f i (x i)) μ := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ht =>
        have hmul := ht.bdd_mul (hcoord_meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall (hcoord_bound i))
        simpa [Finset.prod_insert hi] using hmul
  simpa using hproduct_int_finset Finset.univ

private lemma integrable_sumDifferenceProduct_normalizedCenteredTiltedHalfLine
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (s : Coord m) :
    Integrable
      (sumDifferenceProduct (fun i ↦ normalizedCenteredTiltedHalfLine (s i)))
      ((multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R)) := by
  classical
  let h : Fin m → ℝ → ℝ := fun i ↦ normalizedCenteredTiltedHalfLine (s i)
  choose C hC using fun i ↦
    (isBounded_range_normalizedCenteredTiltedHalfLine (s i)).exists_norm_le
  have hC_nonneg (i : Fin m) : 0 ≤ C i :=
    (norm_nonneg (h i 0)).trans (hC i (h i 0) (Set.mem_range_self 0))
  have hfactor_meas (i : Fin m) : Measurable (fun p : Coord m × Coord m ↦
      fixedAverageFactor (h i) (p.1 i) (p.2 i)) := by
    exact ((measurable_normalizedCenteredTiltedHalfLine (s i)).comp (by fun_prop)).mul
      ((measurable_normalizedCenteredTiltedHalfLine (s i)).comp (by fun_prop))
  have hfactor_bound (i : Fin m) : ∀ p : Coord m × Coord m,
      ‖fixedAverageFactor (h i) (p.1 i) (p.2 i)‖ ≤ C i ^ 2 := by
    intro p
    simp only [fixedAverageFactor, norm_mul, pow_two]
    exact mul_le_mul
      (hC i _ (Set.mem_range_self _)) (hC i _ (Set.mem_range_self _))
      (norm_nonneg _) (hC_nonneg i)
  have hproduct_int_finset (t : Finset (Fin m)) : Integrable
      (fun p : Coord m × Coord m ↦
        ∏ i ∈ t, fixedAverageFactor (h i) (p.1 i) (p.2 i))
      ((multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ht =>
        have hmul := ht.bdd_mul (hfactor_meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall (hfactor_bound i))
        simpa [Finset.prod_insert hi] using hmul
  change Integrable
    (fun p : Coord m × Coord m ↦
      ∏ i, fixedAverageFactor (h i) (p.1 i) (p.2 i))
    ((multivariateGaussian (0 : Coord m) R).prod
      (multivariateGaussian (0 : Coord m) R))
  simpa using hproduct_int_finset Finset.univ

private lemma selfConvolution_product_lt_sq
    {m : ℕ} (hm : 0 < m) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (s : Coord m) :
    (∫ u, ∏ i,
        normalizedSelfConvolution (normalizedCenteredTiltedHalfLine (s i)) (u i)
        ∂multivariateGaussian (0 : Coord m) R) <
      (∫ x, ∏ i, normalizedCenteredTiltedHalfLine (s i) (x i)
        ∂multivariateGaussian (0 : Coord m) R) ^ 2 := by
  classical
  let μ : Measure (Coord m) := multivariateGaussian (0 : Coord m) R
  let h : Fin m → ℝ → ℝ := fun i ↦ normalizedCenteredTiltedHalfLine (s i)
  let F : Coord m → ℝ := fun u ↦
    ∏ i, normalizedSelfConvolution (h i) (u i)
  let G : Coord m → ℝ := fun u ↦
    ∫ v, sumDifferenceProduct h (u, v) ∂μ
  have hFint : Integrable F μ := by
    exact integrable_coordinateProduct
      (fun i ↦ normalizedSelfConvolution (h i))
      (fun i ↦ measurable_normalizedSelfConvolution
        (measurable_normalizedCenteredTiltedHalfLine (s i)))
      (fun i ↦ isBounded_range_normalizedSelfConvolution
        (normalizedCenteredTiltedHalfLine_nonneg (s i))
        (isBounded_range_normalizedCenteredTiltedHalfLine (s i)))
  have hjoint : Integrable (sumDifferenceProduct h) (μ.prod μ) := by
    simpa only [h, μ] using
      integrable_sumDifferenceProduct_normalizedCenteredTiltedHalfLine R s
  have hGint : Integrable G μ := by
    exact hjoint.integral_prod_left
  have hF_nonneg (u : Coord m) : 0 ≤ F u := by
    exact Finset.prod_nonneg fun i hi ↦ normalizedSelfConvolution_nonneg (h i) (u i)
  have hG_nonneg (u : Coord m) : 0 ≤ G u := by
    exact integral_nonneg fun v ↦ Finset.prod_nonneg fun i hi ↦
      mul_nonneg
        (normalizedCenteredTiltedHalfLine_nonneg (s i) ((u i + v i) / Real.sqrt 2))
        (normalizedCenteredTiltedHalfLine_nonneg (s i) ((u i - v i) / Real.sqrt 2))
  have hle : (fun u ↦ ENNReal.ofReal (F u)) ≤ᵐ[μ]
      fun u ↦ ENNReal.ofReal (G u) := by
    filter_upwards with u
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [F, G, h, μ] using fixedAverage_pointwise_le R hR.1 s u)
  have hstrict : ∀ᵐ u ∂μ, u ∈ strictAverageSet s →
      ENNReal.ofReal (F u) < ENNReal.ofReal (G u) := by
    filter_upwards with u
    intro hu
    have hlt : F u < G u := by
      simpa only [F, G, h, μ] using
        fixedAverage_pointwise_lt R hR.1 hRne s u hu
    have hGpos : 0 < G u := (hF_nonneg u).trans_lt hlt
    exact (ENNReal.ofReal_lt_ofReal_iff hGpos).2 hlt
  have hFfinite : (∫⁻ u, ENNReal.ofReal (F u) ∂μ) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall hF_nonneg)]
    exact ENNReal.ofReal_ne_top
  have hlin := lintegral_strict_mono_of_ae_le_of_ae_lt_on
    hGint.aestronglyMeasurable.aemeasurable.ennreal_ofReal hFfinite hle
    (measure_strictAverageSet_pos hm R hR s).ne' hstrict
  rw [← ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall hF_nonneg),
    ← ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall hG_nonneg)] at hlin
  have hGintegral_pos : 0 < ∫ u, G u ∂μ := by
    exact ENNReal.ofReal_pos.1 (lt_of_le_of_lt bot_le hlin)
  have hreal : (∫ u, F u ∂μ) < ∫ u, G u ∂μ :=
    (ENNReal.ofReal_lt_ofReal_iff hGintegral_pos).1 hlin
  calc
    (∫ u, ∏ i,
        normalizedSelfConvolution (normalizedCenteredTiltedHalfLine (s i)) (u i)
        ∂multivariateGaussian (0 : Coord m) R) = ∫ u, F u ∂μ := rfl
    _ < ∫ u, G u ∂μ := hreal
    _ = (∫ x, ∏ i, normalizedCenteredTiltedHalfLine (s i) (x i)
        ∂multivariateGaussian (0 : Coord m) R) ^ 2 := by
      simpa only [G, h, μ] using
        integral_integral_sumDifferenceProduct_eq_sq R h
          (fun i ↦ measurable_normalizedCenteredTiltedHalfLine (s i))
          (fun i ↦ isBounded_range_normalizedCenteredTiltedHalfLine (s i))

private lemma one_lt_normalizedCenteredTiltedHalfLine_product
    {m : ℕ} (hm : 0 < m) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (s : Coord m) :
    1 < ∫ x, ∏ i, normalizedCenteredTiltedHalfLine (s i) (x i)
      ∂multivariateGaussian (0 : Coord m) R := by
  classical
  let h : Fin m → ℝ → ℝ := fun i ↦ normalizedCenteredTiltedHalfLine (s i)
  let D : Fin m → ℝ → ℝ := fun i ↦ normalizedSelfConvolution (h i)
  have hD_mass (i : Fin m) :
      (∫ u, D i u ∂gaussianReal 0 1) = 1 := by
    exact integral_normalizedSelfConvolution_eq_one
      (measurable_normalizedCenteredTiltedHalfLine (s i))
      (normalizedCenteredTiltedHalfLine_nonneg (s i))
      (isBounded_range_normalizedCenteredTiltedHalfLine (s i))
      (integral_normalizedCenteredTiltedHalfLine (s i))
  have hD_barycenter (i : Fin m) :
      (∫ u, u * D i u ∂gaussianReal 0 1) = 0 := by
    exact integral_mul_normalizedSelfConvolution_eq_zero
      (measurable_normalizedCenteredTiltedHalfLine (s i))
      (normalizedCenteredTiltedHalfLine_nonneg (s i))
      (isBounded_range_normalizedCenteredTiltedHalfLine (s i))
      (integral_normalizedCenteredTiltedHalfLine (s i))
      (integral_mul_normalizedCenteredTiltedHalfLine (s i))
  have hone_le : 1 ≤
      ∫ u, ∏ i, D i (u i) ∂multivariateGaussian (0 : Coord m) R := by
    have hmain := centered_product_of_continuous R hR.1 D
      (fun i ↦ continuous_normalizedSelfConvolution_normalizedCenteredTiltedHalfLine (s i))
      (fun i ↦ measurable_normalizedSelfConvolution
        (measurable_normalizedCenteredTiltedHalfLine (s i)))
      (fun i ↦ normalizedSelfConvolution_nonneg (h i))
      (fun i ↦ isBounded_range_normalizedSelfConvolution
        (normalizedCenteredTiltedHalfLine_nonneg (s i))
        (isBounded_range_normalizedCenteredTiltedHalfLine (s i)))
      (fun i ↦ isLogConcave_normalizedSelfConvolution
        (measurable_normalizedCenteredTiltedHalfLine (s i))
        (normalizedCenteredTiltedHalfLine_nonneg (s i))
        (isBounded_range_normalizedCenteredTiltedHalfLine (s i))
        (isLogConcave_normalizedCenteredTiltedHalfLine (s i)))
      (fun i ↦ by norm_num [hD_mass i]) hD_barycenter
    simpa only [hD_mass, Finset.prod_const_one] using hmain
  have hstrict := selfConvolution_product_lt_sq hm R hR hRne s
  have hone_lt_sq : 1 <
      (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R) ^ 2 :=
    hone_le.trans_lt (by simpa only [D, h] using hstrict)
  have hproduct_nonneg : 0 ≤
      ∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R := by
    exact integral_nonneg fun x ↦ Finset.prod_nonneg fun i hi ↦
      normalizedCenteredTiltedHalfLine_nonneg (s i) (x i)
  change 1 < ∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R
  nlinarith

/-- The adaptive centered half-lines have a strict product gain away from independence. -/
theorem centeredTiltedHalfLine_product_lt_of_ne_one
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (s : Coord m) :
    (∏ i, ∫ z, centeredTiltedHalfLine (s i) z ∂gaussianReal 0 1) <
      ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
        ∂multivariateGaussian 0 R := by
  classical
  let mass : Fin m → ℝ := fun i ↦
    ∫ z, centeredTiltedHalfLine (s i) z ∂gaussianReal 0 1
  let M : ℝ := ∏ i, mass i
  have hMpos : 0 < M := by
    exact Finset.prod_pos fun i hi ↦ integral_centeredTiltedHalfLine_pos (s i)
  have hnormalized := one_lt_normalizedCenteredTiltedHalfLine_product hm R hR hRne s
  have hnormalized_eq :
      (∫ x, ∏ i, normalizedCenteredTiltedHalfLine (s i) (x i)
          ∂multivariateGaussian (0 : Coord m) R) =
        M⁻¹ * ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
          ∂multivariateGaussian (0 : Coord m) R := by
    rw [show (fun x : Coord m ↦
        ∏ i, normalizedCenteredTiltedHalfLine (s i) (x i)) =
        fun x ↦ M⁻¹ * ∏ i, centeredTiltedHalfLine (s i) (x i) by
      funext x
      simp only [normalizedCenteredTiltedHalfLine]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib],
      integral_const_mul]
  rw [hnormalized_eq] at hnormalized
  change M < ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
    ∂multivariateGaussian (0 : Coord m) R
  calc
    M = M * 1 := (mul_one M).symm
    _ < M * (M⁻¹ * ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
        ∂multivariateGaussian (0 : Coord m) R) :=
      mul_lt_mul_of_pos_left hnormalized hMpos
    _ = ∫ x, ∏ i, centeredTiltedHalfLine (s i) (x i)
        ∂multivariateGaussian (0 : Coord m) R := by
      field_simp [hMpos.ne']

end WeakSimplex
