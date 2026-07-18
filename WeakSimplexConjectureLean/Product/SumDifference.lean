import WeakSimplexConjectureLean.Product.EvenLayerCake
import WeakSimplexConjectureLean.Product.NormalizedSelfConvolution

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WeakSimplex

section GaussianRotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

private def gaussianSumDifference (p : E × E) : E × E :=
  ((1 / Real.sqrt 2) • (p.1 + p.2), (1 / Real.sqrt 2) • (p.1 - p.2))

omit [CompleteSpace E] in
private theorem measurable_gaussianSumDifference :
    Measurable (gaussianSumDifference : E × E → E × E) := by
  unfold gaussianSumDifference
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
private theorem gaussianSumDifference_eq_rotation_swap (p : E × E) :
    gaussianSumDifference p =
      ContinuousLinearMap.rotation (E := E) (Real.pi / 4) p.swap := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hcoef : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    field_simp [ne_of_gt hsqrt_pos]
    exact hsqrt_sq
  rw [gaussianSumDifference, ContinuousLinearMap.rotation_apply]
  simp only [Real.cos_pi_div_four, Real.sin_pi_div_four, hcoef]
  ext <;> simp [smul_add, sub_eq_add_neg, add_comm]

private theorem map_gaussianSumDifference_eq_prod {μ : Measure E} [IsGaussian μ]
    (hμ : μ[id] = 0) :
    Measure.map gaussianSumDifference (μ.prod μ) = μ.prod μ := by
  calc
    Measure.map gaussianSumDifference (μ.prod μ) =
        Measure.map (ContinuousLinearMap.rotation (E := E) (Real.pi / 4))
          (Measure.map Prod.swap (μ.prod μ)) := by
      symm
      calc
        Measure.map (ContinuousLinearMap.rotation (E := E) (Real.pi / 4))
            (Measure.map Prod.swap (μ.prod μ)) =
            Measure.map
              ((ContinuousLinearMap.rotation (E := E) (Real.pi / 4)) ∘ Prod.swap)
              (μ.prod μ) := Measure.map_map
                (ContinuousLinearMap.rotation (E := E) (Real.pi / 4)).measurable
                measurable_swap
        _ = Measure.map gaussianSumDifference (μ.prod μ) := by
          congr 1
          funext p
          exact (gaussianSumDifference_eq_rotation_swap p).symm
    _ = Measure.map (ContinuousLinearMap.rotation (E := E) (Real.pi / 4))
        (μ.prod μ) := by
      rw [Measure.prod_swap]
    _ = μ.prod μ := IsGaussian.map_rotation_eq_self hμ (Real.pi / 4)

end GaussianRotation

/-- The normalized sum and difference of two centered multivariate Gaussians have product law. -/
theorem map_multivariateGaussian_sumDifference_eq_prod
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) :
    Measure.map
        (fun p : Coord m × Coord m ↦
          ((1 / Real.sqrt 2) • (p.1 + p.2),
            (1 / Real.sqrt 2) • (p.1 - p.2)))
        ((multivariateGaussian (0 : Coord m) R).prod
          (multivariateGaussian (0 : Coord m) R)) =
      (multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R) := by
  exact map_gaussianSumDifference_eq_prod (by simp)

private def coordProduct {m : ℕ} (h : Fin m → ℝ → ℝ) (x : Coord m) : ℝ :=
  ∏ i, h i (x i)

private def fixedAverageFactor
    (h : ℝ → ℝ) (u v : ℝ) : ℝ :=
  h ((u + v) / Real.sqrt 2) * h ((u - v) / Real.sqrt 2)

private theorem measurable_fixedAverageFactor
    {h : ℝ → ℝ} (hh : Measurable h) (u : ℝ) :
    Measurable (fixedAverageFactor h u) := by
  exact (hh.comp ((measurable_const.add measurable_id).div_const _)).mul
    (hh.comp ((measurable_const.sub measurable_id).div_const _))

private theorem fixedAverageFactor_nonneg
    {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (u v : ℝ) :
    0 ≤ fixedAverageFactor h u v :=
  mul_nonneg (hh _) (hh _)

private theorem fixedAverageFactor_even
    (h : ℝ → ℝ) (u : ℝ) : Function.Even (fixedAverageFactor h u) := by
  intro v
  have hplus : (u + -v) / Real.sqrt 2 = (u - v) / Real.sqrt 2 := by ring
  have hminus : (u - -v) / Real.sqrt 2 = (u + v) / Real.sqrt 2 := by ring
  simp only [fixedAverageFactor, hplus, hminus, mul_comm]

private theorem isLogConcave_comp_add_const_div_sqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) (u : ℝ) :
    IsLogConcave (fun v ↦ h ((u + v) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt x y
  have hmain := hh ht_pos ht_lt ((u + x) / Real.sqrt 2) ((u + y) / Real.sqrt 2)
  have harg : t * ((u + x) / Real.sqrt 2) +
      (1 - t) * ((u + y) / Real.sqrt 2) =
        (u + (t * x + (1 - t) * y)) / Real.sqrt 2 := by ring
  simpa only [smul_eq_mul, harg] using hmain

private theorem isLogConcave_comp_sub_const_div_sqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) (u : ℝ) :
    IsLogConcave (fun v ↦ h ((u - v) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt x y
  have hmain := hh ht_pos ht_lt ((u - x) / Real.sqrt 2) ((u - y) / Real.sqrt 2)
  have harg : t * ((u - x) / Real.sqrt 2) +
      (1 - t) * ((u - y) / Real.sqrt 2) =
        (u - (t * x + (1 - t) * y)) / Real.sqrt 2 := by ring
  simpa only [smul_eq_mul, harg] using hmain

private theorem isLogConcave_fixedAverageFactor
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_lc : IsLogConcave (fun x ↦ ENNReal.ofReal (h x))) (u : ℝ) :
    IsLogConcave (fun v ↦ ENNReal.ofReal (fixedAverageFactor h u v)) := by
  have hplus := isLogConcave_comp_add_const_div_sqrtTwo hh_lc u
  have hminus := isLogConcave_comp_sub_const_div_sqrtTwo hh_lc u
  convert hplus.mul hminus using 1
  funext v
  exact ENNReal.ofReal_mul (hh_nonneg _)

private theorem exists_norm_bound_of_isBounded_range_wp14
    {X : Type*} {f : X → ℝ} (hf : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf
  refine ⟨C, fun x ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self x)

private theorem isBounded_range_fixedAverageFactor
    {h : ℝ → ℝ} (hh : Bornology.IsBounded (Set.range h)) (u : ℝ) :
    Bornology.IsBounded (Set.range (fixedAverageFactor h u)) := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_isBounded_range_wp14 hh
  apply (Metric.isBounded_closedBall :
    Bornology.IsBounded (Metric.closedBall (0 : ℝ) (C ^ 2))).subset
  rintro z ⟨v, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [fixedAverageFactor, norm_mul, pow_two]
  have hC_nonneg : 0 ≤ C := (norm_nonneg (h 0)).trans (hC 0)
  exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC_nonneg

private theorem integrable_of_measurable_isBounded_range
    {X : Type*} [MeasurableSpace X] [Nonempty X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf_meas : Measurable f) (hf_bounded : Bornology.IsBounded (Set.range f)) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_isBounded_range_wp14 hf_bounded
  let x₀ : X := Classical.choice inferInstance
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f x₀)).trans (hC x₀)
  refine Integrable.mono' (integrable_const C) hf_meas.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [abs_of_nonneg hC_nonneg] using hC x

private theorem integral_fixedAverageFactor_eq_normalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) (u : ℝ) :
    (∫ v, fixedAverageFactor h u v ∂gaussianReal 0 1) =
      normalizedSelfConvolution h u := by
  have hfixed_meas := measurable_fixedAverageFactor hh_meas u
  have hfixed_nonneg : ∀ v, 0 ≤ fixedAverageFactor h u v :=
    fixedAverageFactor_nonneg hh_nonneg u
  have hfixed_int : Integrable (fixedAverageFactor h u) (gaussianReal 0 1) :=
    integrable_of_measurable_isBounded_range hfixed_meas
      (isBounded_range_fixedAverageFactor hh_bounded u)
  rw [normalizedSelfConvolution]
  change (∫ v, fixedAverageFactor h u v ∂gaussianReal 0 1) =
    (∫⁻ v, ENNReal.ofReal (h ((u + v) / Real.sqrt 2)) *
      ENNReal.ofReal (h ((u - v) / Real.sqrt 2)) ∂gaussianReal 0 1).toReal
  have hlintegral :
      (∫⁻ v, ENNReal.ofReal (h ((u + v) / Real.sqrt 2)) *
          ENNReal.ofReal (h ((u - v) / Real.sqrt 2)) ∂gaussianReal 0 1) =
        ENNReal.ofReal (∫ v, fixedAverageFactor h u v ∂gaussianReal 0 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfixed_int
      (Filter.Eventually.of_forall hfixed_nonneg)]
    apply lintegral_congr
    intro v
    exact (ENNReal.ofReal_mul (hh_nonneg _)).symm
  rw [hlintegral, ENNReal.toReal_ofReal (integral_nonneg hfixed_nonneg)]

private theorem integrable_coord_product
    {m : ℕ} {μ : Measure (Coord m)} [IsFiniteMeasure μ]
    (h : Fin m → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i))) :
    Integrable (fun x : Coord m ↦ ∏ i, h i (x i)) μ := by
  classical
  choose C hC using fun i ↦ exists_norm_bound_of_isBounded_range_wp14 (hh_bounded i)
  have hcoord_meas (i : Fin m) : Measurable (fun x : Coord m ↦ h i (x i)) :=
    (hh_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable
  have hcoord_bound (i : Fin m) : ∀ x : Coord m, ‖h i (x i)‖ ≤ C i :=
    fun x ↦ hC i (x i)
  have hproduct_int_finset (s : Finset (Fin m)) :
      Integrable (fun x : Coord m ↦ ∏ i ∈ s, h i (x i)) μ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
        have hmul := hs.bdd_mul (hcoord_meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall (hcoord_bound i))
        simpa [Finset.prod_insert hi] using hmul
  simpa using hproduct_int_finset Finset.univ

private theorem measurable_coordProduct
    {m : ℕ} (h : Fin m → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) :
    Measurable (coordProduct h) := by
  classical
  exact Finset.measurable_prod Finset.univ fun i _ ↦
    (hh_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

private theorem rotation_neg_pi_div_four_apply {m : ℕ} (p : Coord m × Coord m) :
    ContinuousLinearMap.rotation (-(Real.pi / 4)) p =
      ((Real.sqrt 2)⁻¹ • (p.1 - p.2), (Real.sqrt 2)⁻¹ • (p.1 + p.2)) := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hcoef : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    field_simp [ne_of_gt hsqrt_pos]
    nlinarith
  simp only [ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.cos_pi_div_four,
    Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg, hcoef]
  apply Prod.ext
  · module
  · module

private theorem multivariateGaussian_prod_rotation {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) :
    ((multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R)).map
      (ContinuousLinearMap.rotation (-(Real.pi / 4))) =
      (multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R) := by
  apply IsGaussian.map_rotation_eq_self
  simp

private def sumDifferenceProduct {m : ℕ}
    (h : Fin m → ℝ → ℝ) (p : Coord m × Coord m) : ℝ :=
  ∏ i, fixedAverageFactor (h i) (p.1 i) (p.2 i)

private theorem sumDifferenceProduct_eq_rotated {m : ℕ}
    (h : Fin m → ℝ → ℝ) (p : Coord m × Coord m) :
    sumDifferenceProduct h p =
      coordProduct h (ContinuousLinearMap.rotation (-(Real.pi / 4)) p).1 *
        coordProduct h (ContinuousLinearMap.rotation (-(Real.pi / 4)) p).2 := by
  classical
  rw [rotation_neg_pi_div_four_apply]
  simp only [sumDifferenceProduct, fixedAverageFactor, coordProduct, PiLp.smul_apply,
    PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hsub : (Real.sqrt 2)⁻¹ * (p.1 i - p.2 i) =
      (p.1 i - p.2 i) / Real.sqrt 2 := by
    rw [div_eq_mul_inv, mul_comm]
  have hadd : (Real.sqrt 2)⁻¹ * (p.1 i + p.2 i) =
      (p.1 i + p.2 i) / Real.sqrt 2 := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hsub, hadd, mul_comm]

private theorem fixedAverage_pointwise_deficit
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x))) (u : Coord m) :
    (∏ i, normalizedSelfConvolution (h i) (u i)) ≤
      ∫ v, sumDifferenceProduct h (u, v)
        ∂multivariateGaussian (0 : Coord m) R := by
  let g : Fin m → ℝ → ℝ := fun i ↦ fixedAverageFactor (h i) (u i)
  have hmain := even_logConcave_product_of_posDef R hR hdiag g
    (fun i ↦ measurable_fixedAverageFactor (hh_meas i) (u i))
    (fun i ↦ fixedAverageFactor_nonneg (hh_nonneg i) (u i))
    (fun i ↦ isBounded_range_fixedAverageFactor (hh_bounded i) (u i))
    (fun i ↦ fixedAverageFactor_even (h i) (u i))
    (fun i ↦ isLogConcave_fixedAverageFactor (hh_nonneg i) (hh_lc i) (u i))
  calc
    (∏ i, normalizedSelfConvolution (h i) (u i)) =
        ∏ i, ∫ v, g i v ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (integral_fixedAverageFactor_eq_normalizedSelfConvolution
        (hh_meas i) (hh_nonneg i) (hh_bounded i) (u i)).symm
    _ ≤ ∫ v, ∏ i, g i (v i) ∂multivariateGaussian (0 : Coord m) R := hmain
    _ = ∫ v, sumDifferenceProduct h (u, v)
          ∂multivariateGaussian (0 : Coord m) R := by rfl

/-- Normalized self-convolution cannot increase the correlated product deficit. -/
theorem normalizedSelfConvolution_product_deficit_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x))) :
    (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R) ^ 2 ≥
      ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R := by
  classical
  let μ : Measure (Coord m) := multivariateGaussian (0 : Coord m) R
  let rot : Coord m × Coord m →L[ℝ] Coord m × Coord m :=
    ContinuousLinearMap.rotation (-(Real.pi / 4))
  let original : Coord m × Coord m → ℝ := fun p ↦
    coordProduct h p.1 * coordProduct h p.2
  let transformed : Coord m → ℝ := fun u ↦
    ∏ i, normalizedSelfConvolution (h i) (u i)
  have hcoord_int : Integrable (coordProduct h) μ := by
    exact integrable_coord_product h hh_meas hh_bounded
  have horiginal_int : Integrable original (μ.prod μ) := by
    exact hcoord_int.mul_prod hcoord_int
  have horiginal_meas : Measurable original := by
    exact ((measurable_coordProduct h hh_meas).comp measurable_fst).mul
      ((measurable_coordProduct h hh_meas).comp measurable_snd)
  have hrot_map : (μ.prod μ).map rot = μ.prod μ := by
    simpa only [μ, rot] using multivariateGaussian_prod_rotation R
  have hrot_pres : MeasurePreserving rot (μ.prod μ) (μ.prod μ) :=
    ⟨rot.measurable, hrot_map⟩
  have hsum_int : Integrable (sumDifferenceProduct h) (μ.prod μ) := by
    have hcomp := hrot_pres.integrable_comp_of_integrable horiginal_int
    have heq : sumDifferenceProduct h = original ∘ rot := by
      funext p
      simpa only [Function.comp_apply, original, rot] using
        sumDifferenceProduct_eq_rotated h p
    rw [heq]
    exact hcomp
  have htransformed_int : Integrable transformed μ := by
    exact integrable_coord_product
      (fun i ↦ normalizedSelfConvolution (h i))
      (fun i ↦ measurable_normalizedSelfConvolution (hh_meas i))
      (fun i ↦ isBounded_range_normalizedSelfConvolution
        (hh_nonneg i) (hh_bounded i))
  have hiterated_int :
      Integrable (fun u ↦ ∫ v, sumDifferenceProduct h (u, v) ∂μ) μ :=
    hsum_int.integral_prod_left
  have hpointwise (u : Coord m) :
      transformed u ≤ ∫ v, sumDifferenceProduct h (u, v) ∂μ := by
    simpa only [transformed, μ] using
      fixedAverage_pointwise_deficit R hR hdiag h hh_meas hh_nonneg
        hh_bounded hh_lc u
  have hmono :
      (∫ u, transformed u ∂μ) ≤
        ∫ u, ∫ v, sumDifferenceProduct h (u, v) ∂μ ∂μ :=
    integral_mono htransformed_int hiterated_int hpointwise
  have hrotate_integral :
      (∫ p, original p ∂μ.prod μ) =
        ∫ p, sumDifferenceProduct h p ∂μ.prod μ := by
    calc
      (∫ p, original p ∂μ.prod μ) =
          ∫ p, original p ∂Measure.map rot (μ.prod μ) := by rw [hrot_map]
      _ = ∫ p, original (rot p) ∂μ.prod μ :=
        integral_map_of_stronglyMeasurable rot.measurable
          horiginal_meas.stronglyMeasurable
      _ = ∫ p, sumDifferenceProduct h p ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with p
        exact (sumDifferenceProduct_eq_rotated h p).symm
  calc
    (∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R) = ∫ u, transformed u ∂μ := rfl
    _ ≤ ∫ u, ∫ v, sumDifferenceProduct h (u, v) ∂μ ∂μ := hmono
    _ = ∫ p, sumDifferenceProduct h p ∂μ.prod μ :=
      (integral_prod (sumDifferenceProduct h) hsum_int).symm
    _ = ∫ p, original p ∂μ.prod μ := hrotate_integral.symm
    _ = (∫ x, coordProduct h x ∂μ) ^ 2 := by
      rw [integral_prod_mul]
      ring
    _ = (∫ x, ∏ i, h i (x i)
        ∂multivariateGaussian (0 : Coord m) R) ^ 2 := rfl

end WeakSimplex
