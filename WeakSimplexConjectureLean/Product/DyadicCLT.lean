import WeakSimplexConjectureLean.Product.NormalizedSelfConvolution
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.CharacteristicFunction

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

namespace WeakSimplex

/-- The `r`-fold normalized self-convolution of a scalar factor. -/
def iteratedNormalizedSelfConvolution (h : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => h
  | r + 1 => normalizedSelfConvolution (iteratedNormalizedSelfConvolution h r)

theorem measurable_iteratedNormalizedSelfConvolution
    {h : ℝ → ℝ} (hh : Measurable h) (r : ℕ) :
    Measurable (iteratedNormalizedSelfConvolution h r) := by
  induction r with
  | zero => simpa [iteratedNormalizedSelfConvolution] using hh
  | succ r ih =>
      simpa [iteratedNormalizedSelfConvolution] using
        measurable_normalizedSelfConvolution ih

theorem iteratedNormalizedSelfConvolution_nonneg
    {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (r : ℕ) (x : ℝ) :
    0 ≤ iteratedNormalizedSelfConvolution h r x := by
  induction r with
  | zero => simpa [iteratedNormalizedSelfConvolution] using hh x
  | succ r ih =>
      simpa [iteratedNormalizedSelfConvolution] using
        normalizedSelfConvolution_nonneg (iteratedNormalizedSelfConvolution h r) x

theorem isBounded_range_iteratedNormalizedSelfConvolution
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) (r : ℕ) :
    Bornology.IsBounded (Set.range (iteratedNormalizedSelfConvolution h r)) := by
  induction r with
  | zero => simpa [iteratedNormalizedSelfConvolution] using hh_bounded
  | succ r ih =>
      simpa [iteratedNormalizedSelfConvolution] using
        isBounded_range_normalizedSelfConvolution
          (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r) ih

theorem isLogConcave_iteratedNormalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_lc : IsLogConcave (fun x ↦ ENNReal.ofReal (h x))) (r : ℕ) :
    IsLogConcave
      (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x)) := by
  induction r with
  | zero => simpa [iteratedNormalizedSelfConvolution] using hh_lc
  | succ r ih =>
      simpa [iteratedNormalizedSelfConvolution] using
        isLogConcave_normalizedSelfConvolution
          (measurable_iteratedNormalizedSelfConvolution hh_meas r)
          (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r)
          (isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r) ih

theorem integral_iteratedNormalizedSelfConvolution_eq_one
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) (r : ℕ) :
    ∫ x, iteratedNormalizedSelfConvolution h r x ∂gaussianReal 0 1 = 1 := by
  induction r with
  | zero => simpa [iteratedNormalizedSelfConvolution] using hh_mass
  | succ r ih =>
      simpa [iteratedNormalizedSelfConvolution] using
        integral_normalizedSelfConvolution_eq_one
          (measurable_iteratedNormalizedSelfConvolution hh_meas r)
          (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r)
          (isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r) ih

theorem integral_mul_iteratedNormalizedSelfConvolution_eq_zero
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∫ x, x * h x ∂gaussianReal 0 1 = 0) (r : ℕ) :
    ∫ x, x * iteratedNormalizedSelfConvolution h r x ∂gaussianReal 0 1 = 0 := by
  induction r with
  | zero => simpa [iteratedNormalizedSelfConvolution] using hh_barycenter
  | succ r ih =>
      simpa [iteratedNormalizedSelfConvolution] using
        integral_mul_normalizedSelfConvolution_eq_zero
          (measurable_iteratedNormalizedSelfConvolution hh_meas r)
          (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r)
          (isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r)
          (integral_iteratedNormalizedSelfConvolution_eq_one
            hh_meas hh_nonneg hh_bounded hh_mass r) ih

theorem variance_id_iteratedNormalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) (r : ℕ) :
    Var[id; (gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))] =
      Var[id; (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))] := by
  induction r with
  | zero => rfl
  | succ r ih =>
      calc
        Var[id; (gaussianReal 0 1).withDensity
            (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h (r + 1) x))] =
            Var[id; (gaussianReal 0 1).withDensity
              (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))] := by
          simpa [iteratedNormalizedSelfConvolution] using
            variance_id_normalizedSelfConvolution
              (measurable_iteratedNormalizedSelfConvolution hh_meas r)
              (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r)
              (isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r)
              (integral_iteratedNormalizedSelfConvolution_eq_one
                hh_meas hh_nonneg hh_bounded hh_mass r)
        _ = Var[id; (gaussianReal 0 1).withDensity
            (fun x ↦ ENNReal.ofReal (h x))] := ih

private def gaussianDensityMeasure (h : ℝ → ℝ) : Measure ℝ :=
  (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))

private theorem isProbabilityMeasure_gaussianDensityMeasure
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    IsProbabilityMeasure (gaussianDensityMeasure h) := by
  obtain ⟨C, hC⟩ := hh_bounded.exists_norm_le
  have hC_nonneg : 0 ≤ C := (norm_nonneg (h 0)).trans (hC (h 0) ⟨0, rfl⟩)
  have hh_int : Integrable h (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const C) hh_meas.aestronglyMeasurable ?_
    filter_upwards with x
    simpa [abs_of_nonneg hC_nonneg] using hC (h x) ⟨x, rfl⟩
  refine ⟨?_⟩
  rw [gaussianDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hh_int
      (Filter.Eventually.of_forall hh_nonneg), hh_mass]
  simp

theorem isProbabilityMeasure_iteratedNormalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) (r : ℕ) :
    IsProbabilityMeasure
      ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))) := by
  simpa only [gaussianDensityMeasure] using
    isProbabilityMeasure_gaussianDensityMeasure
      (measurable_iteratedNormalizedSelfConvolution hh_meas r)
      (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r)
      (isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r)
      (integral_iteratedNormalizedSelfConvolution_eq_one
        hh_meas hh_nonneg hh_bounded hh_mass r)

private theorem memLp_id_gaussianDensityMeasure
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) :
    MemLp id 2 (gaussianDensityMeasure h) := by
  obtain ⟨C, hC⟩ := hh_bounded.exists_norm_le
  have hle (x : ℝ) : h x ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hh_nonneg x)] using hC (h x) ⟨x, rfl⟩
  rw [gaussianDensityMeasure, memLp_two_iff_integrable_sq (by fun_prop),
    integrable_withDensity_iff hh_meas.ennreal_ofReal (by simp)]
  have hbase := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq
  refine Integrable.mono' (hbase.mul_const C) (by fun_prop) ?_
  filter_upwards with x
  simp only [id_eq, ENNReal.toReal_ofReal (hh_nonneg x), Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg x) (hh_nonneg x))]
  exact mul_le_mul_of_nonneg_left (hle x) (sq_nonneg x)

private theorem integral_id_gaussianDensityMeasure
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_barycenter : ∫ x, x * h x ∂gaussianReal 0 1 = 0) :
    ∫ x, x ∂gaussianDensityMeasure h = 0 := by
  change ∫ x, id x ∂((gaussianReal 0 1).withDensity
    (fun x ↦ ENNReal.ofReal (h x))) = 0
  rw [integral_withDensity_eq_integral_toReal_smul hh_meas.ennreal_ofReal (by simp) id]
  simpa only [id_eq, ENNReal.toReal_ofReal (hh_nonneg _), smul_eq_mul,
    mul_comm] using hh_barycenter

private theorem variance_id_gaussianDensityMeasure_ne_zero
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    Var[id; gaussianDensityMeasure h] ≠ 0 := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  let ν := gaussianDensityMeasure h
  letI : NoAtoms ν := by
    dsimp only [ν, gaussianDensityMeasure]
    infer_instance
  have hν : IsProbabilityMeasure ν := by
    simpa only [ν] using
      isProbabilityMeasure_gaussianDensityMeasure hh_meas hh_nonneg hh_bounded hh_mass
  letI := hν
  have hmem : MemLp id 2 ν := by
    simpa only [ν] using memLp_id_gaussianDensityMeasure hh_meas hh_nonneg hh_bounded
  intro hvar
  have hconst : ∀ᵐ x ∂ν, id x = ν[id] :=
    ae_eq_integral_of_variance_eq_zero hmem hvar
  have hne : ∀ᵐ x ∂ν, id x ≠ ν[id] := by
    simpa only [id_eq] using ν.ae_ne ν[id]
  have hfalse : ∀ᵐ _x ∂ν, False := by
    filter_upwards [hconst, hne] with x hx hnx
    exact hnx hx
  exact hfalse.exists.elim fun _ hx ↦ hx

theorem variance_id_withDensity_ofReal_pos
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    0 < Var[id; (gaussianReal 0 1).withDensity
      (fun x ↦ ENNReal.ofReal (h x))] := by
  apply lt_of_le_of_ne (variance_nonneg _ _)
  simpa only [gaussianDensityMeasure] using
    (variance_id_gaussianDensityMeasure_ne_zero
      hh_meas hh_nonneg hh_bounded hh_mass).symm

private def iteratedNormalizedAverageLaw (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => ν
  | r + 1 =>
      Measure.map (fun p : ℝ × ℝ ↦ (p.1 + p.2) / Real.sqrt 2)
        ((iteratedNormalizedAverageLaw ν r).prod (iteratedNormalizedAverageLaw ν r))

private theorem iteratedNormalizedSelfConvolution_law
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) (r : ℕ) :
    iteratedNormalizedAverageLaw (gaussianDensityMeasure h) r =
      gaussianDensityMeasure (iteratedNormalizedSelfConvolution h r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedNormalizedAverageLaw, ih, iteratedNormalizedSelfConvolution]
      simpa only [gaussianDensityMeasure] using
        normalizedSelfConvolution_law
          (measurable_iteratedNormalizedSelfConvolution hh_meas r)
          (iteratedNormalizedSelfConvolution_nonneg hh_nonneg r)
          (isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r)

private def dyadicConvolution (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => ν
  | r + 1 => dyadicConvolution ν r ∗ dyadicConvolution ν r

private def realScale (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

private theorem realScale_apply (a x : ℝ) : realScale a x = a * x := by
  simp [realScale]

private def dyadicScale (r : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ ^ r

private theorem sqrt_two_pow (r : ℕ) :
    Real.sqrt ((2 : ℝ) ^ r) = (Real.sqrt 2) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private theorem dyadicScale_eq_inv_sqrt_two_pow (r : ℕ) :
    dyadicScale r = (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ := by
  rw [show ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r by norm_num, sqrt_two_pow]
  exact inv_pow (Real.sqrt 2) r

private theorem normalizedAverageLaw_eq_map_conv
    (ν : Measure ℝ) [SFinite ν] :
    Measure.map (fun p : ℝ × ℝ ↦ (p.1 + p.2) / Real.sqrt 2) (ν.prod ν) =
      (ν ∗ ν).map (realScale (Real.sqrt 2)⁻¹) := by
  rw [Measure.conv, Measure.map_map (realScale (Real.sqrt 2)⁻¹).measurable
    measurable_add]
  congr 1
  funext p
  rw [Function.comp_apply, realScale_apply, div_eq_mul_inv, mul_comm]

private theorem sfinite_dyadicConvolution
    (ν : Measure ℝ) [SFinite ν] (r : ℕ) :
    SFinite (dyadicConvolution ν r) := by
  induction r with
  | zero => simpa [dyadicConvolution] using (inferInstance : SFinite ν)
  | succ r ih =>
      rw [dyadicConvolution]
      letI := ih
      infer_instance

private theorem iteratedNormalizedAverageLaw_eq_map_dyadicConvolution
    (ν : Measure ℝ) [SFinite ν] (r : ℕ) :
    iteratedNormalizedAverageLaw ν r =
      (dyadicConvolution ν r).map (realScale (dyadicScale r)) := by
  induction r with
  | zero => simp [iteratedNormalizedAverageLaw, dyadicConvolution, dyadicScale, realScale]
  | succ r ih =>
      letI := sfinite_dyadicConvolution ν r
      rw [iteratedNormalizedAverageLaw, ih, normalizedAverageLaw_eq_map_conv,
        dyadicConvolution]
      rw [← Measure.map_conv_continuousLinearMap (realScale (dyadicScale r))]
      rw [Measure.map_map (realScale (Real.sqrt 2)⁻¹).measurable
        (realScale (dyadicScale r)).measurable]
      congr 1
      funext x
      simp only [Function.comp_apply, realScale_apply, dyadicScale, pow_succ]
      ring

private theorem isFiniteMeasure_dyadicConvolution
    (ν : Measure ℝ) [IsFiniteMeasure ν] (r : ℕ) :
    IsFiniteMeasure (dyadicConvolution ν r) := by
  induction r with
  | zero => simpa [dyadicConvolution] using (inferInstance : IsFiniteMeasure ν)
  | succ r ih =>
      rw [dyadicConvolution]
      letI := ih
      infer_instance

private theorem charFun_dyadicConvolution
    (ν : Measure ℝ) [IsFiniteMeasure ν] (r : ℕ) (t : ℝ) :
    charFun (dyadicConvolution ν r) t = (charFun ν t) ^ (2 ^ r) := by
  induction r with
  | zero => simp [dyadicConvolution]
  | succ r ih =>
      letI := isFiniteMeasure_dyadicConvolution ν r
      rw [dyadicConvolution, charFun_conv, ih]
      simp only [pow_succ]
      rw [pow_mul, pow_two]

private theorem map_dyadicSum_eq_dyadicConvolution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_law : ∀ i, HasLaw (X i) ν P)
    (hX_indep : iIndepFun X P) (r : ℕ) :
    P.map (fun omega ↦ ∑ k ∈ Finset.range (2 ^ r), X k omega) =
      dyadicConvolution ν r := by
  letI := isFiniteMeasure_dyadicConvolution ν r
  apply Measure.ext_of_charFun
  funext t
  have hsum := (hX_indep.restrict (Finset.range (2 ^ r))).charFun_map_fun_finsetSum_eq_prod
    (fun i _ ↦ (hX_meas i).aemeasurable)
  rw [congrFun hsum t, charFun_dyadicConvolution]
  simp_rw [(hX_law _).map_eq]
  simp

/-- The iterated density transform is the law of the normalized sum of `2 ^ r` iid copies. -/
theorem hasLaw_iteratedNormalizedSelfConvolution_dyadicSum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : ℝ → ℝ} {X : ℕ → Ω → ℝ}
    (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hX_meas : ∀ i, Measurable (X i))
    (hX_law : ∀ i, HasLaw (X i)
      ((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))) P)
    (hX_indep : iIndepFun X P) (r : ℕ) :
    HasLaw
      (fun omega ↦ (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (2 ^ r), X k omega)
      ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))) P := by
  let sumFun : Ω → ℝ := fun omega ↦ ∑ k ∈ Finset.range (2 ^ r), X k omega
  have hsum_meas : Measurable sumFun := by
    exact Finset.measurable_sum _ fun i _ ↦ hX_meas i
  have hX_law' : ∀ i, HasLaw (X i) (gaussianDensityMeasure h) P := by
    simpa only [gaussianDensityMeasure] using hX_law
  have hnu_prob : IsProbabilityMeasure (gaussianDensityMeasure h) := by
    exact (hX_law' 0).isProbabilityMeasure_iff.1 inferInstance
  letI := hnu_prob
  have hsum : P.map sumFun = dyadicConvolution (gaussianDensityMeasure h) r := by
    exact map_dyadicSum_eq_dyadicConvolution hX_meas hX_law' hX_indep r
  have hmap : P.map (fun omega ↦ dyadicScale r * sumFun omega) =
      gaussianDensityMeasure (iteratedNormalizedSelfConvolution h r) := by
    calc
      P.map (fun omega ↦ dyadicScale r * sumFun omega) =
          (P.map sumFun).map (realScale (dyadicScale r)) := by
        rw [Measure.map_map (realScale (dyadicScale r)).measurable hsum_meas]
        rfl
      _ = (dyadicConvolution (gaussianDensityMeasure h) r).map
          (realScale (dyadicScale r)) := by rw [hsum]
      _ = iteratedNormalizedAverageLaw (gaussianDensityMeasure h) r :=
        (iteratedNormalizedAverageLaw_eq_map_dyadicConvolution _ r).symm
      _ = gaussianDensityMeasure (iteratedNormalizedSelfConvolution h r) :=
        iteratedNormalizedSelfConvolution_law hh_meas hh_nonneg hh_bounded r
  refine ⟨?_, ?_⟩
  · exact hsum_meas.const_mul _ |>.aemeasurable
  · change P.map (fun omega ↦ (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ * sumFun omega) =
      gaussianDensityMeasure (iteratedNormalizedSelfConvolution h r)
    rw [← dyadicScale_eq_inv_sqrt_two_pow]
    exact hmap

theorem tendstoInDistribution_iteratedNormalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∫ x, x * h x ∂gaussianReal 0 1 = 0) :
    letI _ : ∀ r, IsProbabilityMeasure
      ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))) :=
      fun r ↦ isProbabilityMeasure_iteratedNormalizedSelfConvolution
        hh_meas hh_nonneg hh_bounded hh_mass r
    TendstoInDistribution (fun _ : ℕ ↦ id) atTop id
      (fun r ↦ (gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x)))
      (gaussianReal 0
        Var[id; (gaussianReal 0 1).withDensity
          (fun x ↦ ENNReal.ofReal (h x))].toNNReal) := by
  letI iteratedProb : ∀ r, IsProbabilityMeasure
      ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))) :=
    fun r ↦ isProbabilityMeasure_iteratedNormalizedSelfConvolution
      hh_meas hh_nonneg hh_bounded hh_mass r
  let ν := gaussianDensityMeasure h
  have hν : IsProbabilityMeasure ν := by
    simpa only [ν] using
      isProbabilityMeasure_gaussianDensityMeasure hh_meas hh_nonneg hh_bounded hh_mass
  letI := hν
  let P := Measure.infinitePi (fun _ : ℕ ↦ ν)
  letI : IsProbabilityMeasure P := by
    dsimp only [P]
    infer_instance
  let X : ℕ → (ℕ → ℝ) → ℝ := fun n omega ↦ omega n
  have hX_meas : ∀ n, Measurable (X n) := fun n ↦ measurable_pi_apply n
  have hX_law : ∀ n, HasLaw (X n) ν P := fun n ↦ by
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ ν) n).hasLaw
  have hident : ∀ n, IdentDistrib (X n) (X 0) P P := fun n ↦
    ⟨(hX_meas n).aemeasurable, (hX_meas 0).aemeasurable,
      (hX_law n).map_eq.trans (hX_law 0).map_eq.symm⟩
  have hindep : iIndepFun X P := by
    simpa only [P, X, id_eq] using
      (iIndepFun_infinitePi (P := fun _ : ℕ ↦ ν)
        (X := fun _ ↦ (id : ℝ → ℝ)) (fun _ ↦ measurable_id))
  have hmemν : MemLp id 2 ν := by
    simpa only [ν] using memLp_id_gaussianDensityMeasure hh_meas hh_nonneg hh_bounded
  have hX0_ident : IdentDistrib (X 0) id P ν :=
    ⟨(hX_meas 0).aemeasurable, measurable_id.aemeasurable, by
      simpa using (hX_law 0).map_eq⟩
  have hmemX : MemLp (X 0) 2 P := hX0_ident.memLp_iff.mpr hmemν
  have hmeanX : P[X 0] = 0 := by
    rw [(hX_law 0).integral_eq]
    exact integral_id_gaussianDensityMeasure hh_meas hh_nonneg hh_barycenter
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := P) (P' := gaussianReal 0 Var[X 0; P].toNNReal)
    (X := X) (Y := id) (HasLaw.id) hmemX hindep hident
  have hvar : Var[X 0; P] = Var[id; ν] := (hX_law 0).variance_eq
  have hsubseq : Tendsto (fun r : ℕ ↦ 2 ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hdyadic : TendstoInDistribution
      (fun (r : ℕ) omega ↦
        (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ *
          (∑ k ∈ Finset.range (2 ^ r), X k omega - ((2 ^ r : ℕ) : ℝ) * P[X 0]))
      atTop id (fun _ ↦ P) (gaussianReal 0 Var[X 0; P].toNNReal) := {
    forall_aemeasurable r := hclt.forall_aemeasurable (2 ^ r)
    aemeasurable_limit := hclt.aemeasurable_limit
    tendsto := hclt.tendsto.comp hsubseq
  }
  have hdyadic' : TendstoInDistribution
      (fun (r : ℕ) omega ↦ (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (2 ^ r), X k omega)
      atTop id (fun _ ↦ P) (gaussianReal 0 Var[id; ν].toNNReal) := by
    rw [hvar] at hdyadic
    simpa only [hmeanX, mul_zero, sub_zero] using hdyadic
  refine ⟨fun _ ↦ measurable_id.aemeasurable, measurable_id.aemeasurable, ?_⟩
  have hlaw (r : ℕ) : HasLaw
      (fun omega ↦ (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (2 ^ r), X k omega)
      ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))) P := by
    simpa only [ν, gaussianDensityMeasure] using
      hasLaw_iteratedNormalizedSelfConvolution_dyadicSum
        hh_meas hh_nonneg hh_bounded hX_meas hX_law hindep r
  have hsource :
      (fun r ↦ ⟨Measure.map id
          ((gaussianReal 0 1).withDensity
            (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x))),
          Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
        ℕ → ProbabilityMeasure ℝ) =
      (fun r ↦ ⟨P.map (fun omega ↦ (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ *
          ∑ k ∈ Finset.range (2 ^ r), X k omega),
          Measure.isProbabilityMeasure_map (hdyadic'.forall_aemeasurable r)⟩) := by
    funext r
    apply Subtype.ext
    change Measure.map id _ = P.map _
    rw [Measure.map_id, (hlaw r).map_eq]
  rw [hsource]
  simpa only [ν, gaussianDensityMeasure] using hdyadic'.tendsto

end WeakSimplex
