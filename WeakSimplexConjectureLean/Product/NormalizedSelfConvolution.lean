import WeakSimplexConjectureLean.LogConcavity.Prekopa
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.Variance

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WeakSimplex

private def normalizedSelfConvolutionENNReal (h : ℝ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, h ((u + v) / Real.sqrt 2) * h ((u - v) / Real.sqrt 2) ∂gaussianReal 0 1

/-- The density-coordinate normalized self-convolution relative to standard Gaussian measure.

This total `toReal` wrapper is used under boundedness in the substantive interface theorems. -/
def normalizedSelfConvolution (h : ℝ → ℝ) (u : ℝ) : ℝ :=
  (normalizedSelfConvolutionENNReal (fun x ↦ ENNReal.ofReal (h x)) u).toReal

private theorem measurable_normalizedSelfConvolutionENNReal
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    Measurable (normalizedSelfConvolutionENNReal h) := by
  apply Measurable.lintegral_prod_right
  exact (hh.comp ((measurable_fst.add measurable_snd).div_const _)).mul
    (hh.comp ((measurable_fst.sub measurable_snd).div_const _))

private theorem normalizedSelfConvolutionENNReal_le
    {h : ℝ → ℝ≥0∞} {C : ℝ≥0∞} (hh : ∀ x, h x ≤ C) (u : ℝ) :
    normalizedSelfConvolutionENNReal h u ≤ C ^ 2 := by
  calc
    normalizedSelfConvolutionENNReal h u ≤ ∫⁻ _ : ℝ, C ^ 2 ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro v
      simpa [pow_two] using mul_le_mul (hh _) (hh _) bot_le bot_le
    _ = C ^ 2 := by simp

private def gaussianKernelOne (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(x ^ 2) / 2))

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

private theorem isLogConcave_comp_sumDivSqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) :
    IsLogConcave (fun p : ℝ × ℝ ↦ h ((p.1 + p.2) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt p q
  have hmain := hh ht_pos ht_lt ((p.1 + p.2) / Real.sqrt 2)
    ((q.1 + q.2) / Real.sqrt 2)
  convert hmain using 1
  change h _ = h _
  congr 1
  change (t * p.1 + (1 - t) * q.1 + (t * p.2 + (1 - t) * q.2)) /
      Real.sqrt 2 =
    t * ((p.1 + p.2) / Real.sqrt 2) +
      (1 - t) * ((q.1 + q.2) / Real.sqrt 2)
  ring

private theorem isLogConcave_comp_subDivSqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) :
    IsLogConcave (fun p : ℝ × ℝ ↦ h ((p.1 - p.2) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt p q
  have hmain := hh ht_pos ht_lt ((p.1 - p.2) / Real.sqrt 2)
    ((q.1 - q.2) / Real.sqrt 2)
  convert hmain using 1
  change h _ = h _
  congr 1
  change (t * p.1 + (1 - t) * q.1 - (t * p.2 + (1 - t) * q.2)) /
      Real.sqrt 2 =
    t * ((p.1 - p.2) / Real.sqrt 2) +
      (1 - t) * ((q.1 - q.2) / Real.sqrt 2)
  ring

private theorem isLogConcave_lintegral_real_right
    {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [Module ℝ E]
    {F : E → ℝ → ℝ≥0∞}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_lc : IsLogConcave (fun p : E × ℝ ↦ F p.1 p.2)) :
    IsLogConcave (fun x ↦ ∫⁻ y, F x y) := by
  let G : E → (Fin 1 → ℝ) → ℝ≥0∞ := fun x y ↦
    F x (MeasurableEquiv.funUnique (Fin 1) ℝ y)
  have hG_meas : ∀ x, Measurable (G x) := fun x ↦
    (hF_meas.comp (measurable_const.prodMk
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable))
  have hG_lc : IsLogConcave (fun p : E × (Fin 1 → ℝ) ↦ G p.1 p.2) := by
    intro t ht_pos ht_lt p q
    simpa [G, MeasurableEquiv.funUnique, MeasurableEquiv.piUnique,
      Equiv.funUnique, Equiv.piUnique] using
        hF_lc ht_pos ht_lt
          (p.1, MeasurableEquiv.funUnique (Fin 1) ℝ p.2)
          (q.1, MeasurableEquiv.funUnique (Fin 1) ℝ q.2)
  have hmain := isLogConcave_lintegral_right hG_meas hG_lc
  have hEq : (fun x ↦ ∫⁻ y, G x y) = fun x ↦ ∫⁻ y, F x y := by
    funext x
    exact (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding (F x)
  rwa [hEq] at hmain

private theorem isLogConcave_normalizedSelfConvolutionENNReal
    {h : ℝ → ℝ≥0∞} (hh_meas : Measurable h) (hh_lc : IsLogConcave h) :
    IsLogConcave (normalizedSelfConvolutionENNReal h) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun u v ↦
    h ((u + v) / Real.sqrt 2) * h ((u - v) / Real.sqrt 2) * gaussianPDF 0 1 v
  have hF_meas : Measurable (Function.uncurry F) :=
    (((hh_meas.comp ((measurable_fst.add measurable_snd).div_const _)).mul
      (hh_meas.comp ((measurable_fst.sub measurable_snd).div_const _))).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd))
  have hF_lc : IsLogConcave (fun p : ℝ × ℝ ↦ F p.1 p.2) :=
    ((isLogConcave_comp_sumDivSqrtTwo hh_lc).mul
      (isLogConcave_comp_subDivSqrtTwo hh_lc)).mul
        (isLogConcave_gaussianPDF_zero_one.comp_affineMap
          (ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.toAffineMap)
  have hMarg := isLogConcave_lintegral_real_right hF_meas hF_lc
  have hEq : normalizedSelfConvolutionENNReal h = fun u ↦ ∫⁻ v, F u v := by
    funext u
    rw [normalizedSelfConvolutionENNReal, gaussianReal_of_var_ne_zero 0 one_ne_zero,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)]
    · apply lintegral_congr
      intro v
      simp only [Pi.mul_apply, F]
      ac_rfl
    · exact ((hh_meas.comp ((measurable_const.add measurable_id).div_const _)).mul
        (hh_meas.comp ((measurable_const.sub measurable_id).div_const _)))
  rwa [hEq]

theorem measurable_normalizedSelfConvolution
    {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (normalizedSelfConvolution h) := by
  exact (measurable_normalizedSelfConvolutionENNReal hh.ennreal_ofReal).ennreal_toReal

theorem normalizedSelfConvolution_nonneg (h : ℝ → ℝ) (u : ℝ) :
    0 ≤ normalizedSelfConvolution h u :=
  ENNReal.toReal_nonneg

private theorem ofReal_normalizedSelfConvolution
    {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, h x ≤ C) :
    (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u)) =
      normalizedSelfConvolutionENNReal (fun x ↦ ENNReal.ofReal (h x)) := by
  funext u
  rw [normalizedSelfConvolution]
  apply ENNReal.ofReal_toReal
  have hle := normalizedSelfConvolutionENNReal_le
    (h := fun x ↦ ENNReal.ofReal (h x)) (C := ENNReal.ofReal C)
    (fun x ↦ ENNReal.ofReal_le_ofReal (hC x)) u
  exact ne_of_lt (hle.trans_lt (by simp))

private theorem isLogConcave_normalizedSelfConvolution_of_le
    {h : ℝ → ℝ} (hh_meas : Measurable h)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_lc : IsLogConcave (fun x ↦ ENNReal.ofReal (h x))) :
    IsLogConcave (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u)) := by
  rw [ofReal_normalizedSelfConvolution hC]
  exact isLogConcave_normalizedSelfConvolutionENNReal hh_meas.ennreal_ofReal hh_lc

private theorem isBounded_range_normalizedSelfConvolution_of_le
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C) :
    Bornology.IsBounded (Set.range (normalizedSelfConvolution h)) := by
  apply (Metric.isBounded_Icc (0 : ℝ) (C ^ 2)).subset
  rintro y ⟨u, rfl⟩
  refine ⟨normalizedSelfConvolution_nonneg h u, ?_⟩
  rw [normalizedSelfConvolution]
  have hle := normalizedSelfConvolutionENNReal_le
    (h := fun x ↦ ENNReal.ofReal (h x)) (C := ENNReal.ofReal C)
    (fun x ↦ ENNReal.ofReal_le_ofReal (hC x)) u
  have hC_nonneg : 0 ≤ C := le_trans (hh_nonneg 0) (hC 0)
  simpa [hC_nonneg, pow_two] using ENNReal.toReal_mono (by simp) hle

private def normalizedAverage (p : ℝ × ℝ) : ℝ :=
  (p.1 + p.2) / Real.sqrt 2

private theorem measurable_normalizedAverage : Measurable normalizedAverage := by
  exact (measurable_fst.add measurable_snd).div_const _

private theorem rotation_pi_div_four_apply (p : ℝ × ℝ) :
    ContinuousLinearMap.rotation (Real.pi / 4) p =
      ((p.1 + p.2) / Real.sqrt 2, (p.2 - p.1) / Real.sqrt 2) := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  ext
  · simp only [ContinuousLinearMap.rotation_apply, Real.cos_pi_div_four,
      Real.sin_pi_div_four, smul_eq_mul]
    field_simp [ne_of_gt hsqrt_pos]
    rw [hsqrt_sq]
  · simp only [ContinuousLinearMap.rotation_apply, Real.cos_pi_div_four,
      Real.sin_pi_div_four, smul_eq_mul]
    field_simp [ne_of_gt hsqrt_pos]
    rw [hsqrt_sq]
    ring

private theorem lintegral_mul_normalizedSelfConvolutionENNReal
    {h φ : ℝ → ℝ≥0∞} (hh : Measurable h) (hφ : Measurable φ) :
    (∫⁻ u, φ u * normalizedSelfConvolutionENNReal h u ∂gaussianReal 0 1) =
      ∫⁻ p : ℝ × ℝ, φ (normalizedAverage p) * (h p.1 * h p.2)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let K : ℝ × ℝ → ℝ≥0∞ := fun p ↦
    φ p.1 * (h ((p.1 + p.2) / Real.sqrt 2) * h ((p.1 - p.2) / Real.sqrt 2))
  have hK : Measurable K :=
    (hφ.comp measurable_fst).mul
      ((hh.comp ((measurable_fst.add measurable_snd).div_const _)).mul
        (hh.comp ((measurable_fst.sub measurable_snd).div_const _)))
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation (E := ℝ) (Real.pi / 4))
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ⟨(ContinuousLinearMap.rotation (E := ℝ) (Real.pi / 4)).measurable,
      IsGaussian.map_rotation_eq_self (by simp) (Real.pi / 4)⟩
  calc
    (∫⁻ u, φ u * normalizedSelfConvolutionENNReal h u ∂gaussianReal 0 1) =
        ∫⁻ p : ℝ × ℝ, K p
          ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [MeasureTheory.lintegral_prod _ hK.aemeasurable]
      apply lintegral_congr
      intro u
      rw [normalizedSelfConvolutionENNReal, ← lintegral_const_mul]
      exact ((hh.comp ((measurable_const.add measurable_id).div_const _)).mul
        (hh.comp ((measurable_const.sub measurable_id).div_const _)))
    _ = ∫⁻ p : ℝ × ℝ,
          K (ContinuousLinearMap.rotation (Real.pi / 4) p)
          ∂(gaussianReal 0 1).prod (gaussianReal 0 1) :=
      (hrot.lintegral_comp hK).symm
    _ = ∫⁻ p : ℝ × ℝ, φ (normalizedAverage p) * (h p.1 * h p.2)
          ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
      apply lintegral_congr
      intro p
      rw [rotation_pi_div_four_apply]
      simp only [K, normalizedAverage]
      have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
      have hplus :
          ((p.1 + p.2) / Real.sqrt 2 + (p.2 - p.1) / Real.sqrt 2) /
              Real.sqrt 2 = p.2 := by
        field_simp [ne_of_gt hsqrt_pos]
        rw [hsqrt_sq]
        ring
      have hminus :
          ((p.1 + p.2) / Real.sqrt 2 - (p.2 - p.1) / Real.sqrt 2) /
              Real.sqrt 2 = p.1 := by
        field_simp [ne_of_gt hsqrt_pos]
        rw [hsqrt_sq]
        ring
      rw [hplus, hminus, mul_comm (h p.2)]

private theorem map_normalizedAverage_prod_withDensity
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    Measure.map normalizedAverage
        (((gaussianReal 0 1).withDensity h).prod
          ((gaussianReal 0 1).withDensity h)) =
      (gaussianReal 0 1).withDensity (normalizedSelfConvolutionENNReal h) := by
  classical
  rw [prod_withDensity hh hh]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_normalizedAverage hs,
    withDensity_apply _ hs, withDensity_apply _
      (measurable_normalizedAverage hs), ← lintegral_indicator hs,
    ← lintegral_indicator (measurable_normalizedAverage hs)]
  let φ : ℝ → ℝ≥0∞ := s.indicator (fun _ ↦ 1)
  have hφ : Measurable φ := measurable_const.indicator hs
  change (∫⁻ a : ℝ × ℝ,
      if normalizedAverage a ∈ s then h a.1 * h a.2 else 0
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
    ∫⁻ a : ℝ, if a ∈ s then normalizedSelfConvolutionENNReal h a else 0
      ∂gaussianReal 0 1
  simpa only [φ, Set.indicator, Function.comp_apply, ite_mul, one_mul, zero_mul] using
    (lintegral_mul_normalizedSelfConvolutionENNReal hh hφ).symm

private theorem normalizedSelfConvolution_law_of_le
    {h : ℝ → ℝ} (hh_meas : Measurable h)
    {C : ℝ} (hC : ∀ x, h x ≤ C) :
    Measure.map (fun p : ℝ × ℝ ↦ (p.1 + p.2) / Real.sqrt 2)
        (((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))).prod
          ((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x)))) =
      (gaussianReal 0 1).withDensity
        (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u)) := by
  change Measure.map normalizedAverage _ = _
  rw [ofReal_normalizedSelfConvolution hC]
  exact map_normalizedAverage_prod_withDensity hh_meas.ennreal_ofReal

private theorem integrable_of_measurable_nonneg_le
    {f : ℝ → ℝ} (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {C : ℝ} (hC : ∀ x, f x ≤ C) :
    Integrable f (gaussianReal 0 1) := by
  have hC_nonneg : 0 ≤ C := le_trans (hf_nonneg 0) (hC 0)
  refine Integrable.mono' (integrable_const C) hf_meas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
  exact hC x

private theorem withDensity_ofReal_mass
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    ((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))) Set.univ = 1 := by
  have hh_int := integrable_of_measurable_nonneg_le hh_meas hh_nonneg hC
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hh_int (ae_of_all _ hh_nonneg), hh_mass]
  simp

private theorem memLp_id_withDensity_ofReal_of_le
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C) :
    MemLp id 2 ((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop),
    integrable_withDensity_iff hh_meas.ennreal_ofReal (by simp)]
  have hbase := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq
  refine Integrable.mono' (hbase.mul_const C) (by fun_prop) ?_
  filter_upwards with x
  simp only [id_eq, ENNReal.toReal_ofReal (hh_nonneg x), Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg x) (hh_nonneg x))]
  exact mul_le_mul_of_nonneg_left (hC x) (sq_nonneg x)

private theorem withDensity_normalized_mass
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    ((gaussianReal 0 1).withDensity
      (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u))) Set.univ = 1 := by
  let ν := (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))
  have hν : ν Set.univ = 1 := by
    simpa only [ν] using withDensity_ofReal_mass hh_meas hh_nonneg hC hh_mass
  have hlaw := normalizedSelfConvolution_law_of_le hh_meas hC
  rw [← hlaw, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  rw [Set.preimage_univ]
  rw [show (Set.univ : Set (ℝ × ℝ)) = Set.univ ×ˢ Set.univ by ext; simp,
    Measure.prod_prod]
  simpa only [ν, one_mul] using congrArg₂ (fun a b : ℝ≥0∞ ↦ a * b) hν hν

private theorem integral_normalizedSelfConvolution_eq_one_of_le
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    ∫ u, normalizedSelfConvolution h u ∂gaussianReal 0 1 = 1 := by
  have hD_meas := measurable_normalizedSelfConvolution hh_meas
  have hD_nonneg := normalizedSelfConvolution_nonneg h
  have hD_bound (u : ℝ) : normalizedSelfConvolution h u ≤ C ^ 2 := by
    have hle := normalizedSelfConvolutionENNReal_le
      (h := fun x ↦ ENNReal.ofReal (h x)) (C := ENNReal.ofReal C)
      (fun x ↦ ENNReal.ofReal_le_ofReal (hC x)) u
    have hC_nonneg : 0 ≤ C := le_trans (hh_nonneg 0) (hC 0)
    simpa [normalizedSelfConvolution, hC_nonneg, pow_two] using
      ENNReal.toReal_mono (by simp) hle
  have hD_int := integrable_of_measurable_nonneg_le hD_meas hD_nonneg hD_bound
  have hmass := withDensity_normalized_mass hh_meas hh_nonneg hC hh_mass
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hD_int (ae_of_all _ hD_nonneg)] at hmass
  have hnonneg : 0 ≤ ∫ u, normalizedSelfConvolution h u ∂gaussianReal 0 1 :=
    integral_nonneg hD_nonneg
  simpa [ENNReal.ofReal_eq_one, hnonneg] using hmass

private theorem integral_id_normalizedSelfConvolution_eq_zero
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1)
    (hh_mean : ∫ x, x ∂((gaussianReal 0 1).withDensity
      (fun x ↦ ENNReal.ofReal (h x))) = 0) :
    ∫ u, u ∂((gaussianReal 0 1).withDensity
      (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u))) = 0 := by
  let ν := (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))
  have hν : ν Set.univ = 1 := by
    simpa only [ν] using withDensity_ofReal_mass hh_meas hh_nonneg hC hh_mass
  letI : IsProbabilityMeasure ν := ⟨hν⟩
  have hh_memLp := memLp_id_withDensity_ofReal_of_le hh_meas hh_nonneg hC
  have hh_memLpν : MemLp id 2 ν := by simpa only [ν] using hh_memLp
  change ∫ x, x ∂ν = 0 at hh_mean
  have hlaw := normalizedSelfConvolution_law_of_le hh_meas hC
  rw [← hlaw, integral_map (by fun_prop) (by fun_prop)]
  change ∫ p : ℝ × ℝ, (p.1 + p.2) / Real.sqrt 2 ∂ν.prod ν = 0
  have hfst : Integrable (fun p : ℝ × ℝ ↦ p.1) (ν.prod ν) :=
    (hh_memLpν.comp_fst ν).integrable (by norm_num)
  have hsnd : Integrable (fun p : ℝ × ℝ ↦ p.2) (ν.prod ν) :=
    (hh_memLpν.comp_snd ν).integrable (by norm_num)
  have hifst : (∫ p : ℝ × ℝ, p.1 ∂ν.prod ν) = ∫ x, x ∂ν := by
    simpa only [id_eq, probReal_univ, one_smul] using
      (integral_fun_fst (μ := ν) (ν := ν) id)
  have hisnd : (∫ p : ℝ × ℝ, p.2 ∂ν.prod ν) = ∫ x, x ∂ν := by
    simpa only [id_eq, probReal_univ, one_smul] using
      (integral_fun_snd (μ := ν) (ν := ν) id)
  rw [integral_div, integral_add hfst hsnd, hifst, hisnd, hh_mean]
  simp

private theorem integral_mul_normalizedSelfConvolution_eq_zero_of_le
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∫ x, x * h x ∂gaussianReal 0 1 = 0) :
    ∫ u, u * normalizedSelfConvolution h u ∂gaussianReal 0 1 = 0 := by
  have hh_mean : ∫ x, x ∂((gaussianReal 0 1).withDensity
      (fun x ↦ ENNReal.ofReal (h x))) = 0 := by
    change ∫ x, id x ∂((gaussianReal 0 1).withDensity
      (fun x ↦ ENNReal.ofReal (h x))) = 0
    rw [integral_withDensity_eq_integral_toReal_smul hh_meas.ennreal_ofReal
      (by simp) id]
    simpa only [id_eq, ENNReal.toReal_ofReal (hh_nonneg _), smul_eq_mul,
      mul_comm] using hh_barycenter
  have hout := integral_id_normalizedSelfConvolution_eq_zero
    hh_meas hh_nonneg hC hh_mass hh_mean
  change (∫ u, id u ∂((gaussianReal 0 1).withDensity
    (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u)))) = 0 at hout
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_normalizedSelfConvolution hh_meas).ennreal_ofReal
    (by simp) id] at hout
  simpa only [id_eq,
    ENNReal.toReal_ofReal (normalizedSelfConvolution_nonneg h _), smul_eq_mul,
    mul_comm] using hout

private theorem variance_id_normalizedSelfConvolution_of_le
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    {C : ℝ} (hC : ∀ x, h x ≤ C)
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    Var[id; (gaussianReal 0 1).withDensity
        (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u))] =
      Var[id; (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))] := by
  let ν := (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))
  have hν : ν Set.univ = 1 := by
    simpa only [ν] using withDensity_ofReal_mass hh_meas hh_nonneg hC hh_mass
  letI : IsProbabilityMeasure ν := ⟨hν⟩
  have hh_memLp := memLp_id_withDensity_ofReal_of_le hh_meas hh_nonneg hC
  have hh_memLpν : MemLp id 2 ν := by simpa only [ν] using hh_memLp
  have hlaw := normalizedSelfConvolution_law_of_le hh_meas hC
  rw [← hlaw, variance_id_map (by fun_prop)]
  change Var[fun p : ℝ × ℝ ↦ (p.1 + p.2) / Real.sqrt 2; ν.prod ν] =
    Var[id; ν]
  have hadd := variance_add_prod (X := id) (Y := id) hh_memLpν hh_memLpν
  rw [show (fun p : ℝ × ℝ ↦ (p.1 + p.2) / Real.sqrt 2) =
      fun p ↦ (Real.sqrt 2)⁻¹ * (id p.1 + id p.2) by
        funext p
        simp only [id_eq]
        ring,
    variance_const_mul, hadd]
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]
  ring

private theorem exists_upper_bound_of_isBounded_range
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) :
    ∃ C : ℝ, ∀ x, h x ≤ C := by
  obtain ⟨C, hC⟩ := hh_bounded.exists_norm_le
  refine ⟨C, fun x ↦ ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hh_nonneg x)] using
    hC (h x) ⟨x, rfl⟩

theorem isBounded_range_normalizedSelfConvolution
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) :
    Bornology.IsBounded (Set.range (normalizedSelfConvolution h)) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isBounded_range hh_nonneg hh_bounded
  exact isBounded_range_normalizedSelfConvolution_of_le hh_nonneg hC

theorem isLogConcave_normalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_lc : IsLogConcave (fun x ↦ ENNReal.ofReal (h x))) :
    IsLogConcave (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u)) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isBounded_range hh_nonneg hh_bounded
  exact isLogConcave_normalizedSelfConvolution_of_le hh_meas hC hh_lc

/-- Equality of finite density measures with the normalized-average pushforward.

When the input has mass one, this is an equality of probability laws. -/
theorem normalizedSelfConvolution_law
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) :
    Measure.map (fun p : ℝ × ℝ ↦ (p.1 + p.2) / Real.sqrt 2)
        (((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))).prod
          ((gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x)))) =
      (gaussianReal 0 1).withDensity
        (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u)) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isBounded_range hh_nonneg hh_bounded
  exact normalizedSelfConvolution_law_of_le hh_meas hC

theorem integral_normalizedSelfConvolution_eq_one
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    ∫ u, normalizedSelfConvolution h u ∂gaussianReal 0 1 = 1 := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isBounded_range hh_nonneg hh_bounded
  exact integral_normalizedSelfConvolution_eq_one_of_le
    hh_meas hh_nonneg hC hh_mass

theorem integral_mul_normalizedSelfConvolution_eq_zero
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∫ x, x * h x ∂gaussianReal 0 1 = 0) :
    ∫ u, u * normalizedSelfConvolution h u ∂gaussianReal 0 1 = 0 := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isBounded_range hh_nonneg hh_bounded
  exact integral_mul_normalizedSelfConvolution_eq_zero_of_le
    hh_meas hh_nonneg hC hh_mass hh_barycenter

theorem variance_id_normalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h))
    (hh_mass : ∫ x, h x ∂gaussianReal 0 1 = 1) :
    Var[id; (gaussianReal 0 1).withDensity
        (fun u ↦ ENNReal.ofReal (normalizedSelfConvolution h u))] =
      Var[id; (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h x))] := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isBounded_range hh_nonneg hh_bounded
  exact variance_id_normalizedSelfConvolution_of_le
    hh_meas hh_nonneg hC hh_mass

end WeakSimplex
