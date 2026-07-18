import WeakSimplexConjectureLean.Normal.Mills

/-!
# Scalar tilt functions

This module proves the derivative, strict-positivity, sign, and endpoint properties of the scalar
tilt functions used by the adaptive potential.
-/

namespace WeakSimplex

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

def r (s : ℝ) : ℝ := normalPDF s / normalCDF s

def H (s : ℝ) : ℝ := s + r s

def localLogMass (s : ℝ) : ℝ :=
  Real.log (normalCDF s) + (r s) ^ 2 / 2

lemma r_pos (s : ℝ) : 0 < r s := by
  exact div_pos (normalPDF_pos s) (normalCDF_pos s)

lemma hasDerivAt_r (s : ℝ) :
    HasDerivAt r (-r s * H s) s := by
  unfold r
  refine ((hasDerivAt_normalPDF s).div (hasDerivAt_normalCDF s)
    (normalCDF_pos s).ne').congr_deriv ?_
  simp only [H, r]
  field_simp [(normalCDF_pos s).ne']
  ring

lemma hasDerivAt_H (s : ℝ) :
    HasDerivAt H (1 - s * r s - (r s) ^ 2) s := by
  unfold H
  refine ((hasDerivAt_id s).add (hasDerivAt_r s)).congr_deriv ?_
  simp only [H]
  ring

private lemma integrable_normalPDF : Integrable normalPDF := by
  exact integrable_gaussianPDFReal 0 1

private lemma integrable_mul_normalPDF :
    Integrable (fun x : ℝ ↦ x * normalPDF x) := by
  have hgauss : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) := by
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hgauss
  simpa [normalPDF] using hgauss

private lemma integrable_sq_mul_normalPDF :
    Integrable (fun x : ℝ ↦ x ^ 2 * normalPDF x) := by
  have hgauss : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hgauss
  simpa [normalPDF] using hgauss

private lemma integrable_centered_sq_normalPDF (s : ℝ) :
    Integrable (fun x : ℝ ↦ (x + r s) ^ 2 * normalPDF x) := by
  have hsum : Integrable (fun x : ℝ ↦ x ^ 2 * normalPDF x +
      (2 * r s) * (x * normalPDF x) + (r s) ^ 2 * normalPDF x) :=
    (integrable_sq_mul_normalPDF.add
      (integrable_mul_normalPDF.const_mul (2 * r s))).add
      (integrable_normalPDF.const_mul ((r s) ^ 2))
  exact hsum.congr (ae_of_all _ fun x ↦ by ring)

private lemma centered_sq_integral (s : ℝ) :
    (∫ x in Set.Iic s, (x + r s) ^ 2 * normalPDF x) =
      normalCDF s * (1 - s * r s - (r s) ^ 2) := by
  have hsq : IntegrableOn (fun x : ℝ ↦ x ^ 2 * normalPDF x) (Set.Iic s) :=
    integrable_sq_mul_normalPDF.integrableOn
  have hfirst : IntegrableOn (fun x : ℝ ↦ (2 * r s) * (x * normalPDF x))
      (Set.Iic s) := (integrable_mul_normalPDF.const_mul (2 * r s)).integrableOn
  have hzero : IntegrableOn (fun x : ℝ ↦ (r s) ^ 2 * normalPDF x) (Set.Iic s) :=
    (integrable_normalPDF.const_mul ((r s) ^ 2)).integrableOn
  calc
    (∫ x in Set.Iic s, (x + r s) ^ 2 * normalPDF x) =
        ∫ x in Set.Iic s, x ^ 2 * normalPDF x +
          (2 * r s) * (x * normalPDF x) + (r s) ^ 2 * normalPDF x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by ring
    _ = (∫ x in Set.Iic s, x ^ 2 * normalPDF x) +
        (∫ x in Set.Iic s, (2 * r s) * (x * normalPDF x)) +
        ∫ x in Set.Iic s, (r s) ^ 2 * normalPDF x := by
      calc
        (∫ x in Set.Iic s, x ^ 2 * normalPDF x +
            (2 * r s) * (x * normalPDF x) + (r s) ^ 2 * normalPDF x) =
            (∫ x in Set.Iic s, x ^ 2 * normalPDF x +
              (2 * r s) * (x * normalPDF x)) +
              ∫ x in Set.Iic s, (r s) ^ 2 * normalPDF x := by
          exact integral_add (hsq.add hfirst) hzero
        _ = (∫ x in Set.Iic s, x ^ 2 * normalPDF x) +
            (∫ x in Set.Iic s, (2 * r s) * (x * normalPDF x)) +
            ∫ x in Set.Iic s, (r s) ^ 2 * normalPDF x := by
          rw [integral_add hsq hfirst]
    _ = (normalCDF s - s * normalPDF s) +
        (2 * r s) * (-normalPDF s) + (r s) ^ 2 * normalCDF s := by
      rw [truncated_second_moment, integral_const_mul, truncated_first_moment,
        integral_const_mul]
      rfl
    _ = normalCDF s * (1 - s * r s - (r s) ^ 2) := by
      have hpdf : normalPDF s = r s * normalCDF s := by
        rw [r]
        field_simp [(normalCDF_pos s).ne']
      rw [hpdf]
      ring

private lemma centered_sq_integral_pos (s : ℝ) :
    0 < ∫ x in Set.Iic s, (x + r s) ^ 2 * normalPDF x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg _) (normalPDF_pos x).le)
    (integrable_centered_sq_normalPDF s).integrableOn).2
  rw [show Function.support (fun x : ℝ ↦ (x + r s) ^ 2 * normalPDF x) =
      {x | x ≠ -r s} by
    ext x
    simp only [Function.mem_support, Set.mem_setOf_eq]
    constructor
    · intro h hx
      apply h
      rw [hx]
      norm_num
    · intro hx
      apply mul_ne_zero
      · apply pow_ne_zero
        intro h
        apply hx
        linarith
      · exact (normalPDF_pos x).ne']
  rw [show {x : ℝ | x ≠ -r s} ∩ Set.Iic s = Set.Iic s \ {-r s} by
    ext
    simp [and_comm]]
  rw [MeasureTheory.measure_sdiff_null ((Set.finite_singleton (-r s)).measure_zero volume),
    Real.volume_Iic]
  exact ENNReal.zero_lt_top

lemma H_deriv_pos (s : ℝ) :
    0 < 1 - s * r s - (r s) ^ 2 := by
  have hpos := centered_sq_integral_pos s
  rw [centered_sq_integral] at hpos
  nlinarith [normalCDF_pos s]

lemma hasDerivAt_localLogMass (s : ℝ) :
    HasDerivAt localLogMass
      (r s * (1 - s * r s - (r s) ^ 2)) s := by
  unfold localLogMass
  refine (((hasDerivAt_normalCDF s).log (normalCDF_pos s).ne').add
    (((hasDerivAt_r s).pow 2).div_const 2)).congr_deriv ?_
  rw [show normalPDF s / normalCDF s = r s by rfl]
  simp only [H]
  ring

private lemma tendsto_normalPDF_atTop : Tendsto normalPDF atTop (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (f' := fun x : ℝ ↦ -(x * normalPDF x))
  · intro x _
    refine (hasDerivAt_normalPDF x).congr_deriv ?_
    ring
  · exact integrable_mul_normalPDF.neg.integrableOn
  · exact integrable_normalPDF.integrableOn

private lemma tendsto_r_atTop : Tendsto r atTop (𝓝 0) := by
  change Tendsto (normalPDF / normalCDF) atTop (𝓝 0)
  simpa only [zero_div] using
    tendsto_normalPDF_atTop.div tendsto_normalCDF_atTop one_ne_zero

lemma localLogMass_tendsto_atTop :
    Tendsto localLogMass atTop (𝓝 0) := by
  have hlog : Tendsto (fun s ↦ Real.log (normalCDF s)) atTop (𝓝 0) := by
    simpa only [Real.log_one] using tendsto_normalCDF_atTop.log one_ne_zero
  have hr : Tendsto (fun s ↦ (r s) ^ 2 / 2) atTop (𝓝 0) := by
    have h := (tendsto_r_atTop.pow 2).div_const 2
    norm_num at h
    exact h
  change Tendsto (fun s ↦ Real.log (normalCDF s) + (r s) ^ 2 / 2) atTop (𝓝 0)
  simpa only [zero_add] using hlog.add hr

lemma localLogMass_neg (s : ℝ) :
    localLogMass s < 0 := by
  have hstrict : StrictMono localLogMass := strictMono_of_hasDerivAt_pos
    hasDerivAt_localLogMass fun x ↦ mul_pos (r_pos x) (H_deriv_pos x)
  calc
    localLogMass s < localLogMass (s + 1) := hstrict (by linarith)
    _ ≤ 0 := hstrict.monotone.ge_of_tendsto localLogMass_tendsto_atTop (s + 1)

private lemma normalPDF_neg (x : ℝ) : normalPDF (-x) = normalPDF x := by
  simp only [normalPDF, gaussianPDFReal]
  congr 2
  ring

private lemma r_neg_le (t : ℝ) (ht : 0 < t) :
    r (-t) ≤ t + 1 / t := by
  have hfactor : 0 ≤ (1 + t ^ 2) / t := (div_nonneg (by positivity) ht.le)
  have h := mul_le_mul_of_nonneg_left (mills_lower t ht) hfactor
  have hleft : (1 + t ^ 2) / t *
      (t / (1 + t ^ 2) * normalPDF t) = normalPDF t := by
    field_simp [ht.ne']
  have hright : (1 + t ^ 2) / t * normalCDF (-t) =
      (t + 1 / t) * normalCDF (-t) := by
    field_simp [ht.ne']
    ring
  rw [hleft, hright] at h
  apply (div_le_iff₀ (normalCDF_pos (-t))).2
  simpa only [r, normalPDF_neg] using h

private lemma log_normalPDF_div (t : ℝ) (ht : 0 < t) :
    Real.log (normalPDF t / t) =
      -(t ^ 2) / 2 - Real.log t - Real.log (Real.sqrt (2 * Real.pi)) := by
  rw [show normalPDF t = (Real.sqrt (2 * Real.pi))⁻¹ *
    Real.exp (-(t ^ 2) / 2) by norm_num [normalPDF, gaussianPDFReal]]
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  rw [Real.log_div (mul_ne_zero (inv_ne_zero hsqrt.ne') (Real.exp_ne_zero _)) ht.ne',
    Real.log_mul (inv_ne_zero hsqrt.ne') (Real.exp_ne_zero _), Real.log_inv,
    Real.log_exp]
  ring

private lemma localLogMass_neg_le (t : ℝ) (ht : 0 < t) :
    localLogMass (-t) ≤
      1 + 1 / (2 * t ^ 2) - Real.log t - Real.log (Real.sqrt (2 * Real.pi)) := by
  have hlog : Real.log (normalCDF (-t)) ≤ Real.log (normalPDF t / t) :=
    Real.log_le_log (normalCDF_pos (-t)) (mills_upper t ht)
  have hrnonneg : 0 ≤ r (-t) := (r_pos (-t)).le
  have hboundnonneg : 0 ≤ t + 1 / t := add_nonneg ht.le (one_div_nonneg.mpr ht.le)
  have hrsq : (r (-t)) ^ 2 ≤ (t + 1 / t) ^ 2 :=
    (sq_le_sq₀ hrnonneg hboundnonneg).2 (r_neg_le t ht)
  calc
    localLogMass (-t) ≤
        Real.log (normalPDF t / t) + (t + 1 / t) ^ 2 / 2 := by
      exact add_le_add hlog (div_le_div_of_nonneg_right hrsq (by norm_num))
    _ = 1 + 1 / (2 * t ^ 2) - Real.log t -
        Real.log (Real.sqrt (2 * Real.pi)) := by
      rw [log_normalPDF_div t ht]
      field_simp [ht.ne']
      ring

private lemma tendsto_millsEnvelope_atTop :
    Tendsto (fun t : ℝ ↦ 1 + 1 / (2 * t ^ 2) - Real.log t -
      Real.log (Real.sqrt (2 * Real.pi))) atTop atBot := by
  have hpow : Tendsto (fun t : ℝ ↦ t ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  have hinv : Tendsto (fun t : ℝ ↦ (t ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hsmall : Tendsto (fun t : ℝ ↦ 1 / (2 * t ^ 2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, zero_mul] using
      hinv.mul_const (1 / 2 : ℝ)
  have hfinite : Tendsto (fun t : ℝ ↦ 1 + 1 / (2 * t ^ 2) -
      Real.log (Real.sqrt (2 * Real.pi))) atTop
      (𝓝 (1 - Real.log (Real.sqrt (2 * Real.pi)))) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hsmall).sub tendsto_const_nhds
  have hneglog : Tendsto (fun t : ℝ ↦ -Real.log t) atTop atBot :=
    tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop
  convert hfinite.add_atBot hneglog using 1
  funext t
  ring

private lemma tendsto_localLogMass_neg_atTop :
    Tendsto (fun t : ℝ ↦ localLogMass (-t)) atTop atBot := by
  apply tendsto_atBot.2
  intro b
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    tendsto_millsEnvelope_atTop.eventually (eventually_le_atBot b)] with t ht hb
  exact (localLogMass_neg_le t ht).trans hb

lemma localLogMass_tendsto_atBot :
    Tendsto localLogMass atBot atBot := by
  have h := tendsto_localLogMass_neg_atTop.comp tendsto_neg_atBot_atTop
  change Tendsto (fun s : ℝ ↦ localLogMass (-(-s))) atBot atBot at h
  simpa only [neg_neg] using h

end

end WeakSimplex
