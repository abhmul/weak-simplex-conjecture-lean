import WeakSimplexConjectureLean.Normal.TruncatedMoments

/-!
# Mills bounds for the standard normal distribution

This module proves the upper and lower one-sided Mills estimates needed for the scalar tilt
endpoints.
-/

namespace WeakSimplex

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

private lemma normalPDF_neg (x : ℝ) : normalPDF (-x) = normalPDF x := by
  simp only [normalPDF, gaussianPDFReal]
  congr 2
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

private lemma tendsto_normalPDF_atBot : Tendsto normalPDF atBot (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (f' := fun x : ℝ ↦ -(x * normalPDF x))
  · intro x _
    refine (hasDerivAt_normalPDF x).congr_deriv ?_
    ring
  · exact integrable_mul_normalPDF.neg.integrableOn
  · exact integrable_normalPDF.integrableOn

private lemma integrable_div_sq_normalPDF_Iic (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ normalPDF x / x ^ 2) (Set.Iic (-t)) := by
  have hdom : IntegrableOn (fun x : ℝ ↦ (1 / t ^ 2) * normalPDF x) (Set.Iic (-t)) :=
    (integrable_normalPDF.const_mul (1 / t ^ 2)).integrableOn
  change Integrable _ (volume.restrict (Set.Iic (-t)))
  change Integrable _ (volume.restrict (Set.Iic (-t))) at hdom
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ normalPDF x / x ^ 2)
      (volume.restrict (Set.Iic (-t))) := by
    exact ((measurable_gaussianPDFReal 0 1).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  refine hdom.mono hmeas ?_
  exact ae_restrict_of_forall_mem measurableSet_Iic fun x hx ↦ by
    change x ≤ -t at hx
    have hxt : t ≤ -x := by linarith
    have hsquare : t ^ 2 ≤ x ^ 2 := by nlinarith
    have hinv : 1 / x ^ 2 ≤ 1 / t ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos ht) hsquare
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (normalPDF_pos x).le (sq_nonneg x)),
      abs_of_nonneg (mul_nonneg (by positivity) (normalPDF_pos x).le)]
    calc
      normalPDF x / x ^ 2 = (1 / x ^ 2) * normalPDF x := by ring
      _ ≤ (1 / t ^ 2) * normalPDF x :=
        mul_le_mul_of_nonneg_right hinv (normalPDF_pos x).le

private lemma hasDerivAt_millsAntiderivative (t x : ℝ) (ht : 0 < t)
    (hx : x ∈ Set.Iic (-t)) :
    HasDerivAt (fun y : ℝ ↦ normalPDF y / (-y))
      (normalPDF x + normalPDF x / x ^ 2) x := by
  have hxneg : x < 0 := lt_of_le_of_lt hx (neg_neg_of_pos ht)
  have hx0 : x ≠ 0 := hxneg.ne
  refine ((hasDerivAt_normalPDF x).div (hasDerivAt_id x).neg (neg_ne_zero.mpr hx0)).congr_deriv ?_
  simp only [id_eq, Pi.neg_apply]
  field_simp [hx0]
  ring

private lemma mills_parts_identity (t : ℝ) (ht : 0 < t) :
    normalPDF t / t = normalCDF (-t) +
      ∫ x in Set.Iic (-t), normalPDF x / x ^ 2 := by
  have hdiv := integrable_div_sq_normalPDF_Iic t ht
  have hpdf : IntegrableOn normalPDF (Set.Iic (-t)) := integrable_normalPDF.integrableOn
  have hlim : Tendsto (fun x : ℝ ↦ normalPDF x / (-x)) atBot (𝓝 0) := by
    simpa only using tendsto_normalPDF_atBot.div_atTop tendsto_neg_atBot_atTop
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x hx ↦ hasDerivAt_millsAntiderivative t x ht hx) (hpdf.add hdiv) hlim
  rw [integral_add hpdf hdiv] at h
  simpa [normalCDF, normalPDF_neg] using h.symm

private lemma mills_remainder_le (t : ℝ) (ht : 0 < t) :
    (∫ x in Set.Iic (-t), normalPDF x / x ^ 2) ≤ normalCDF (-t) / t ^ 2 := by
  have hdiv := integrable_div_sq_normalPDF_Iic t ht
  have hdom : IntegrableOn (fun x : ℝ ↦ (1 / t ^ 2) * normalPDF x) (Set.Iic (-t)) :=
    (integrable_normalPDF.const_mul (1 / t ^ 2)).integrableOn
  have hmono : (∫ x in Set.Iic (-t), normalPDF x / x ^ 2) ≤
      ∫ x in Set.Iic (-t), (1 / t ^ 2) * normalPDF x := by
    refine integral_mono_ae hdiv hdom ?_
    exact ae_restrict_of_forall_mem measurableSet_Iic fun x hx ↦ by
      change x ≤ -t at hx
      have hxt : t ≤ -x := by linarith
      have hsquare : t ^ 2 ≤ x ^ 2 := by nlinarith
      have hinv : 1 / x ^ 2 ≤ 1 / t ^ 2 :=
        one_div_le_one_div_of_le (sq_pos_of_pos ht) hsquare
      calc
        normalPDF x / x ^ 2 = (1 / x ^ 2) * normalPDF x := by ring
        _ ≤ (1 / t ^ 2) * normalPDF x :=
          mul_le_mul_of_nonneg_right hinv (normalPDF_pos x).le
  calc
    (∫ x in Set.Iic (-t), normalPDF x / x ^ 2) ≤
        ∫ x in Set.Iic (-t), (1 / t ^ 2) * normalPDF x := hmono
    _ = normalCDF (-t) / t ^ 2 := by
      rw [integral_const_mul]
      simp only [normalCDF]
      ring

lemma mills_upper (t : ℝ) (ht : 0 < t) :
    normalCDF (-t) ≤ normalPDF t / t := by
  have hpdf : IntegrableOn normalPDF (Set.Iic (-t)) := integrable_normalPDF.integrableOn
  have hright : IntegrableOn (fun x : ℝ ↦ (-x / t) * normalPDF x) (Set.Iic (-t)) := by
    have h := integrable_mul_normalPDF.const_mul (-1 / t)
    exact h.congr (ae_of_all _ fun x ↦ by ring) |>.integrableOn
  have hmono : (∫ x in Set.Iic (-t), normalPDF x) ≤
      ∫ x in Set.Iic (-t), (-x / t) * normalPDF x := by
    refine integral_mono_ae hpdf hright ?_
    exact ae_restrict_of_forall_mem measurableSet_Iic fun x hx ↦ by
      change x ≤ -t at hx
      have hratio : 1 ≤ -x / t := (le_div_iff₀ ht).2 (by linarith)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hratio (normalPDF_pos x).le
  rw [← normalCDF] at hmono
  calc
    normalCDF (-t) ≤ ∫ x in Set.Iic (-t), (-x / t) * normalPDF x := hmono
    _ = (-1 / t) * ∫ x in Set.Iic (-t), x * normalPDF x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by ring
    _ = (-1 / t) * (-normalPDF (-t)) := by rw [truncated_first_moment]
    _ = normalPDF t / t := by rw [normalPDF_neg]; ring

lemma mills_lower (t : ℝ) (ht : 0 < t) :
    t / (1 + t ^ 2) * normalPDF t ≤ normalCDF (-t) := by
  have hparts := mills_parts_identity t ht
  have hrem := mills_remainder_le t ht
  have hmain : normalPDF t / t ≤ normalCDF (-t) + normalCDF (-t) / t ^ 2 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hmain (sq_nonneg t)
  have hleft : normalPDF t / t * t ^ 2 = t * normalPDF t := by
    field_simp [ht.ne']
  have hright :
      (normalCDF (-t) + normalCDF (-t) / t ^ 2) * t ^ 2 =
        normalCDF (-t) * (1 + t ^ 2) := by
    field_simp [ht.ne']
    ring
  have hscaled' : t * normalPDF t ≤ normalCDF (-t) * (1 + t ^ 2) := by
    rwa [hleft, hright] at hscaled
  rw [show t / (1 + t ^ 2) * normalPDF t =
    (t * normalPDF t) / (1 + t ^ 2) by ring]
  exact (div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using hscaled')

end

end WeakSimplex
