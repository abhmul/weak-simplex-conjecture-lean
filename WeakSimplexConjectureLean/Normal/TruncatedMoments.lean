import WeakSimplexConjectureLean.Normal.PDFCDF

namespace WeakSimplex

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

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

private lemma integrable_normalPDF : Integrable normalPDF := by
  exact integrable_gaussianPDFReal 0 1

private lemma tendsto_normalPDF_atBot : Tendsto normalPDF atBot (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (f' := fun x : ℝ ↦ -(x * normalPDF x))
  · intro x _
    refine (hasDerivAt_normalPDF x).congr_deriv ?_
    ring
  · exact integrable_mul_normalPDF.neg.integrableOn
  · exact integrable_normalPDF.integrableOn

private lemma hasDerivAt_mul_normalPDF (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * normalPDF y)
      (normalPDF x - x ^ 2 * normalPDF x) x := by
  refine ((hasDerivAt_id x).mul (hasDerivAt_normalPDF x)).congr_deriv ?_
  simp only [id_eq]
  ring

private lemma integrable_deriv_mul_normalPDF :
    Integrable (fun x : ℝ ↦ normalPDF x - x ^ 2 * normalPDF x) :=
  integrable_normalPDF.sub integrable_sq_mul_normalPDF

private lemma tendsto_mul_normalPDF_atBot :
    Tendsto (fun x : ℝ ↦ x * normalPDF x) atBot (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (f' := fun x : ℝ ↦ normalPDF x - x ^ 2 * normalPDF x)
  · exact fun x _ ↦ hasDerivAt_mul_normalPDF x
  · exact integrable_deriv_mul_normalPDF.integrableOn
  · exact integrable_mul_normalPDF.integrableOn

lemma truncated_first_moment (s : ℝ) :
    ∫ x in Set.Iic s, x * normalPDF x = -normalPDF s := by
  have hderiv : ∀ x ∈ Set.Iic s,
      HasDerivAt (fun y : ℝ ↦ -normalPDF y) (x * normalPDF x) x := by
    intro x _
    refine (hasDerivAt_normalPDF x).neg.congr_deriv ?_
    ring
  have hlim : Tendsto (fun x : ℝ ↦ -normalPDF x) atBot (𝓝 0) := by
    simpa only [neg_zero] using tendsto_normalPDF_atBot.neg
  simpa using integral_Iic_of_hasDerivAt_of_tendsto' hderiv
    integrable_mul_normalPDF.integrableOn hlim

private lemma hasDerivAt_second_antiderivative (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ normalCDF y - y * normalPDF y)
      (x ^ 2 * normalPDF x) x := by
  refine ((hasDerivAt_normalCDF x).sub (hasDerivAt_mul_normalPDF x)).congr_deriv ?_
  ring

private lemma tendsto_second_antiderivative_atBot :
    Tendsto (fun x : ℝ ↦ normalCDF x - x * normalPDF x) atBot (𝓝 0) := by
  simpa only [sub_zero] using tendsto_normalCDF_atBot.sub tendsto_mul_normalPDF_atBot

lemma truncated_second_moment (s : ℝ) :
    ∫ x in Set.Iic s, x ^ 2 * normalPDF x = normalCDF s - s * normalPDF s := by
  have hderiv : ∀ x ∈ Set.Iic s,
      HasDerivAt (fun y : ℝ ↦ normalCDF y - y * normalPDF y)
        (x ^ 2 * normalPDF x) x := by
    exact fun x _ ↦ hasDerivAt_second_antiderivative x
  simpa using integral_Iic_of_hasDerivAt_of_tendsto' hderiv
    integrable_sq_mul_normalPDF.integrableOn tendsto_second_antiderivative_atBot

end

end WeakSimplex
