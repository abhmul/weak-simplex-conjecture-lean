import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

namespace WeakSimplex

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

def normalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

def normalCDF (x : ℝ) : ℝ := ∫ t in Set.Iic x, normalPDF t

private lemma continuous_normalPDF : Continuous normalPDF := by
  unfold normalPDF gaussianPDFReal
  fun_prop

private lemma integrable_normalPDF : Integrable normalPDF := by
  exact integrable_gaussianPDFReal 0 1

lemma normalPDF_pos (x : ℝ) : 0 < normalPDF x := by
  exact gaussianPDFReal_pos 0 1 x one_ne_zero

private lemma normalPDF_nonneg (x : ℝ) : 0 ≤ normalPDF x := (normalPDF_pos x).le

private lemma normalCDF_nonneg (x : ℝ) : 0 ≤ normalCDF x := by
  exact integral_nonneg_of_ae (ae_of_all _ fun y ↦ normalPDF_nonneg y)

lemma hasDerivAt_normalPDF (x : ℝ) :
    HasDerivAt normalPDF (-x * normalPDF x) x := by
  have hpdf : normalPDF =
      fun y : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
    funext y
    norm_num [normalPDF, gaussianPDFReal]
  rw [hpdf]
  have hexp : HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / 2) (-x) x := by
    refine ((((hasDerivAt_id x).pow 2).neg.div_const 2).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      ring
    · exact Filter.Eventually.of_forall fun y ↦ by
        change -(y ^ 2) / 2 = -(y ^ 2) / 2
        rfl
  refine (((Real.hasDerivAt_exp _).comp x hexp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv ?_
  ring

lemma normalCDF_eq_measure_Iic (x : ℝ) :
    ENNReal.ofReal (normalCDF x) = (gaussianReal 0 1) (Set.Iic x) := by
  exact (gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Iic x)).symm

lemma normalCDF_pos (x : ℝ) : 0 < normalCDF x := by
  rw [normalCDF, setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun y ↦ normalPDF_nonneg y) integrable_normalPDF.integrableOn]
  have hsupp : Function.support normalPDF = Set.univ := by
    ext y
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (normalPDF_pos y).ne'
  rw [hsupp, Set.univ_inter, Real.volume_Iic]
  simp

lemma normalCDF_lt_one (x : ℝ) : normalCDF x < 1 := by
  have htail : 0 < ∫ y in Set.Ioi x, normalPDF y := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun y ↦ normalPDF_nonneg y) integrable_normalPDF.integrableOn]
    have hsupp : Function.support normalPDF = Set.univ := by
      ext y
      simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
      exact (normalPDF_pos y).ne'
    rw [hsupp, Set.univ_inter, Real.volume_Ioi]
    simp
  have hsum : normalCDF x + ∫ y in Set.Ioi x, normalPDF y = 1 := by
    rw [normalCDF, intervalIntegral.integral_Iic_add_Ioi
      integrable_normalPDF.integrableOn integrable_normalPDF.integrableOn]
    exact integral_gaussianPDFReal_eq_one 0 one_ne_zero
  linarith

lemma hasDerivAt_normalCDF (x : ℝ) : HasDerivAt normalCDF (normalPDF x) x := by
  have hFTC : HasDerivAt (fun u ↦ ∫ y in x..u, normalPDF y) (normalPDF x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (continuous_normalPDF.intervalIntegrable x x)
      continuous_normalPDF.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_normalPDF.continuousAt
  let C := ∫ y in Set.Iic x, normalPDF y
  have hEq : normalCDF = fun u ↦ C + ∫ y in x..u, normalPDF y := by
    funext u
    rw [normalCDF]
    change (∫ y in Set.Iic u, normalPDF y) = (∫ y in Set.Iic x, normalPDF y) + _
    have h := intervalIntegral.integral_Iic_sub_Iic
      (a := x) (b := u) integrable_normalPDF.integrableOn
      integrable_normalPDF.integrableOn
    linarith
  rw [hEq]
  change HasDerivAt
    ((fun _ : ℝ ↦ C) + fun u ↦ ∫ y in x..u, normalPDF y) (normalPDF x) x
  simpa only [zero_add] using (hasDerivAt_const x C).add hFTC

private lemma normalCDF_eq_cdf (x : ℝ) : normalCDF x = cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact (ENNReal.toReal_ofReal (normalCDF_nonneg x)).symm

lemma tendsto_normalCDF_atTop : Tendsto normalCDF atTop (𝓝 1) := by
  have hfun : normalCDF = cdf (gaussianReal 0 1) := funext normalCDF_eq_cdf
  rw [hfun]
  exact tendsto_cdf_atTop (gaussianReal 0 1)

lemma tendsto_normalCDF_atBot : Tendsto normalCDF atBot (𝓝 0) := by
  have hfun : normalCDF = cdf (gaussianReal 0 1) := funext normalCDF_eq_cdf
  rw [hfun]
  exact tendsto_cdf_atBot (gaussianReal 0 1)

end

end WeakSimplex
