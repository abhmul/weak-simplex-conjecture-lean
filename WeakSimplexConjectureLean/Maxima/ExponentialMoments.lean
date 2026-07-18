import WeakSimplexConjectureLean.Maxima.StochasticOrder
import Mathlib.MeasureTheory.Integral.Layercake

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WeakSimplex

private theorem exp_mul_coordinateMax_le_sum
    {m : ℕ} (hm : 0 < m) (μ : ℝ) (x : Coord m) :
    Real.exp (μ * coordinateMax hm x) ≤ ∑ i : Fin m, Real.exp (μ * x i) := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)) (fun i : Fin m ↦ x i)
  rw [coordinateMax, hmax]
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (μ * x j)).le) hi

private theorem integrable_exp_mul_coordinate
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (μ : ℝ) (i : Fin m) :
    Integrable (fun x : Coord m ↦ Real.exp (μ * x i))
      (multivariateGaussian (0 : Coord m) R) := by
  have hmap := measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord m)) hR (i := i)
  have hmapOne : MeasurePreserving (fun x : Coord m ↦ x i)
      (multivariateGaussian (0 : Coord m) R) (gaussianReal 0 1) := by
    simpa [hdiag i] using hmap
  have hint := hmapOne.integrable_comp_of_integrable
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) μ)
  simpa [Function.comp_def] using hint

private theorem integrable_exp_mul_coordinateMax
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (μ : ℝ) :
    Integrable (fun x : Coord m ↦ Real.exp (μ * coordinateMax hm x))
      (multivariateGaussian (0 : Coord m) R) := by
  have hsum : Integrable (fun x : Coord m ↦ ∑ i : Fin m, Real.exp (μ * x i))
      (multivariateGaussian (0 : Coord m) R) := by
    exact integrable_finsetSum Finset.univ fun i _ ↦
      integrable_exp_mul_coordinate R hR hdiag μ i
  apply hsum.mono_nonneg
  · exact (((continuous_coordinateMax hm).measurable.const_mul μ).exp).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall fun x ↦ exp_mul_coordinateMax_le_sum hm μ x

private theorem lintegral_exp_mul_le_of_tail_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : Measure α) (q : Measure β) (U : α → ℝ) (V : β → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (htail : ∀ c : ℝ, p {x | c < U x} ≤ q {x | c < V x})
    (μ : ℝ) (hμ : 0 < μ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (μ * U x)) ∂p) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (μ * V x)) ∂q := by
  rw [lintegral_eq_lintegral_meas_lt p
    (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos (μ * U x)).le)
    (hU.const_mul μ).exp.aemeasurable]
  rw [lintegral_eq_lintegral_meas_lt q
    (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos (μ * V x)).le)
    (hV.const_mul μ).exp.aemeasurable]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  have hsetU : {x : α | t < Real.exp (μ * U x)} = {x | Real.log t / μ < U x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← Real.log_lt_iff_lt_exp ht, div_lt_iff₀ hμ]
    simp only [mul_comm]
  have hsetV : {x : β | t < Real.exp (μ * V x)} = {x | Real.log t / μ < V x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← Real.log_lt_iff_lt_exp ht, div_lt_iff₀ hμ]
    simp only [mul_comm]
  rw [hsetU, hsetV]
  exact htail (Real.log t / μ)

private theorem mgf_le_of_tail_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : Measure α) (q : Measure β) [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    (U : α → ℝ) (V : β → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hintU : ∀ μ : ℝ, Integrable (fun x ↦ Real.exp (μ * U x)) p)
    (hintV : ∀ μ : ℝ, Integrable (fun x ↦ Real.exp (μ * V x)) q)
    (htail : ∀ c : ℝ, p {x | c < U x} ≤ q {x | c < V x})
    (μ : ℝ) (hμ : 0 ≤ μ) :
    mgf U p μ ≤ mgf V q μ := by
  rcases hμ.eq_or_lt with rfl | hμ
  · simp [mgf]
  · have hlin := lintegral_exp_mul_le_of_tail_le p q U V hU hV htail μ hμ
    have hnonnegU : 0 ≤ᵐ[p] fun x ↦ Real.exp (μ * U x) :=
      Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
    have hnonnegV : 0 ≤ᵐ[q] fun x ↦ Real.exp (μ * V x) :=
      Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
    rw [← ofReal_integral_eq_lintegral_ofReal (hintU μ) hnonnegU,
      ← ofReal_integral_eq_lintegral_ofReal (hintV μ) hnonnegV] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ (Real.exp_pos _).le)).mp hlin

/-- Admissible Gaussian coordinate maxima have no larger nonnegative exponential moments than
the independent standard-Gaussian maximum. -/
theorem gaussianMax_mgf_le_regularSimplex
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    mgf (coordinateMax hm) (multivariateGaussian 0 R) μ ≤
      mgf (coordinateMax hm)
        (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) μ := by
  apply mgf_le_of_tail_le
  · exact (continuous_coordinateMax hm).measurable
  · exact (continuous_coordinateMax hm).measurable
  · intro t
    exact integrable_exp_mul_coordinateMax hm R hR.1.1 hR.1.2 t
  · intro t
    exact integrable_exp_mul_coordinateMax hm 1 Matrix.PosSemidef.one
      (fun i ↦ by simp) t
  · exact coordinateMax_tail_le_iid hm R hR
  · exact hμ

end WeakSimplex
