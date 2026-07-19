import WeakSimplexConjectureLean.Maxima.ExponentialMoments

/-!
# U10 strict exponential-moment spike

This file proves the strict layer-cake step on the positive-measure level interval `[1, 2]`, with
explicit integrability hypotheses at the selected positive parameter. The Gaussian theorems remain
conditional only on the frozen strict-tail statement proved by the first U10 file from U09.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WeakSimplex

/-- The frozen strict-tail statement supplied by the first U10 file. -/
def StrictCoordinateMaxTailStatement : Prop :=
  ∀ {m : ℕ} (hm : 0 < m),
    ∀ (R : Matrix (Fin m) (Fin m) ℝ),
      IsWeakSimplexCov R →
      R ≠ (1 : Matrix (Fin m) (Fin m) ℝ) →
      ∀ c : ℝ,
        (multivariateGaussian 0 R) {x | c < coordinateMax hm x} <
          (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ))
            {x | c < coordinateMax hm x}

private theorem exp_tail_set_eq
    {α : Type*} (U : α → ℝ) (t μ : ℝ) (ht : 0 < t) (hμ : 0 < μ) :
    {x | t < Real.exp (μ * U x)} = {x | Real.log t / μ < U x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  rw [← Real.log_lt_iff_lt_exp ht, div_lt_iff₀ hμ]
  simp only [mul_comm]

private theorem lintegral_exp_mul_lt_of_tail_lt
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : Measure α) (q : Measure β)
    (U : α → ℝ) (V : β → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (μ : ℝ) (hμ : 0 < μ)
    (hintU : Integrable (fun x ↦ Real.exp (μ * U x)) p)
    (hintV : Integrable (fun x ↦ Real.exp (μ * V x)) q)
    (htail_le : ∀ c : ℝ, p {x | c < U x} ≤ q {x | c < V x})
    (htail_lt : ∀ c : ℝ, p {x | c < U x} < q {x | c < V x}) :
    ((∫⁻ x, ENNReal.ofReal (Real.exp (μ * U x)) ∂p) <
      (∫⁻ x, ENNReal.ofReal (Real.exp (μ * V x)) ∂q)) ∧
      ((∫⁻ x, ENNReal.ofReal (Real.exp (μ * V x)) ∂q) ≠ ∞) := by
  let F : ℝ → ℝ≥0∞ := fun t ↦ p {x | t < Real.exp (μ * U x)}
  let G : ℝ → ℝ≥0∞ := fun t ↦ q {x | t < Real.exp (μ * V x)}
  have hnonnegU : 0 ≤ᵐ[p] fun x ↦ Real.exp (μ * U x) :=
    Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  have hnonnegV : 0 ≤ᵐ[q] fun x ↦ Real.exp (μ * V x) :=
    Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  have hlayerU :
      (∫⁻ x, ENNReal.ofReal (Real.exp (μ * U x)) ∂p) =
        ∫⁻ t in Set.Ioi 0, F t := by
    simpa [F] using lintegral_eq_lintegral_meas_lt p hnonnegU
      (hU.const_mul μ).exp.aemeasurable
  have hlayerV :
      (∫⁻ x, ENNReal.ofReal (Real.exp (μ * V x)) ∂q) =
        ∫⁻ t in Set.Ioi 0, G t := by
    simpa [G] using lintegral_eq_lintegral_meas_lt q hnonnegV
      (hV.const_mul μ).exp.aemeasurable
  constructor
  · rw [hlayerU, hlayerV]
    have hGanti : Antitone G := by
      intro a b hab
      exact measure_mono fun x hx ↦ hab.trans_lt hx
    have hGmeas : Measurable G := hGanti.measurable
    have hFfinite : (∫⁻ t in Set.Ioi 0, F t) ≠ ∞ := by
      rw [← hlayerU]
      rw [← ofReal_integral_eq_lintegral_ofReal hintU hnonnegU]
      exact ENNReal.ofReal_ne_top
    have hle : F ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] G := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change p {x | t < Real.exp (μ * U x)} ≤ q {x | t < Real.exp (μ * V x)}
      rw [exp_tail_set_eq U t μ ht hμ, exp_tail_set_eq V t μ ht hμ]
      exact htail_le (Real.log t / μ)
    have hIcc_pos :
        (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Icc (1 : ℝ) 2) ≠ 0 := by
      rw [Measure.restrict_apply measurableSet_Icc]
      have hinter : Set.Icc (1 : ℝ) 2 ∩ Set.Ioi 0 = Set.Icc 1 2 :=
        Set.inter_eq_left.2 fun t ht ↦ lt_of_lt_of_le zero_lt_one ht.1
      rw [hinter]
      norm_num [Real.volume_Icc]
    have hstrict :
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          t ∈ Set.Icc (1 : ℝ) 2 → F t < G t := by
      filter_upwards with t
      intro ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
      change p {x | t < Real.exp (μ * U x)} < q {x | t < Real.exp (μ * V x)}
      rw [exp_tail_set_eq U t μ htpos hμ, exp_tail_set_eq V t μ htpos hμ]
      exact htail_lt (Real.log t / μ)
    exact lintegral_strict_mono_of_ae_le_of_ae_lt_on
      hGmeas.aemeasurable hFfinite hle hIcc_pos hstrict
  · rw [← ofReal_integral_eq_lintegral_ofReal hintV hnonnegV]
    exact ENNReal.ofReal_ne_top

private theorem mgf_lt_of_tail_lt
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : Measure α) (q : Measure β)
    (U : α → ℝ) (V : β → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (μ : ℝ) (hμ : 0 < μ)
    (hintU : Integrable (fun x ↦ Real.exp (μ * U x)) p)
    (hintV : Integrable (fun x ↦ Real.exp (μ * V x)) q)
    (htail_le : ∀ c : ℝ, p {x | c < U x} ≤ q {x | c < V x})
    (htail_lt : ∀ c : ℝ, p {x | c < U x} < q {x | c < V x}) :
    mgf U p μ < mgf V q μ := by
  have hlin := lintegral_exp_mul_lt_of_tail_lt
    p q U V hU hV μ hμ hintU hintV htail_le htail_lt |>.1
  have hnonnegU : 0 ≤ᵐ[p] fun x ↦ Real.exp (μ * U x) :=
    Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  have hnonnegV : 0 ≤ᵐ[q] fun x ↦ Real.exp (μ * V x) :=
    Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hintU hnonnegU,
    ← ofReal_integral_eq_lintegral_ofReal hintV hnonnegV] at hlin
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (integral_nonneg fun _ ↦ (Real.exp_pos _).le)).mp hlin

private theorem exp_mul_coordinateMax_le_sum_u10
    {m : ℕ} (hm : 0 < m) (μ : ℝ) (x : Coord m) :
    Real.exp (μ * coordinateMax hm x) ≤ ∑ i : Fin m, Real.exp (μ * x i) := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)) (fun i : Fin m ↦ x i)
  rw [coordinateMax, hmax]
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (μ * x j)).le) hi

private theorem integrable_exp_mul_coordinate_u10
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

private theorem integrable_exp_mul_coordinateMax_u10
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (μ : ℝ) :
    Integrable (fun x : Coord m ↦ Real.exp (μ * coordinateMax hm x))
      (multivariateGaussian (0 : Coord m) R) := by
  have hsum : Integrable (fun x : Coord m ↦ ∑ i : Fin m, Real.exp (μ * x i))
      (multivariateGaussian (0 : Coord m) R) := by
    exact integrable_finsetSum Finset.univ fun i _ ↦
      integrable_exp_mul_coordinate_u10 R hR hdiag μ i
  apply hsum.mono_nonneg
  · exact (((continuous_coordinateMax hm).measurable.const_mul μ).exp).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall fun x ↦ exp_mul_coordinateMax_le_sum_u10 hm μ x

/-- The frozen U10 MGF theorem, conditional only on the frozen U09 theorem. -/
theorem gaussianMax_mgf_lt_regularSimplex_of_strictTail
    (strictTail : StrictCoordinateMaxTailStatement)
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (hRne : R ≠ (1 : Matrix (Fin m) (Fin m) ℝ))
    (μ : ℝ) (hμ : 0 < μ) :
    mgf (coordinateMax hm) (multivariateGaussian 0 R) μ <
      mgf (coordinateMax hm)
        (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) μ := by
  apply mgf_lt_of_tail_lt
  · exact (continuous_coordinateMax hm).measurable
  · exact (continuous_coordinateMax hm).measurable
  · exact hμ
  · exact integrable_exp_mul_coordinateMax_u10 hm R hR.1.1 hR.1.2 μ
  · exact integrable_exp_mul_coordinateMax_u10 hm 1 Matrix.PosSemidef.one
      (fun i ↦ by simp) μ
  · exact coordinateMax_tail_le_iid hm R hR
  · exact strictTail hm R hR hRne

/-- The frozen U10 MGF equality characterization, conditional only on U09. -/
theorem gaussianMax_mgf_eq_regularSimplex_iff_of_strictTail
    (strictTail : StrictCoordinateMaxTailStatement)
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (μ : ℝ) (hμ : 0 < μ) :
    mgf (coordinateMax hm) (multivariateGaussian 0 R) μ =
        mgf (coordinateMax hm)
          (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) μ ↔
      R = (1 : Matrix (Fin m) (Fin m) ℝ) := by
  constructor
  · intro heq
    by_contra hRne
    have hlt := gaussianMax_mgf_lt_regularSimplex_of_strictTail
      strictTail hm R hR hRne μ hμ
    exact (ne_of_lt hlt) heq
  · intro hRone
    subst R
    rfl

end WeakSimplex
