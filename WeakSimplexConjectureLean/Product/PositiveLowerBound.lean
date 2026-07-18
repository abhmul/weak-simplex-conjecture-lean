import WeakSimplexConjectureLean.Gaussian.DensityRatio
import WeakSimplexConjectureLean.Product.DyadicCLT
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace WeakSimplex

private theorem tendsto_measure_of_tendstoInDistribution_id
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : TendstoInDistribution (fun _ : ι ↦ id) l id μ ν) {s : Set ℝ}
    (hs : ν (frontier s) = 0) :
    Tendsto (fun i ↦ μ i s) l (𝓝 (ν s)) := by
  have hs' : (Measure.map id ν) (frontier s) = 0 := by
    simpa using hs
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (E := s) h.tendsto hs'
  simpa using ht

private theorem gaussianReal_frontier_Icc_eq_zero
    {v : ℝ≥0} (hv : v ≠ 0) {L : ℝ} (hL : 0 ≤ L) :
    gaussianReal 0 v (frontier (Icc (-L) L)) = 0 := by
  letI : NoAtoms (gaussianReal 0 v) := noAtoms_gaussianReal (μ := 0) hv
  rw [frontier_Icc (neg_le_self hL)]
  exact ((finite_singleton L).insert (-L)).measure_zero _

private theorem gaussianReal_Icc_pos
    {v : ℝ≥0} (hv : v ≠ 0) {L : ℝ} (hL : 0 < L) :
    0 < gaussianReal 0 v (Icc (-L) L) := by
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 v) :=
    (gaussianReal_absolutelyContinuous' 0 hv).isOpenPosMeasure
  refine ((Measure.measure_Ioo_pos (gaussianReal 0 v)).2 ?_).trans_le
    (measure_mono Ioo_subset_Icc_self)
  linarith

private theorem tendsto_Icc_of_tendstoInDistribution_gaussian
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {v : ℝ≥0} (hv : v ≠ 0) {L : ℝ} (hL : 0 < L)
    (h : TendstoInDistribution (fun _ : ι ↦ id) l id μ (gaussianReal 0 v)) :
    Tendsto (fun i ↦ μ i (Icc (-L) L)) l
      (𝓝 (gaussianReal 0 v (Icc (-L) L))) :=
  tendsto_measure_of_tendstoInDistribution_id h
    (gaussianReal_frontier_Icc_eq_zero hv hL.le)

private theorem eventually_ge_half_of_tendsto
    {ι : Type*} {l : Filter ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
    (h : Tendsto f l (𝓝 a)) (ha_pos : 0 < a) (ha_top : a ≠ ∞) :
    ∀ᶠ i in l, a / 2 ≤ f i := by
  have hhalf : a / 2 < a := ENNReal.half_lt_self ha_pos.ne' ha_top
  exact (h.eventually (eventually_gt_nhds hhalf)).mono fun _ hi ↦ hi.le

private theorem tendsto_prod_Icc_of_tendstoInDistribution_gaussian
    {κ ι : Type*} [Fintype κ] {l : Filter ι} {μ : κ → ι → Measure ℝ}
    [∀ k i, IsProbabilityMeasure (μ k i)] {v : κ → ℝ≥0}
    (hv : ∀ k, v k ≠ 0)
    (h : ∀ k, TendstoInDistribution (fun _ : ι ↦ id) l id (μ k)
      (gaussianReal 0 (v k))) {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun i ↦ ∏ k, μ k i (Icc (-L) L)) l
      (𝓝 (∏ k, gaussianReal 0 (v k) (Icc (-L) L))) := by
  apply ENNReal.tendsto_finsetProd_of_ne_top Finset.univ
  · intro k _
    exact tendsto_Icc_of_tendstoInDistribution_gaussian (hv k) hL (h k)
  · intro k _
    exact measure_ne_top _ _

private theorem exists_eventual_pos_lower_bound_prod_Icc_gaussian
    {κ ι : Type*} [Fintype κ] {l : Filter ι} {μ : κ → ι → Measure ℝ}
    [∀ k i, IsProbabilityMeasure (μ k i)] {v : κ → ℝ≥0}
    (hv : ∀ k, v k ≠ 0)
    (h : ∀ k, TendstoInDistribution (fun _ : ι ↦ id) l id (μ k)
      (gaussianReal 0 (v k))) {L : ℝ} (hL : 0 < L) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ᶠ i in l, c ≤ ∏ k, μ k i (Icc (-L) L) := by
  let p := ∏ k, gaussianReal 0 (v k) (Icc (-L) L)
  have hp : 0 < p := by
    rw [pos_iff_ne_zero]
    dsimp only [p]
    rw [Finset.prod_ne_zero_iff]
    exact fun k _ ↦ (gaussianReal_Icc_pos (hv k) hL).ne'
  have hp_top : p ≠ ∞ := ENNReal.prod_ne_top fun k _ ↦ measure_ne_top _ _
  refine ⟨p / 2, ENNReal.div_pos hp.ne' (by norm_num), ?_⟩
  exact eventually_ge_half_of_tendsto
    (by simpa only [p] using
      tendsto_prod_Icc_of_tendstoInDistribution_gaussian hv h hL) hp hp_top

private theorem exists_eventual_pos_lower_bound_prod_Icc_iterated
    {κ : Type*} [Fintype κ] {h : κ → ℝ → ℝ}
    (hh_meas : ∀ k, Measurable (h k)) (hh_nonneg : ∀ k x, 0 ≤ h k x)
    (hh_bounded : ∀ k, Bornology.IsBounded (Set.range (h k)))
    (hh_mass : ∀ k, ∫ x, h k x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∀ k, ∫ x, x * h k x ∂gaussianReal 0 1 = 0)
    {L : ℝ} (hL : 0 < L) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ᶠ r in atTop, c ≤ ∏ k,
        ((gaussianReal 0 1).withDensity
          (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution (h k) r x)))
            (Icc (-L) L) := by
  let μ : κ → ℕ → Measure ℝ := fun k r ↦
    (gaussianReal 0 1).withDensity
      (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution (h k) r x))
  let v : κ → ℝ≥0 := fun k ↦ Var[id;
    (gaussianReal 0 1).withDensity (fun x ↦ ENNReal.ofReal (h k x))].toNNReal
  letI iteratedProb : ∀ k r, IsProbabilityMeasure (μ k r) := fun k r ↦ by
    dsimp only [μ]
    exact isProbabilityMeasure_iteratedNormalizedSelfConvolution
      (hh_meas k) (hh_nonneg k) (hh_bounded k) (hh_mass k) r
  have hv : ∀ k, v k ≠ 0 := fun k ↦ (Real.toNNReal_pos.mpr
    (variance_id_withDensity_ofReal_pos
      (hh_meas k) (hh_nonneg k) (hh_bounded k) (hh_mass k))).ne'
  have hclt : ∀ k, TendstoInDistribution (fun _ : ℕ ↦ id) atTop id (μ k)
      (gaussianReal 0 (v k)) := by
    intro k
    simpa only [μ, v] using
      (tendstoInDistribution_iteratedNormalizedSelfConvolution
        (hh_meas k) (hh_nonneg k) (hh_bounded k) (hh_mass k) (hh_barycenter k))
  simpa only [μ] using
    exists_eventual_pos_lower_bound_prod_Icc_gaussian hv hclt hL

private theorem integrable_iterated_factor
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) (r : ℕ) :
    Integrable (iteratedNormalizedSelfConvolution h r) (gaussianReal 0 1) := by
  have hbounded :=
    isBounded_range_iteratedNormalizedSelfConvolution hh_nonneg hh_bounded r
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  have hint := (integrable_const (1 : ℝ) :
    Integrable (fun _ : ℝ ↦ (1 : ℝ)) (gaussianReal 0 1))
  have hmul := hint.bdd_mul
    (measurable_iteratedNormalizedSelfConvolution hh_meas r).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ hC _ ⟨x, rfl⟩)
  simpa using hmul

private theorem boxMeasure_toReal_eq_setIntegral_iterated
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) (r : ℕ) (L : ℝ) :
    (((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution h r x)))
      (Set.Icc (-L) L)).toReal =
      ∫ x in Set.Icc (-L) L,
        iteratedNormalizedSelfConvolution h r x ∂gaussianReal 0 1 := by
  rw [withDensity_apply _ measurableSet_Icc]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_iterated_factor hh_meas hh_nonneg hh_bounded r).integrableOn
    (Filter.Eventually.of_forall fun x ↦
      iteratedNormalizedSelfConvolution_nonneg hh_nonneg r x)]
  rw [ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Icc fun x _ ↦
    iteratedNormalizedSelfConvolution_nonneg hh_nonneg r x

/-- The positive-definite Gaussian product integrals of all dyadic iterates have an eventual
strictly positive lower bound. -/
theorem exists_eventual_pos_lower_bound_integral_iteratedNormalizedSelfConvolution
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (h : Fin m → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_mass : ∀ i, ∫ x, h i x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∀ i, ∫ x, x * h i x ∂gaussianReal 0 1 = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      c ≤ ∫ x, ∏ i, iteratedNormalizedSelfConvolution (h i) r (x i)
        ∂multivariateGaussian (0 : Coord m) R := by
  let L : ℝ := 1
  letI iteratedProb : ∀ i r, IsProbabilityMeasure
      ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution (h i) r x))) :=
    fun i r ↦ isProbabilityMeasure_iteratedNormalizedSelfConvolution
      (hh_meas i) (hh_nonneg i) (hh_bounded i) (hh_mass i) r
  obtain ⟨a, ha, ha_le⟩ := exists_pos_le_gaussianDensityRatio_on_box hR L
  obtain ⟨b, hb, hb_eventually⟩ :=
    exists_eventual_pos_lower_bound_prod_Icc_iterated
      hh_meas hh_nonneg hh_bounded hh_mass hh_barycenter (L := L) (by norm_num [L])
  let d : ℝ≥0∞ := b ⊓ 1
  have hd_pos : 0 < d := by
    change 0 < b ⊓ 1
    rw [lt_inf_iff]
    exact ⟨hb, zero_lt_one⟩
  have hd_top : d ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (by simp [d])
  refine ⟨a * d.toReal, mul_pos ha (ENNReal.toReal_pos hd_pos.ne' hd_top), ?_⟩
  filter_upwards [hb_eventually] with r hr
  have hprod_top :
      (∏ i, ((gaussianReal 0 1).withDensity
        (fun x ↦ ENNReal.ofReal (iteratedNormalizedSelfConvolution (h i) r x)))
          (Set.Icc (-L) L)) ≠ ∞ :=
    ENNReal.prod_ne_top fun i _ ↦ measure_ne_top _ _
  have hd_real := ENNReal.toReal_mono hprod_top ((inf_le_left : d ≤ b).trans hr)
  rw [ENNReal.toReal_prod] at hd_real
  simp_rw [boxMeasure_toReal_eq_setIntegral_iterated
    (hh_meas _) (hh_nonneg _) (hh_bounded _)] at hd_real
  calc
    a * d.toReal ≤
        a * (∏ i, ∫ x in Set.Icc (-L) L,
          iteratedNormalizedSelfConvolution (h i) r x ∂gaussianReal 0 1) :=
      mul_le_mul_of_nonneg_left hd_real ha.le
    _ ≤ ∫ x, ∏ i, iteratedNormalizedSelfConvolution (h i) r (x i)
          ∂multivariateGaussian (0 : Coord m) R :=
      mul_prod_setIntegral_le_integral_of_le_gaussianDensityRatio_on_box
        hR L (fun i ↦ iteratedNormalizedSelfConvolution (h i) r)
        (fun i ↦ measurable_iteratedNormalizedSelfConvolution (hh_meas i) r)
        (fun i x ↦ iteratedNormalizedSelfConvolution_nonneg (hh_nonneg i) r x)
        (fun i ↦ isBounded_range_iteratedNormalizedSelfConvolution
          (hh_nonneg i) (hh_bounded i) r) ha.le ha_le

end WeakSimplex
