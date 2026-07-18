import WeakSimplexConjectureLean.Product.SymmetricRectangle
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder Topology

namespace WeakSimplex

private theorem symmetricConvex_ae_centeredInterval_or_univ
    (S : Set ℝ) (hS_conv : Convex ℝ S)
    (hS_symm : ∀ x, -x ∈ S ↔ x ∈ S) :
    S = Set.univ ∨
      ∃ r : ℝ, 0 ≤ r ∧ S =ᵐ[gaussianReal 0 1] Set.Icc (-r) r := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  rcases S.eq_empty_or_nonempty with hS_empty | hS_nonempty
  · right
    refine ⟨0, le_rfl, ?_⟩
    rw [hS_empty]
    simpa using
      (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 0) (μ := gaussianReal 0 1))
  · by_cases hS_bdd : BddAbove S
    · right
      have hS_neg : -S = S := by
        ext x
        simpa using hS_symm x
      have hS_bddBelow : BddBelow S := by
        rw [← hS_neg]
        exact bddBelow_neg.mpr hS_bdd
      have hinf : sInf S = -sSup S := by
        calc
          sInf S = sInf (-S) := by rw [hS_neg]
          _ = -sSup S := Real.sInf_neg S
      have hzero : 0 ∈ S := by
        obtain ⟨x, hx⟩ := hS_nonempty
        have hnx : -x ∈ S := (hS_symm x).2 hx
        have hmid := hS_conv hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
        convert hmid using 1
        all_goals ring
      have hr : 0 ≤ sSup S := le_csSup hS_bdd hzero
      refine ⟨sSup S, hr, ?_⟩
      have hinner : Set.Ioo (-sSup S) (sSup S) ⊆ S := by
        rw [← hinf]
        exact (hS_conv.isConnected hS_nonempty).Ioo_csInf_csSup_subset hS_bddBelow hS_bdd
      have houter : S ⊆ Set.Icc (-sSup S) (sSup S) := by
        rw [← hinf]
        exact subset_Icc_csInf_csSup hS_bddBelow hS_bdd
      filter_upwards [Ioo_ae_eq_Icc
        (a := -sSup S) (b := sSup S) (μ := gaussianReal 0 1)] with x hx
      apply propext
      constructor
      · intro hxS
        exact houter hxS
      · intro hxclosed
        apply hinner
        change Set.Ioo (-sSup S) (sSup S) x
        rw [hx]
        exact hxclosed
    · left
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hyS, hy⟩ := not_bddAbove_iff.mp hS_bdd |x|
      have hnyS : -y ∈ S := (hS_symm y).2 hyS
      have hxIcc : x ∈ Set.Icc (-y) y := by
        rw [Set.mem_Icc]
        exact ⟨(by linarith [neg_abs_le x]), (le_abs_self x).trans hy.le⟩
      exact hS_conv.ordConnected.out hnyS hyS hxIcc

private noncomputable def centeredIntervalApproxRadius
    (S : Set ℝ) (hS_conv : Convex ℝ S)
    (hS_symm : ∀ x, -x ∈ S ↔ x ∈ S) (n : ℕ) : ℝ :=
  if h : S = Set.univ then n
  else Classical.choose
    ((symmetricConvex_ae_centeredInterval_or_univ S hS_conv hS_symm).resolve_left h)

private theorem centeredIntervalApproxRadius_nonneg
    (S : Set ℝ) (hS_conv : Convex ℝ S)
    (hS_symm : ∀ x, -x ∈ S ↔ x ∈ S) (n : ℕ) :
    0 ≤ centeredIntervalApproxRadius S hS_conv hS_symm n := by
  classical
  by_cases h : S = Set.univ
  · simp [centeredIntervalApproxRadius, h]
  · rw [centeredIntervalApproxRadius, dif_neg h]
    exact Classical.choose_spec
      ((symmetricConvex_ae_centeredInterval_or_univ S hS_conv hS_symm).resolve_left h) |>.1

private theorem centeredIntervalApproxRadius_ae
    (S : Set ℝ) (hS_conv : Convex ℝ S)
    (hS_symm : ∀ x, -x ∈ S ↔ x ∈ S) (n : ℕ)
    (hS_ne : S ≠ Set.univ) :
    S =ᵐ[gaussianReal 0 1]
      Set.Icc (-centeredIntervalApproxRadius S hS_conv hS_symm n)
        (centeredIntervalApproxRadius S hS_conv hS_symm n) := by
  rw [centeredIntervalApproxRadius, dif_neg hS_ne]
  exact Classical.choose_spec
    ((symmetricConvex_ae_centeredInterval_or_univ S hS_conv hS_symm).resolve_left hS_ne) |>.2

private theorem centeredIntervalApproxRadius_eq_natCast
    (S : Set ℝ) (hS_conv : Convex ℝ S)
    (hS_symm : ∀ x, -x ∈ S ↔ x ∈ S) (n : ℕ)
    (hS : S = Set.univ) :
    centeredIntervalApproxRadius S hS_conv hS_symm n = n := by
  simp [centeredIntervalApproxRadius, hS]

private theorem iUnion_centered_nat_Icc :
    (⋃ n : ℕ, Set.Icc (-(n : ℝ)) n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge |x|
  rw [Set.mem_iUnion]
  refine ⟨n, ?_⟩
  exact ⟨(neg_le_of_abs_le hn), (le_abs_self x).trans hn⟩

private theorem symmetricConvexSet_product_ge_iid_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (S : Fin m → Set ℝ)
    (hS_conv : ∀ i, Convex ℝ (S i))
    (hS_symm : ∀ i x, -x ∈ S i ↔ x ∈ S i) :
    (∏ i, gaussianReal 0 1 (S i)) ≤
      multivariateGaussian (0 : Coord m) R {x | ∀ i, x i ∈ S i} := by
  classical
  let rad : Fin m → ℕ → ℝ := fun i n ↦
    centeredIntervalApproxRadius (S i) (hS_conv i) (hS_symm i) n
  have hrad_nonneg (i : Fin m) (n : ℕ) : 0 ≤ rad i n :=
    centeredIntervalApproxRadius_nonneg (S i) (hS_conv i) (hS_symm i) n
  have hrect_le (n : ℕ) :
      multivariateGaussian (0 : Coord m) R (symmetricRectangle (fun i ↦ rad i n)) ≤
        multivariateGaussian (0 : Coord m) R {x | ∀ i, x i ∈ S i} := by
    apply measure_mono_ae
    have hi (i : Fin m) : ∀ᵐ x ∂multivariateGaussian (0 : Coord m) R,
        x i ∈ Set.Icc (-rad i n) (rad i n) → x i ∈ S i := by
      by_cases hSi : S i = Set.univ
      · filter_upwards with x
        simp [hSi]
      · have hmp : MeasurePreserving (fun x : Coord m ↦ x i)
            (multivariateGaussian (0 : Coord m) R) (gaussianReal 0 1) := by
          simpa [hdiag i] using
            (measurePreserving_eval_multivariateGaussian
              (μ := (0 : Coord m)) hR.posSemidef (i := i))
        have hae := centeredIntervalApproxRadius_ae
          (S i) (hS_conv i) (hS_symm i) n hSi
        have hpre := hmp.quasiMeasurePreserving.preimage_ae_eq hae.symm
        filter_upwards [hpre] with x hx hxi
        exact hx.mp hxi
    have hall : ∀ᵐ x ∂multivariateGaussian (0 : Coord m) R,
        ∀ i, x i ∈ Set.Icc (-rad i n) (rad i n) → x i ∈ S i :=
      Filter.eventually_all.mpr hi
    filter_upwards [hall] with x hx hrect i
    exact hx i (hrect i)
  have hineq (n : ℕ) :
      (∏ i, gaussianReal 0 1 (Set.Icc (-rad i n) (rad i n))) ≤
        multivariateGaussian (0 : Coord m) R {x | ∀ i, x i ∈ S i} :=
    (symmetricRectangle_ge_iid_of_posDef R hR hdiag (fun i ↦ rad i n)
      (fun i ↦ hrad_nonneg i n)).trans (hrect_le n)
  have hfactor_tendsto (i : Fin m) :
      Tendsto (fun n : ℕ ↦ gaussianReal 0 1 (Set.Icc (-rad i n) (rad i n)))
        Filter.atTop (nhds (gaussianReal 0 1 (S i))) := by
    by_cases hSi : S i = Set.univ
    · have hmono : Monotone (fun n : ℕ ↦ Set.Icc (-(n : ℝ)) n) := by
        intro n k hnk
        exact Set.Icc_subset_Icc
          (neg_le_neg (by exact_mod_cast hnk : (n : ℝ) ≤ k))
          (by exact_mod_cast hnk)
      have ht := tendsto_measure_iUnion_atTop
        (μ := gaussianReal 0 1) hmono
      rw [show (⋃ n : ℕ, Set.Icc (-(n : ℝ)) n) = Set.univ from
        iUnion_centered_nat_Icc] at ht
      simp only [measure_univ] at ht
      change Tendsto (fun n : ℕ ↦ gaussianReal 0 1 (Set.Icc (-(n : ℝ)) n))
        atTop (nhds 1) at ht
      simpa [rad, centeredIntervalApproxRadius_eq_natCast
        (S i) (hS_conv i) (hS_symm i), hSi] using ht
    · have hae := centeredIntervalApproxRadius_ae
        (S i) (hS_conv i) (hS_symm i) 0 hSi
      have hmeasure : gaussianReal 0 1
          (Set.Icc (-rad i 0) (rad i 0)) = gaussianReal 0 1 (S i) := by
        exact measure_congr hae.symm
      have hrad_const (n : ℕ) : rad i n = rad i 0 := by
        simp only [rad, centeredIntervalApproxRadius, dif_neg hSi]
      have heq :
          (fun n : ℕ ↦ gaussianReal 0 1 (Set.Icc (-rad i n) (rad i n))) =
            fun _ ↦ gaussianReal 0 1 (S i) := by
        funext n
        rw [hrad_const, hmeasure]
      rw [heq]
      exact tendsto_const_nhds
  have hprod_tendsto :
      Tendsto
        (fun n : ℕ ↦ ∏ i, gaussianReal 0 1 (Set.Icc (-rad i n) (rad i n)))
        Filter.atTop (nhds (∏ i, gaussianReal 0 1 (S i))) := by
    simpa using
      ENNReal.tendsto_finsetProd_of_ne_top Finset.univ
        (fun i _ ↦ hfactor_tendsto i)
        (fun i _ ↦ (measure_ne_top (gaussianReal 0 1) (S i)))
  exact le_of_tendsto hprod_tendsto (Filter.Eventually.of_forall hineq)

private theorem lintegral_Iio_one_restrict_Ioi (a : ℝ) :
    (∫⁻ t, (Set.Iio a).indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      ∂(volume.restrict (Set.Ioi 0))) = ENNReal.ofReal a := by
  rw [lintegral_indicator measurableSet_Iio, setLIntegral_one,
    Measure.restrict_apply measurableSet_Iio]
  have hinter : Set.Iio a ∩ Set.Ioi 0 = Set.Ioo 0 a := by
    ext x
    simp [and_comm]
  rw [hinter, Real.volume_Ioo]
  simp

private def positiveLevelMeasure {m : ℕ} : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))

private instance positiveLevelMeasure_sigmaFinite {m : ℕ} :
    SigmaFinite (positiveLevelMeasure (m := m)) := by
  dsimp [positiveLevelMeasure]
  infer_instance

private def productLevelIndicator {m : ℕ}
    (g : Fin m → ℝ → ℝ) (x : Coord m) (t : Fin m → ℝ) : ℝ≥0∞ :=
  ∏ i, if t i < g i (x i) then 1 else 0

private theorem measurable_uncurry_productLevelIndicator
    {m : ℕ} {g : Fin m → ℝ → ℝ}
    (hg_meas : ∀ i, Measurable (g i)) :
    Measurable (Function.uncurry (productLevelIndicator g)) := by
  change Measurable (fun p : Coord m × (Fin m → ℝ) ↦
    ∏ i, if p.2 i < g i (p.1 i) then (1 : ℝ≥0∞) else 0)
  apply Finset.measurable_prod Finset.univ
  intro i hi
  apply Measurable.ite
  · exact measurableSet_lt
      ((measurable_pi_apply i).comp measurable_snd)
      ((hg_meas i).comp
        ((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp measurable_fst))
  · exact measurable_const
  · exact measurable_const

private theorem lintegral_productLevelIndicator_right
    {m : ℕ} (g : Fin m → ℝ → ℝ) (x : Coord m) :
    (∫⁻ t, productLevelIndicator g x t ∂positiveLevelMeasure) =
      ∏ i, ENNReal.ofReal (g i (x i)) := by
  change (∫⁻ t, ∏ i, if t i < g i (x i) then (1 : ℝ≥0∞) else 0
      ∂Measure.pi (fun _ : Fin m ↦ volume.restrict (Set.Ioi 0))) = _
  have hprod :=
    WeakSimplex.Vendor.StatLean.MeasureTheory.lintegral_fintype_prod_eq_prod
      (μ := fun _ : Fin m ↦ volume.restrict (Set.Ioi 0))
      (f := fun i t ↦ if t < g i (x i) then (1 : ℝ≥0∞) else 0)
      (fun i ↦ Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const measurable_const)
  rw [hprod]
  · apply Finset.prod_congr rfl
    intro i hi
    have hfun : (fun t : ℝ ↦ if t < g i (x i) then (1 : ℝ≥0∞) else 0) =
        (Set.Iio (g i (x i))).indicator (fun _ ↦ 1) := by
      funext t
      by_cases ht : t < g i (x i) <;> simp [ht]
    rw [hfun, lintegral_Iio_one_restrict_Ioi]

private theorem lintegral_prod_ofReal_eq_lintegral_levelMeasure
    {m : ℕ} (g : Fin m → ℝ → ℝ)
    (hg_meas : ∀ i, Measurable (g i))
    (μ : Measure (Coord m)) [SFinite μ] :
    (∫⁻ x, ∏ i, ENNReal.ofReal (g i (x i)) ∂μ) =
      ∫⁻ t, μ {x | ∀ i, t i < g i (x i)} ∂positiveLevelMeasure := by
  have hjoint := measurable_uncurry_productLevelIndicator hg_meas
  calc
    (∫⁻ x, ∏ i, ENNReal.ofReal (g i (x i)) ∂μ) =
        ∫⁻ x, ∫⁻ t, productLevelIndicator g x t ∂positiveLevelMeasure ∂μ := by
      apply lintegral_congr
      intro x
      exact (lintegral_productLevelIndicator_right g x).symm
    _ = ∫⁻ t, ∫⁻ x, productLevelIndicator g x t ∂μ ∂positiveLevelMeasure := by
      exact lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ t, μ {x | ∀ i, t i < g i (x i)} ∂positiveLevelMeasure := by
      apply lintegral_congr
      intro t
      have hset : MeasurableSet {x : Coord m | ∀ i, t i < g i (x i)} := by
        rw [Set.setOf_forall]
        exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const
          ((hg_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable)
      have hfun : (fun x : Coord m ↦ productLevelIndicator g x t) =
          {x | ∀ i, t i < g i (x i)}.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
        funext x
        by_cases hx : ∀ i, t i < g i (x i)
        · simp [productLevelIndicator, hx]
        · push Not at hx
          obtain ⟨i, hi⟩ := hx
          have hxnot : x ∉ {x : Coord m | ∀ i, t i < g i (x i)} := by
            intro hall
            exact (not_lt.mpr hi) (hall i)
          have hzero : (if t i < g i (x i) then (1 : ℝ≥0∞) else 0) = 0 := by
            simp [not_lt.mpr hi]
          rw [Set.indicator_of_notMem hxnot]
          exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
      rw [hfun, lintegral_indicator hset, setLIntegral_one]

private theorem convex_strictSuperlevel_of_isLogConcave
    {g : ℝ → ℝ} (hg : IsLogConcave (fun x ↦ ENNReal.ofReal (g x)))
    {t : ℝ} (ht : 0 < t) :
    Convex ℝ {x | t < g x} := by
  intro x hx y hy a b ha hb hab
  by_cases ha_zero : a = 0
  · have hb_one : b = 1 := by linarith
    simpa [ha_zero, hb_one] using hy
  by_cases hb_zero : b = 0
  · have ha_one : a = 1 := by linarith
    simpa [hb_zero, ha_one] using hx
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb_zero)
  have ha_lt : a < 1 := by linarith
  have hb_eq : b = 1 - a := by linarith
  have htx : ENNReal.ofReal t < ENNReal.ofReal (g x) :=
    ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hx, ht.trans hx⟩
  have hty : ENNReal.ofReal t < ENNReal.ofReal (g y) :=
    ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hy, ht.trans hy⟩
  have ht_ofReal_pos : 0 < ENNReal.ofReal t := ENNReal.ofReal_pos.2 ht
  have ht_ofReal_ne_top : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  have ht_split : ENNReal.ofReal t =
      ENNReal.ofReal t ^ a * ENNReal.ofReal t ^ (1 - a) := by
    rw [← ENNReal.rpow_add a (1 - a) ht_ofReal_pos.ne' ht_ofReal_ne_top]
    norm_num
  have hpow_x : ENNReal.ofReal t ^ a < ENNReal.ofReal (g x) ^ a :=
    ENNReal.rpow_lt_rpow htx ha_pos
  have hpow_y : ENNReal.ofReal t ^ (1 - a) < ENNReal.ofReal (g y) ^ (1 - a) :=
    ENNReal.rpow_lt_rpow hty (by linarith)
  have hproduct : ENNReal.ofReal t ^ a * ENNReal.ofReal t ^ (1 - a) <
      ENNReal.ofReal (g x) ^ a * ENNReal.ofReal (g y) ^ (1 - a) :=
    ENNReal.mul_lt_mul hpow_x hpow_y
  have hlc := hg ha_pos ha_lt x y
  have hlevel : ENNReal.ofReal t <
      ENNReal.ofReal (g (a • x + (1 - a) • y)) := by
    calc
      ENNReal.ofReal t =
          ENNReal.ofReal t ^ a * ENNReal.ofReal t ^ (1 - a) := ht_split
      _ < ENNReal.ofReal (g x) ^ a * ENNReal.ofReal (g y) ^ (1 - a) := hproduct
      _ ≤ ENNReal.ofReal (g (a • x + (1 - a) • y)) := hlc
  rw [hb_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 hlevel).1

private theorem lintegral_even_logConcave_product_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (g : Fin m → ℝ → ℝ)
    (hg_meas : ∀ i, Measurable (g i))
    (hg_nonneg : ∀ i x, 0 ≤ g i x)
    (hg_even : ∀ i, Function.Even (g i))
    (hg_logConcave : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (g i x))) :
    (∏ i, ∫⁻ z, ENNReal.ofReal (g i z) ∂gaussianReal 0 1) ≤
      ∫⁻ x, ∏ i, ENNReal.ofReal (g i (x i))
        ∂multivariateGaussian (0 : Coord m) R := by
  have hscalar_layer (i : Fin m) :
      (∫⁻ z, ENNReal.ofReal (g i z) ∂gaussianReal 0 1) =
        ∫⁻ t, gaussianReal 0 1 {z | t < g i z}
          ∂(volume.restrict (Set.Ioi 0)) :=
    lintegral_eq_lintegral_meas_lt (gaussianReal 0 1)
      (Filter.Eventually.of_forall (hg_nonneg i)) (hg_meas i).aemeasurable
  have hlevel_meas (i : Fin m) :
      Measurable (fun t : ℝ ↦ gaussianReal 0 1 {z | t < g i z}) :=
    (show Antitone (fun t : ℝ ↦ gaussianReal 0 1 {z | t < g i z}) from by
      intro s t hst
      apply measure_mono
      intro z hz
      exact lt_of_le_of_lt hst hz).measurable
  have hproduct_layer :
      (∏ i, ∫⁻ z, ENNReal.ofReal (g i z) ∂gaussianReal 0 1) =
        ∫⁻ t, ∏ i, gaussianReal 0 1 {z | t i < g i z} ∂positiveLevelMeasure := by
    rw [show (∏ i, ∫⁻ z, ENNReal.ofReal (g i z) ∂gaussianReal 0 1) =
        ∏ i, ∫⁻ t, gaussianReal 0 1 {z | t < g i z}
          ∂(volume.restrict (Set.Ioi 0)) by
      exact Finset.prod_congr rfl fun i _ ↦ hscalar_layer i]
    symm
    exact WeakSimplex.Vendor.StatLean.MeasureTheory.lintegral_fintype_prod_eq_prod
      (fun i ↦ hlevel_meas i)
  have hpositive (i : Fin m) :
      ∀ᵐ t ∂positiveLevelMeasure, 0 < t i := by
    exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  have hpositive_all :
      ∀ᵐ t ∂positiveLevelMeasure, ∀ i, 0 < t i :=
    Filter.eventually_all.mpr hpositive
  have hlevel_ineq : ∀ᵐ t ∂positiveLevelMeasure,
      (∏ i, gaussianReal 0 1 {z | t i < g i z}) ≤
        multivariateGaussian (0 : Coord m) R {x | ∀ i, t i < g i (x i)} := by
    filter_upwards [hpositive_all] with t ht
    apply symmetricConvexSet_product_ge_iid_of_posDef R hR hdiag
    · intro i
      exact convex_strictSuperlevel_of_isLogConcave (hg_logConcave i) (ht i)
    · intro i x
      simp only [Set.mem_setOf_eq]
      rw [hg_even i x]
  rw [hproduct_layer,
    lintegral_prod_ofReal_eq_lintegral_levelMeasure g hg_meas
      (multivariateGaussian (0 : Coord m) R)]
  exact lintegral_mono_ae hlevel_ineq

private theorem exists_norm_bound_of_isBounded_range
    {X : Type*} {f : X → ℝ} (hf : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf
  refine ⟨C, fun x ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self x)

/-- Even one-dimensional factors lift the centered Gaussian rectangle comparison to products. -/
theorem even_logConcave_product_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (g : Fin m → ℝ → ℝ)
    (hg_meas : ∀ i, Measurable (g i))
    (hg_nonneg : ∀ i x, 0 ≤ g i x)
    (hg_bounded : ∀ i, Bornology.IsBounded (Set.range (g i)))
    (hg_even : ∀ i, Function.Even (g i))
    (hg_logConcave : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (g i x))) :
    (∏ i, ∫ z, g i z ∂gaussianReal 0 1) ≤
      ∫ x, ∏ i, g i (x i) ∂multivariateGaussian (0 : Coord m) R := by
  classical
  have hfactor_int (i : Fin m) : Integrable (g i) (gaussianReal 0 1) := by
    obtain ⟨C, hC⟩ := exists_norm_bound_of_isBounded_range (hg_bounded i)
    have hint := (integrable_const (1 : ℝ) :
      Integrable (fun _ : ℝ ↦ (1 : ℝ)) (gaussianReal 0 1))
    have hmul := hint.bdd_mul (hg_meas i).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
    simpa using hmul
  have hfactor_integral_nonneg (i : Fin m) :
      0 ≤ ∫ z, g i z ∂gaussianReal 0 1 :=
    integral_nonneg (hg_nonneg i)
  choose C hC using fun i ↦ exists_norm_bound_of_isBounded_range (hg_bounded i)
  have hcoord_meas (i : Fin m) : Measurable (fun x : Coord m ↦ g i (x i)) :=
    (hg_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable
  have hcoord_bound (i : Fin m) :
      ∀ x : Coord m, ‖g i (x i)‖ ≤ C i := fun x ↦ hC i (x i)
  have hproduct_int_finset (s : Finset (Fin m)) :
      Integrable (fun x : Coord m ↦ ∏ i ∈ s, g i (x i))
        (multivariateGaussian (0 : Coord m) R) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
        have hmul := hs.bdd_mul (hcoord_meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall (hcoord_bound i))
        simpa [Finset.prod_insert hi] using hmul
  have hproduct_int :
      Integrable (fun x : Coord m ↦ ∏ i, g i (x i))
        (multivariateGaussian (0 : Coord m) R) := by
    simpa using hproduct_int_finset Finset.univ
  have hproduct_nonneg :
      ∀ x : Coord m, 0 ≤ ∏ i, g i (x i) := fun x ↦
    Finset.prod_nonneg fun i _ ↦ hg_nonneg i (x i)
  have hleft_ofReal :
      ENNReal.ofReal (∏ i, ∫ z, g i z ∂gaussianReal 0 1) =
        ∏ i, ∫⁻ z, ENNReal.ofReal (g i z) ∂gaussianReal 0 1 := by
    rw [ENNReal.ofReal_prod_of_nonneg
      (fun i _ ↦ hfactor_integral_nonneg i)]
    apply Finset.prod_congr rfl
    intro i hi
    exact ofReal_integral_eq_lintegral_ofReal (hfactor_int i)
      (Filter.Eventually.of_forall (hg_nonneg i))
  have hright_ofReal :
      ENNReal.ofReal
          (∫ x, ∏ i, g i (x i) ∂multivariateGaussian (0 : Coord m) R) =
        ∫⁻ x, ∏ i, ENNReal.ofReal (g i (x i))
          ∂multivariateGaussian (0 : Coord m) R := by
    rw [ofReal_integral_eq_lintegral_ofReal hproduct_int
      (Filter.Eventually.of_forall hproduct_nonneg)]
    apply lintegral_congr
    intro x
    exact ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hg_nonneg i (x i)
  apply (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg hproduct_nonneg)).1
  rw [hleft_ofReal, hright_ofReal]
  exact lintegral_even_logConcave_product_of_posDef R hR hdiag g hg_meas hg_nonneg
    hg_even hg_logConcave



end WeakSimplex
