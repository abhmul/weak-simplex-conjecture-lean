import WeakSimplexConjectureLean.Gaussian.Regularization
import WeakSimplexConjectureLean.Tilt.AdaptiveWitnesses
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Adaptive witnesses for singular covariance matrices

This module obtains adaptive witnesses for an admissible singular covariance as a compact limit of
witnesses for its dyadic positive-definite regularizations.
-/

noncomputable section

open Filter
open scoped BigOperators InnerProductSpace Topology

namespace WeakSimplex

private lemma adaptiveWitnesses_value_expression
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (∑ i, localLogMass (w.s i)) - qform R w.a / 2 =
      (∑ i, Real.log (normalCDF (w.s i))) +
        (⟪w.a, w.a⟫_ℝ - ⟪w.a, matrixMul R w.a⟫_ℝ) / 2 := by
  have hsquares : (∑ i, (r (w.s i)) ^ 2) = ⟪w.a, w.a⟫_ℝ := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [w.a_eq_r i]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  simp only [localLogMass, Finset.sum_add_distrib]
  rw [← Finset.sum_div, hsquares]
  rw [qform]
  ring

private lemma adaptiveWitnesses_qform_le
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    qform R w.a ≤ -2 * ((m : ℝ) * Real.log (normalCDF c)) := by
  have hsum : (∑ i, localLogMass (w.s i)) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ (localLogMass_neg (w.s i)).le
  have hvalue := w.value_bound
  rw [← adaptiveWitnesses_value_expression w] at hvalue
  linarith

private lemma adaptiveWitnesses_localLogMass_ge
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (hR : R.PosSemidef) (w : AdaptiveWitnesses R c) (i : Fin m) :
    (m : ℝ) * Real.log (normalCDF c) ≤ localLogMass (w.s i) := by
  have hrest : (∑ j ∈ Finset.univ.erase i, localLogMass (w.s j)) ≤ 0 :=
    Finset.sum_nonpos fun j _ ↦ (localLogMass_neg (w.s j)).le
  have hsum : (∑ j, localLogMass (w.s j)) ≤ localLogMass (w.s i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    linarith
  have hq : 0 ≤ qform R w.a := qform_nonneg_of_posSemidef hR w.a
  have hvalue := w.value_bound
  rw [← adaptiveWitnesses_value_expression w] at hvalue
  linarith

private lemma inner_matrixMul_eq_of_posSemidef
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (x y : Coord m) :
    ⟪matrixMul A x, y⟫_ℝ = ⟪x, matrixMul A y⟫_ℝ := by
  rw [real_inner_comm]
  simp only [matrixMul, Matrix.inner_toEuclideanCLM]
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  simpa only [hsymm.eq, Coord.toFun] using
    (Matrix.dotProduct_transpose_mulVec A (Coord.toFun x) (Coord.toFun y)).symm

private lemma matrixMul_regularizedCovariance
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (a : Coord m) :
    matrixMul (regularizedCovariance R ε) a =
      (1 - ε) • matrixMul R a + ε • a := by
  simp [matrixMul, regularizedCovariance]

/-- A coordinate of a correlation-matrix action is bounded by its quadratic form. -/
lemma sq_matrixMul_apply_le_qform_of_isCorrelation
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : IsCorrelation R) (a : Coord m) (i : Fin m) :
    (matrixMul R a i) ^ 2 ≤ qform R a := by
  let y := matrixMul R a i
  let e : Coord m := EuclideanSpace.single i 1
  have hnonneg := qform_nonneg_of_posSemidef hR.1 (a - y • e)
  have heval : ⟪e, matrixMul R a⟫_ℝ = y := by
    simp [e, y, PiLp.inner_apply]
  have hself : ⟪a, matrixMul R e⟫_ℝ = y := by
    rw [← inner_matrixMul_eq_of_posSemidef hR.1]
    simpa only [real_inner_comm] using heval
  have hee : ⟪e, matrixMul R e⟫_ℝ = 1 := by
    simp [e, matrixMul, PiLp.inner_apply, hR.2 i]
  change 0 ≤ ⟪a - y • e, matrixMul R (a - y • e)⟫_ℝ at hnonneg
  have hmul : matrixMul R (a - y • e) = matrixMul R a - y • matrixMul R e := by
    simp [matrixMul]
  rw [hmul] at hnonneg
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right] at hnonneg
  rw [heval, hself, hee] at hnonneg
  change 0 ≤ qform R a - y * y - (y * y - y * (y * 1)) at hnonneg
  ring_nf at hnonneg
  dsimp only [y] at hnonneg ⊢
  simpa only [pow_two] using sub_nonneg.mp hnonneg

private lemma continuous_r : Continuous r := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (hasDerivAt_r x).continuousAt

private lemma continuous_coordinateMap_r {m : ℕ} :
    Continuous (coordinateMap r : Coord m → Coord m) := by
  unfold coordinateMap Coord.ofFun
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m ↦ ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_r.comp (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i)

private lemma continuous_log_normalCDF :
    Continuous (fun x : ℝ ↦ Real.log (normalCDF x)) := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ ((hasDerivAt_normalCDF x).log (normalCDF_pos x).ne').continuousAt

private lemma continuous_logValue {m : ℕ} :
    Continuous (fun s : Coord m ↦ ∑ i, Real.log (normalCDF (s i))) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_log_normalCDF.comp
    (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i)

/-- Adaptive witnesses exist for every admissible covariance, including singular ones. -/
theorem exists_adaptiveWitnesses_of_weakSimplexCov
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    Nonempty (AdaptiveWitnesses R c) := by
  classical
  let L : ℝ := (m : ℝ) * Real.log (normalCDF c)
  have hL : L < 0 := by
    dsimp only [L]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hm)
      (Real.log_neg (normalCDF_pos c) (normalCDF_lt_one c))
  let Rn : ℕ → Matrix (Fin m) (Fin m) ℝ := fun n ↦
    regularizedCovariance R (regularizationEpsilon n)
  have hRnWeak (n : ℕ) : IsWeakSimplexCov (Rn n) := by
    dsimp only [Rn]
    exact regularizedCovariance_isWeakSimplexCov hm R hR
      (regularizationEpsilon_pos n) (regularizationEpsilon_lt_one n).le
  have hRnPosDef (n : ℕ) : (Rn n).PosDef := by
    dsimp only [Rn]
    exact regularizedCovariance_posDef R hR.1.1
      (regularizationEpsilon_pos n) (regularizationEpsilon_lt_one n).le
  let w : (n : ℕ) → AdaptiveWitnesses (Rn n) c := fun n ↦
    Classical.choice
      (exists_adaptiveWitnesses hm (Rn n) (hRnPosDef n) (hRnWeak n).2 c)
  let s : ℕ → Coord m := fun n ↦ (w n).s
  have ha_eq (n : ℕ) : (w n).a = coordinateMap r (s n) := by
    ext i
    exact (w n).a_eq_r i
  obtain ⟨B, hB⟩ := Filter.eventually_atBot.1
    (localLogMass_tendsto_atBot.eventually_lt_atBot L)
  let M : ℝ := -2 * L
  let W : ℝ := Real.sqrt M
  let U : ℝ := c + W
  let C : ℝ := max |B| |U|
  let D : ℝ := Real.sqrt ((m : ℝ) * C ^ 2)
  have hM : 0 ≤ M := by
    dsimp only [M]
    linarith
  have hC : 0 ≤ C := (abs_nonneg B).trans (le_max_left _ _)
  have hs_abs (n : ℕ) (i : Fin m) : |s n i| ≤ C := by
    have hlower : B < s n i := by
      by_contra hnot
      have htail := hB (s n i) (le_of_not_gt hnot)
      have hlocal := adaptiveWitnesses_localLogMass_ge (hRnWeak n).1.1 (w n) i
      dsimp only [L] at hlocal
      linarith
    have hq := adaptiveWitnesses_qform_le (w n)
    change qform (Rn n) (w n).a ≤ -2 * L at hq
    have hsq := sq_matrixMul_apply_le_qform_of_isCorrelation
      (hRnWeak n).1 (w n).a i
    have hmul_upper : matrixMul (Rn n) (w n).a i ≤ W := by
      dsimp only [M, W]
      nlinarith [hsq.trans hq, Real.sq_sqrt hM, Real.sqrt_nonneg M]
    have hcomp := congrArg (fun x : Coord m ↦ x i) (w n).compatibility
    have hupper : s n i ≤ U := by
      dsimp only [s, U]
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        allOnesVector_apply, smul_eq_mul, mul_one] at hcomp
      linarith [(w n).a_pos i]
    apply abs_le.2
    constructor
    · exact (neg_le_neg (le_max_left |B| |U|)).trans
        ((neg_abs_le B).trans hlower.le)
    · exact hupper.trans ((le_abs_self U).trans (le_max_right |B| |U|))
  have hs_norm (n : ℕ) : ‖s n‖ ≤ D := by
    dsimp only [D]
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc
      (∑ i, ‖s n i‖ ^ 2) ≤ ∑ _i : Fin m, C ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply (sq_le_sq₀ (norm_nonneg _) hC).2
        simpa only [Real.norm_eq_abs] using hs_abs n i
      _ = (m : ℝ) * C ^ 2 := by simp
  have hs_ball (n : ℕ) : s n ∈ Metric.closedBall 0 D := by
    rw [Metric.mem_closedBall]
    simpa only [dist_zero_right] using hs_norm n
  obtain ⟨sStar, _hsStar, φ, hφ, hsTend⟩ :=
    (isCompact_closedBall (0 : Coord m) D).tendsto_subseq hs_ball
  let aStar : Coord m := coordinateMap r sStar
  have haTend :
      Tendsto (fun k ↦ coordinateMap r (s (φ k))) atTop (nhds aStar) := by
    dsimp only [aStar]
    apply (continuous_coordinateMap_r.continuousAt.tendsto.comp hsTend).congr'
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hεTend :
      Tendsto (fun k ↦ regularizationEpsilon (φ k)) atTop (nhds 0) :=
    tendsto_regularizationEpsilon.comp hφ.tendsto_atTop
  have hRaTend :
      Tendsto (fun k ↦ matrixMul R (coordinateMap r (s (φ k)))) atTop
        (nhds (matrixMul R aStar)) := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) R).continuous.continuousAt.tendsto.comp haTend
  have hregMulTend :
      Tendsto
        (fun k ↦ matrixMul (Rn (φ k)) (coordinateMap r (s (φ k))))
        atTop (nhds (matrixMul R aStar)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have ht := ((hone.sub hεTend).smul hRaTend).add
      (hεTend.smul haTend)
    convert ht using 1
    · funext k
      exact matrixMul_regularizedCovariance R (regularizationEpsilon (φ k)) _
    · simp
  have hcompatTend :
      Tendsto
        (fun k ↦ s (φ k) + coordinateMap r (s (φ k)) -
          matrixMul (Rn (φ k)) (coordinateMap r (s (φ k))))
        atTop (nhds (sStar + aStar - matrixMul R aStar)) :=
    (hsTend.add haTend).sub hregMulTend
  have hcompatConst :
      Tendsto
        (fun k ↦ s (φ k) + coordinateMap r (s (φ k)) -
          matrixMul (Rn (φ k)) (coordinateMap r (s (φ k))))
        atTop (nhds (c • allOnesVector m)) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun k ↦ by
      change c • allOnesVector m =
        s (φ k) + coordinateMap r (s (φ k)) -
          matrixMul (Rn (φ k)) (coordinateMap r (s (φ k)))
      rw [← ha_eq (φ k)]
      exact (w (φ k)).compatibility.symm
  have hcompat : sStar + aStar - matrixMul R aStar = c • allOnesVector m :=
    tendsto_nhds_unique hcompatTend hcompatConst
  refine ⟨{
    s := sStar
    a := aStar
    a_eq_r := fun i ↦ rfl
    a_pos := fun i ↦ r_pos (sStar i)
    compatibility := hcompat
    value_bound := ?_
  }⟩
  have hlogTend :
      Tendsto (fun k ↦ ∑ i, Real.log (normalCDF (s (φ k) i))) atTop
        (nhds (∑ i, Real.log (normalCDF (sStar i)))) :=
    continuous_logValue.continuousAt.tendsto.comp hsTend
  have hselfTend :
      Tendsto
        (fun k ↦ ⟪coordinateMap r (s (φ k)), coordinateMap r (s (φ k))⟫_ℝ)
        atTop (nhds ⟪aStar, aStar⟫_ℝ) :=
    haTend.inner haTend
  have hcrossTend :
      Tendsto
        (fun k ↦ ⟪coordinateMap r (s (φ k)),
          matrixMul (Rn (φ k)) (coordinateMap r (s (φ k)))⟫_ℝ)
        atTop (nhds ⟪aStar, matrixMul R aStar⟫_ℝ) :=
    haTend.inner hregMulTend
  have hvalueTend :
      Tendsto
        (fun k ↦ (∑ i, Real.log (normalCDF (s (φ k) i))) +
          (⟪coordinateMap r (s (φ k)), coordinateMap r (s (φ k))⟫_ℝ -
            ⟪coordinateMap r (s (φ k)),
              matrixMul (Rn (φ k)) (coordinateMap r (s (φ k)))⟫_ℝ) / 2)
        atTop
        (nhds ((∑ i, Real.log (normalCDF (sStar i))) +
          (⟪aStar, aStar⟫_ℝ - ⟪aStar, matrixMul R aStar⟫_ℝ) / 2)) :=
    hlogTend.add ((hselfTend.sub hcrossTend).div_const 2)
  have hvalue_each (k : ℕ) :
      L ≤ (∑ i, Real.log (normalCDF (s (φ k) i))) +
        (⟪coordinateMap r (s (φ k)), coordinateMap r (s (φ k))⟫_ℝ -
          ⟪coordinateMap r (s (φ k)),
            matrixMul (Rn (φ k)) (coordinateMap r (s (φ k)))⟫_ℝ) / 2 := by
    rw [← ha_eq (φ k)]
    simpa only [L, s] using (w (φ k)).value_bound
  exact isClosed_Ici.mem_of_tendsto hvalueTend
    (Filter.Eventually.of_forall hvalue_each)

end WeakSimplex
