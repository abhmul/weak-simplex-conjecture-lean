import WeakSimplexConjectureLean.Tilt.Potential
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact superlevels and an adaptive-potential maximizer

This module bounds every negative superlevel of the adaptive potential, proves its compactness,
and obtains a global maximizer with the symmetric trial-point value bound.
-/

namespace WeakSimplex

noncomputable section

open scoped BigOperators

private lemma sum_localLogMass_le_single {m : ℕ} (s : Coord m) (i : Fin m) :
    (∑ j, localLogMass (s j)) ≤ localLogMass (s i) := by
  have hrest : (∑ j ∈ Finset.univ.erase i, localLogMass (s j)) ≤ 0 := by
    exact Finset.sum_nonpos fun j _ ↦ (localLogMass_neg (s j)).le
  calc
    (∑ j, localLogMass (s j)) =
        (∑ j ∈ Finset.univ.erase i, localLogMass (s j)) + localLogMass (s i) := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    _ ≤ 0 + localLogMass (s i) := by linarith
    _ = localLogMass (s i) := zero_add _

private lemma isBounded_adaptivePotential_superlevel
    {m : ℕ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c L : ℝ) (hL : L < 0) :
    Bornology.IsBounded {s : Coord m | L ≤ adaptivePotential R c s} := by
  classical
  obtain ⟨κ, hκ, hcoerc⟩ := posDef_quadratic_coercive hR.inv
  obtain ⟨B, hB⟩ := Filter.eventually_atBot.1
    (localLogMass_tendsto_atBot.eventually_lt_atBot L)
  let W : ℝ := Real.sqrt ((-2 * L) / κ)
  let U : ℝ := W + c
  let C : ℝ := max |B| |U|
  have hC : 0 ≤ C := (abs_nonneg B).trans (le_max_left _ _)
  refine isBounded_iff_forall_norm_le.2 ⟨Real.sqrt ((m : ℝ) * C ^ 2), ?_⟩
  intro s hs
  let w : Coord m := displacement c s
  have hsum_nonpos : (∑ i, localLogMass (s i)) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ (localLogMass_neg (s i)).le
  have hqnonneg : 0 ≤ qform R⁻¹ w := qform_nonneg_of_posSemidef hR.inv.posSemidef w
  have hqle : qform R⁻¹ w ≤ -2 * L := by
    change L ≤ (∑ i, localLogMass (s i)) - 1 / 2 * qform R⁻¹ w at hs
    linarith
  have hwnorm_sq : ‖w‖ ^ 2 ≤ (-2 * L) / κ := by
    apply (le_div_iff₀ hκ).2
    simpa only [mul_comm] using (hcoerc w).trans hqle
  have hquot_nonneg : 0 ≤ (-2 * L) / κ := div_nonneg (by linarith) hκ.le
  have hwnorm : ‖w‖ ≤ W := by
    dsimp only [W]
    nlinarith [Real.sq_sqrt hquot_nonneg, norm_nonneg w,
      Real.sqrt_nonneg ((-2 * L) / κ)]
  have hscoord : ∀ i : Fin m, |s i| ≤ C := by
    intro i
    have hpot_le : adaptivePotential R c s ≤ localLogMass (s i) := by
      rw [adaptivePotential]
      nlinarith [sum_localLogMass_le_single s i, hqnonneg]
    have hlocal : L ≤ localLogMass (s i) := hs.trans hpot_le
    have hlower : B < s i := by
      by_contra hnot
      have htail := hB (s i) (le_of_not_gt hnot)
      linarith
    have hwcoord : w i ≤ W := by
      have habs : |w i| ≤ ‖w‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w i
      exact (le_abs_self (w i)).trans (habs.trans hwnorm)
    have hupper : s i ≤ U := by
      have hsH : s i < H (s i) := by
        rw [H]
        linarith [r_pos (s i)]
      have hH : H (s i) = w i + c := by
        simp [w, displacement]
      dsimp only [U]
      rw [hH] at hsH
      linarith
    apply abs_le.2
    constructor
    · exact (neg_le_neg (le_max_left |B| |U|)).trans
        ((neg_abs_le B).trans hlower.le)
    · exact hupper.trans ((le_abs_self U).trans (le_max_right |B| |U|))
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    (∑ i, ‖s i‖ ^ 2) ≤ ∑ _i : Fin m, C ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (norm_nonneg _) hC).2
      simpa only [Real.norm_eq_abs] using hscoord i
    _ = (m : ℝ) * C ^ 2 := by simp

lemma isCompact_adaptivePotential_superlevel
    {m : ℕ}
    {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c L : ℝ) (hL : L < 0) :
    IsCompact {s : Coord m | L ≤ adaptivePotential R c s} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le continuous_const (continuous_adaptivePotential R c)
  · exact isBounded_adaptivePotential_superlevel hR c L hL

theorem exists_adaptivePotential_maximizer
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef)
    (c : ℝ) :
    ∃ sStar : Coord m,
      ∀ s : Coord m, adaptivePotential R c s ≤ adaptivePotential R c sStar := by
  let base : Coord m := 0
  let baseValue : ℝ := adaptivePotential R c base
  let L : ℝ := baseValue - 1
  let K : Set (Coord m) := {s | L ≤ adaptivePotential R c s}
  have hbaseValue : baseValue ≤ 0 := by
    have hsum : (∑ i, localLogMass (base i)) ≤ 0 :=
      Finset.sum_nonpos fun i _ ↦ (localLogMass_neg (base i)).le
    have hq : 0 ≤ qform R⁻¹ (displacement c base) :=
      qform_nonneg_of_posSemidef hR.inv.posSemidef _
    dsimp only [baseValue]
    rw [adaptivePotential]
    linarith
  have hL : L < 0 := by
    dsimp only [L]
    linarith
  have hbaseK : base ∈ K := by
    change L ≤ adaptivePotential R c base
    dsimp only [L, baseValue]
    linarith
  have hKcompact : IsCompact K := by
    dsimp only [K]
    exact isCompact_adaptivePotential_superlevel hR c L hL
  obtain ⟨sStar, hsStarK, hsStarMax⟩ := hKcompact.exists_isMaxOn
    ⟨base, hbaseK⟩ (continuous_adaptivePotential R c).continuousOn
  refine ⟨sStar, fun s ↦ ?_⟩
  by_cases hsK : s ∈ K
  · exact (isMaxOn_iff.mp hsStarMax) s hsK
  · have hsbelow : adaptivePotential R c s < L := by
      simpa only [K, Set.mem_setOf_eq, not_le] using hsK
    exact (hsbelow.trans_le hsStarK).le

theorem exists_adaptivePotential_maximizer_with_value
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef)
    (hdom : (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef)
    (c : ℝ) :
    ∃ sStar : Coord m,
      (∀ s : Coord m, adaptivePotential R c s ≤ adaptivePotential R c sStar) ∧
      (m : ℝ) * Real.log (normalCDF c) ≤ adaptivePotential R c sStar := by
  obtain ⟨sStar, hmax⟩ := exists_adaptivePotential_maximizer R hR c
  refine ⟨sStar, hmax, ?_⟩
  exact (adaptivePotential_trial_ge hm hR hdom c).trans
    (hmax (c • allOnesVector m))

end

end WeakSimplex
