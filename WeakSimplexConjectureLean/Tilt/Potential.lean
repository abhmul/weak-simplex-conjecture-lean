import WeakSimplexConjectureLean.Normal.TiltFunctions
import WeakSimplexConjectureLean.Tilt.RankOneInverse

/-!
# Adaptive potential

This module defines the unconstrained scalar-coordinate potential and proves its continuity and
symmetric trial-point bound.
-/

namespace WeakSimplex

noncomputable section

open scoped BigOperators InnerProductSpace Topology

def displacement {m : ℕ} (c : ℝ) (s : Coord m) : Coord m :=
  coordinateMap H s - c • allOnesVector m

def adaptivePotential {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (s : Coord m) : ℝ :=
  ∑ i, localLogMass (s i) - 1 / 2 * qform R⁻¹ (displacement c s)

lemma continuous_H : Continuous H := by
  rw [continuous_iff_continuousAt]
  exact fun s ↦ (hasDerivAt_H s).continuousAt

lemma continuous_localLogMass : Continuous localLogMass := by
  rw [continuous_iff_continuousAt]
  exact fun s ↦ (hasDerivAt_localLogMass s).continuousAt

lemma continuous_displacement {m : ℕ} (c : ℝ) :
    Continuous (displacement (m := m) c) := by
  have hmap : Continuous (coordinateMap H : Coord m → Coord m) := by
    unfold coordinateMap Coord.ofFun
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m ↦ ℝ)).comp
    apply continuous_pi
    intro i
    exact continuous_H.comp (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i)
  exact hmap.sub (continuous_const.smul continuous_const)

lemma continuous_adaptivePotential {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    Continuous (adaptivePotential R c) := by
  have hlocal : Continuous (fun s : Coord m ↦ ∑ i, localLogMass (s i)) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_localLogMass.comp
      (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i)
  have hdisp := continuous_displacement (m := m) c
  unfold adaptivePotential qform matrixMul
  exact hlocal.sub (continuous_const.mul
    (hdisp.inner ((Matrix.toEuclideanCLM (𝕜 := ℝ) R⁻¹).continuous.comp hdisp)))

lemma adaptivePotential_trial_ge
    {m : ℕ} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef)
    (hdom : (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef)
    (c : ℝ) :
    (m : ℝ) * Real.log (normalCDF c) ≤
      adaptivePotential R c (c • allOnesVector m) := by
  have hdisp : displacement c (c • allOnesVector m) = r c • allOnesVector m := by
    ext i
    simp [displacement, H]
  have hsum :
      (∑ i, localLogMass ((c • allOnesVector m) i)) =
        (m : ℝ) * localLogMass c := by
    simp [allOnesVector]
  have hq := rankOne_inverse_bound hm hR hdom
  rw [adaptivePotential, hdisp, qform_smul, hsum, localLogMass]
  nlinarith [sq_nonneg (r c)]

end

end WeakSimplex
