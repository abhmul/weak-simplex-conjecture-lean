import WeakSimplexConjectureLean.Tilt.AdaptiveWitnesses
import WeakSimplexConjectureLean.Tilt.TiltedHalfLine

/-!
# Adaptive event shift

This module rewrites the shifted coordinatewise adaptive endpoint event as the target
equal-threshold lower orthant.
-/

namespace WeakSimplex

noncomputable section

theorem AdaptiveWitnesses.endpoint_eq_H
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) :
    w.s i + w.a i = H (w.s i) := by
  rw [w.a_eq_r]
  rfl

theorem AdaptiveWitnesses.shift_le_endpoint_iff
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) :
    (∀ i, (x + matrixMul R w.a) i ≤ w.s i + w.a i) ↔
      x ∈ lowerOrthant c := by
  have hcomp : ∀ i,
      w.s i + w.a i - (matrixMul R w.a) i = c := by
    intro i
    have hi := congrArg (fun y : Coord m ↦ y i) w.compatibility
    change w.s i + w.a i - (matrixMul R w.a) i = c * 1 at hi
    simpa only [mul_one] using hi
  constructor
  · intro h i
    have hi := h i
    have hc := hcomp i
    change x i ≤ c
    change x i + (matrixMul R w.a) i ≤ w.s i + w.a i at hi
    linarith
  · intro h i
    have hi := h i
    have hc := hcomp i
    change x i + (matrixMul R w.a) i ≤ w.s i + w.a i
    linarith

theorem AdaptiveWitnesses.shift_le_H_iff
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (x : Coord m) :
    (∀ i, (x + matrixMul R w.a) i ≤ H (w.s i)) ↔
      x ∈ lowerOrthant c := by
  simpa only [← w.endpoint_eq_H] using w.shift_le_endpoint_iff x

theorem AdaptiveWitnesses.preimage_adaptiveEndpoints_shift
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    (fun x ↦ x + matrixMul R w.a) ⁻¹'
        {y : Coord m | ∀ i, y i ≤ H (w.s i)} =
      lowerOrthant c := by
  ext x
  exact w.shift_le_H_iff x

end

end WeakSimplex
