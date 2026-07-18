import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Elementary log-concavity

This module defines the strict-weight `ℝ≥0∞` log-concavity interface used by the vendored
Prékopa theorem and proves its elementary closure properties.
-/

namespace WeakSimplex

universe u v

open scoped ENNReal

/-- Strict-weight log-concavity for extended-nonnegative-valued functions. -/
def IsLogConcave {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ≥0∞) : Prop :=
  ∀ ⦃t : ℝ⦄, 0 < t → t < 1 → ∀ x y,
    f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)

/-- A constant extended-nonnegative-valued function is log-concave. -/
theorem isLogConcave_const
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (c : ℝ≥0∞) :
    IsLogConcave (fun _ : E ↦ c) := by
  intro t ht_pos ht_lt x y
  rw [← ENNReal.rpow_add_of_nonneg t (1 - t) ht_pos.le (sub_nonneg.mpr ht_lt.le)]
  norm_num

/-- A pointwise product of log-concave functions is log-concave. -/
theorem IsLogConcave.mul
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {f g : E → ℝ≥0∞}
    (hf : IsLogConcave f) (hg : IsLogConcave g) :
    IsLogConcave (f * g) := by
  intro t ht_pos ht_lt x y
  rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply,
    ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le,
    ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht_lt.le)]
  calc
    (f x ^ t * g x ^ t) * (f y ^ (1 - t) * g y ^ (1 - t)) =
        (f x ^ t * f y ^ (1 - t)) * (g x ^ t * g y ^ (1 - t)) := by
      ac_rfl
    _ ≤ f (t • x + (1 - t) • y) * g (t • x + (1 - t) • y) :=
      mul_le_mul (hf ht_pos ht_lt x y) (hg ht_pos ht_lt x y) bot_le bot_le

/-- Precomposition by an affine map preserves log-concavity. -/
theorem IsLogConcave.comp_affineMap
    {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] {f : G → ℝ≥0∞}
    (hf : IsLogConcave f) (A : E →ᵃ[ℝ] G) :
    IsLogConcave (f ∘ A) := by
  intro t ht_pos ht_lt x y
  have h := hf ht_pos ht_lt (A x) (A y)
  have hA := A.apply_lineMap y x t
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hA
  have hA' : A (t • x + (1 - t) • y) = t • A x + (1 - t) • A y := by
    simpa only [add_comm] using hA
  simpa only [Function.comp_apply, hA'] using h

end WeakSimplex
