import WeakSimplexConjectureLean.LogConcavity.Basic
import WeakSimplexConjectureLean.Vendor.StatLean.PrekopaLeindler

/-!
# Prékopa marginalization

This module wraps the attributed StatLean Prékopa--Leindler theorem and exposes the exact
log-concave marginalization and convolution interfaces used downstream.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WeakSimplex

universe u v

/-- Project wrapper around the attributed finite-dimensional Prékopa--Leindler theorem. -/
theorem prekopa_leindler
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z :=
  Vendor.StatLean.AsymptoticStatistics.prekopaLeindler
    hf_meas hg_meas hh_meas ht_pos ht_lt h_le

/-- Integrating out finite-dimensional Euclidean coordinates preserves log-concavity. -/
theorem isLogConcave_lintegral_right
    {E : Type u} {ι : Type v}
    [AddCommMonoid E] [Module ℝ E] [Fintype ι]
    {F : E → (ι → ℝ) → ℝ≥0∞}
    (hF_meas : ∀ x, Measurable (F x))
    (hF_lc : IsLogConcave (fun p : E × (ι → ℝ) ↦ F p.1 p.2)) :
    IsLogConcave (fun x ↦ ∫⁻ y, F x y) := by
  intro t ht_pos ht_lt x y
  exact prekopa_leindler (f := F x) (g := F y)
    (h := F (t • x + (1 - t) • y))
    (hF_meas x) (hF_meas y) (hF_meas (t • x + (1 - t) • y))
    ht_pos ht_lt fun a b ↦ by
      simpa using hF_lc ht_pos ht_lt (x, a) (y, b)

/-- Measurable log-concave marginalization, including the measurability needed for iteration. -/
theorem measurable_isLogConcave_lintegral_right
    {E : Type u} {ι : Type v}
    [MeasurableSpace E] [AddCommMonoid E] [Module ℝ E] [Fintype ι]
    {F : E → (ι → ℝ) → ℝ≥0∞}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_lc : IsLogConcave (fun p : E × (ι → ℝ) ↦ F p.1 p.2)) :
    Measurable (fun x ↦ ∫⁻ y, F x y) ∧
      IsLogConcave (fun x ↦ ∫⁻ y, F x y) := by
  refine ⟨hF_meas.lintegral_prod_right, isLogConcave_lintegral_right ?_ hF_lc⟩
  intro x
  exact hF_meas.comp (measurable_const.prodMk measurable_id)

/-- Convolution preserves measurable log-concavity in finite-dimensional coordinates. -/
theorem measurable_isLogConcave_convolution
    {ι : Type v} [Fintype ι]
    {f g : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_lc : IsLogConcave f) (hg_lc : IsLogConcave g) :
    Measurable (fun x ↦ ∫⁻ y, f (x - y) * g y) ∧
      IsLogConcave (fun x ↦ ∫⁻ y, f (x - y) * g y) := by
  let F : (ι → ℝ) → (ι → ℝ) → ℝ≥0∞ := fun x y ↦ f (x - y) * g y
  have hF_meas : Measurable (Function.uncurry F) :=
    (hf_meas.comp (measurable_fst.sub measurable_snd)).mul
      (hg_meas.comp measurable_snd)
  have hF_lc : IsLogConcave (fun p : (ι → ℝ) × (ι → ℝ) ↦ F p.1 p.2) := by
    intro t ht_pos ht_lt p q
    change (f (p.1 - p.2) * g p.2) ^ t *
      (f (q.1 - q.2) * g q.2) ^ (1 - t) ≤ _
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le,
      ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht_lt.le)]
    calc
      (f (p.1 - p.2) ^ t * g p.2 ^ t) *
          (f (q.1 - q.2) ^ (1 - t) * g q.2 ^ (1 - t)) =
        (f (p.1 - p.2) ^ t * f (q.1 - q.2) ^ (1 - t)) *
          (g p.2 ^ t * g q.2 ^ (1 - t)) := by
            ac_rfl
      _ ≤ f (t • (p.1 - p.2) + (1 - t) • (q.1 - q.2)) *
          g (t • p.2 + (1 - t) • q.2) :=
        mul_le_mul (hf_lc ht_pos ht_lt _ _) (hg_lc ht_pos ht_lt _ _) bot_le bot_le
      _ = F ((t • p + (1 - t) • q).1) ((t • p + (1 - t) • q).2) := by
        congr 1
        congr 1
        funext i
        change t * (p.1 i - p.2 i) + (1 - t) * (q.1 i - q.2 i) =
          (t * p.1 i + (1 - t) * q.1 i) -
            (t * p.2 i + (1 - t) * q.2 i)
        ring
  simpa only [F] using measurable_isLogConcave_lintegral_right hF_meas hF_lc

end WeakSimplex
