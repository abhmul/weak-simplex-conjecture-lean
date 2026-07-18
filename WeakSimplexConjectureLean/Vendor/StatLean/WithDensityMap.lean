import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Vendored from StatLean commit `31c61ed887bf3be0def314a3b3e5375d203b5ba1`, original path
`StatLean/AsymptoticStatistics/ForMathlib/Contiguity.lean`, lines 197--213
(Apache-2.0).

Changes are limited to direct imports, this attribution block, and outer
`WeakSimplex.Vendor.StatLean` namespace isolation. The declaration body matches the
selected upstream slice.
-/

namespace WeakSimplex.Vendor.StatLean

open scoped ENNReal

namespace AsymptoticStatistics

/-- **Commuting `withDensity` past `Measure.map`**:
`(μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ`, for measurable `φ` and `h`.

Useful for pushing a density through a measurable pushforward — e.g., when a joint
law `π_tilted = π.map φ` is `withDensity`-ed against a function `h` that factors
through `φ`, the calculation can be pulled back to `π` under the composed density. -/
lemma Measure.withDensity_map_eq_map_withDensity
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : MeasureTheory.Measure α) (φ : α → β) (hφ : Measurable φ)
    (h : β → ℝ≥0∞) (hh : Measurable h) :
    (μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.withDensity_apply _ hA,
      MeasureTheory.Measure.map_apply hφ hA,
      MeasureTheory.withDensity_apply _ (hφ hA),
      MeasureTheory.setLIntegral_map hA hh hφ]
  rfl

end AsymptoticStatistics

end WeakSimplex.Vendor.StatLean
