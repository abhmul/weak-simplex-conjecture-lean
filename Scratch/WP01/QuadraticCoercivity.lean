import WeakSimplexConjectureLean.Core.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Positive-definite quadratic coercivity spike

This scratch theorem tests the compact-unit-sphere proof against the project coordinate wrappers.
-/

noncomputable section

open scoped InnerProductSpace

namespace Matrix.PosDef

lemma exists_quadratic_lower_bound
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : WeakSimplex.Coord m,
        κ * ‖x‖ ^ 2 ≤ ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) A) x⟫_ℝ := by
  rcases subsingleton_or_nontrivial (WeakSimplex.Coord m) with hE | hE
  · letI := hE
    refine ⟨1, zero_lt_one, fun x ↦ ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · letI := hE
    letI := FiniteDimensional.proper_rclike ℝ (WeakSimplex.Coord m)
    let q : WeakSimplex.Coord m → ℝ :=
      fun x ↦ ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) A) x⟫_ℝ
    have hq_cont : Continuous q :=
      continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) A).continuous
    obtain ⟨u, hu⟩ : ∃ u : WeakSimplex.Coord m, u ≠ 0 := exists_ne 0
    let v : WeakSimplex.Coord m := ‖u‖⁻¹ • u
    have hv_norm : ‖v‖ = 1 := by
      simp [v, norm_smul, hu]
    have hv : v ∈ Metric.sphere (0 : WeakSimplex.Coord m) 1 := by
      simpa [Metric.mem_sphere] using hv_norm
    have hs : IsCompact (Metric.sphere (0 : WeakSimplex.Coord m) 1) :=
      isCompact_sphere _ _
    obtain ⟨z, hz, hz_min⟩ :=
      hs.exists_isMinOn ⟨v, hv⟩ hq_cont.continuousOn
    have hz_ne : z ≠ 0 := by
      intro hz_zero
      rw [hz_zero] at hz
      simp at hz
    have hz_fun_ne : WeakSimplex.Coord.toFun z ≠ 0 := by
      intro hz_fun
      apply hz_ne
      rw [← WeakSimplex.Coord.ofFun_toFun z, hz_fun]
      rfl
    have hq_z_pos : 0 < q z := by
      change 0 < WeakSimplex.qform A z
      rw [WeakSimplex.qform_eq_dotProduct]
      simpa using hA.dotProduct_mulVec_pos hz_fun_ne
    refine ⟨q z, hq_z_pos, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · let y : WeakSimplex.Coord m := ‖x‖⁻¹ • x
      have hy_norm : ‖y‖ = 1 := by
        simp [y, norm_smul, hx]
      have hy : y ∈ Metric.sphere (0 : WeakSimplex.Coord m) 1 := by
        simpa [Metric.mem_sphere] using hy_norm
      have hmin : q z ≤ q y := hz_min hy
      have hxy : ‖x‖ • y = x := by
        simp [y, smul_smul, hx]
      have hscale (r : ℝ) (w : WeakSimplex.Coord m) :
          q (r • w) = r ^ 2 * q w := by
        simp [q, map_smul, real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc]
      change q z * ‖x‖ ^ 2 ≤ q x
      calc
        q z * ‖x‖ ^ 2 ≤ q y * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖x‖)
        _ = q x := by
          rw [mul_comm, ← hscale, hxy]

#print axioms Matrix.PosDef.exists_quadratic_lower_bound

end Matrix.PosDef
