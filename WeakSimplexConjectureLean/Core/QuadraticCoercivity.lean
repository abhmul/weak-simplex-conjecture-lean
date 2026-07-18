import WeakSimplexConjectureLean.Core.Correlation
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Positive-definite quadratic coercivity

This module supplies positivity, symmetry, inverse-action, and coercivity lemmas for the project
quadratic form on finite-dimensional Euclidean coordinate spaces.
-/

noncomputable section

open scoped InnerProductSpace

namespace WeakSimplex

/-- A positive-semidefinite matrix has a nonnegative project quadratic form. -/
theorem qform_nonneg_of_posSemidef
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (x : Coord m) :
    0 ≤ qform A x := by
  rw [qform_eq_dotProduct]
  simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (Coord.toFun x)

/-- A positive-definite matrix has a positive project quadratic form away from zero. -/
theorem qform_pos_of_posDef
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) {x : Coord m} (hx : x ≠ 0) :
    0 < qform A x := by
  rw [qform_eq_dotProduct]
  apply hA.dotProduct_mulVec_pos
  intro h
  apply hx
  calc
    x = Coord.ofFun (Coord.toFun x) := (Coord.ofFun_toFun x).symm
    _ = Coord.ofFun 0 := congrArg Coord.ofFun h
    _ = 0 := rfl

/-- The project quadratic form is homogeneous of degree two in its vector argument. -/
theorem qform_smul
    {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (c : ℝ) (x : Coord m) :
    qform A (c • x) = c ^ 2 * qform A x := by
  simp only [qform, matrixMul, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Matrix action by a positive-definite real matrix is self-adjoint. -/
theorem inner_matrixMul_eq_of_posDef
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) (x y : Coord m) :
    ⟪matrixMul A x, y⟫_ℝ = ⟪x, matrixMul A y⟫_ℝ := by
  rw [real_inner_comm]
  simp only [matrixMul, Matrix.inner_toEuclideanCLM]
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  simpa only [hsymm.eq, Coord.toFun] using
    (Matrix.dotProduct_transpose_mulVec A (Coord.toFun x) (Coord.toFun y)).symm

/-- Applying a positive-definite matrix after its inverse is the identity. -/
theorem matrixMul_inv_right
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) (x : Coord m) :
    matrixMul A (matrixMul A⁻¹ x) = x := by
  letI := hA.isUnit.invertible
  have h := map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ)) A A⁻¹
  have hx := congrArg (fun T : Coord m →L[ℝ] Coord m ↦ T x) h
  simpa only [matrixMul, Matrix.mul_inv_of_invertible, map_one, one_apply_eq_self,
    mul_apply_eq_comp] using hx.symm

/-- Applying the inverse of a positive-definite matrix after the matrix is the identity. -/
theorem matrixMul_inv_left
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) (x : Coord m) :
    matrixMul A⁻¹ (matrixMul A x) = x := by
  letI := hA.isUnit.invertible
  have h := map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ)) A⁻¹ A
  have hx := congrArg (fun T : Coord m →L[ℝ] Coord m ↦ T x) h
  simpa only [matrixMul, Matrix.inv_mul_of_invertible, map_one, one_apply_eq_self,
    mul_apply_eq_comp] using hx.symm

/-- A positive-definite project quadratic form dominates a positive multiple of norm squared. -/
theorem posDef_quadratic_coercive
    {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : Coord m, κ * ‖x‖ ^ 2 ≤ qform A x := by
  classical
  by_cases hm : m = 0
  · subst m
    refine ⟨1, zero_lt_one, fun x ↦ ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx, qform]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let S : Set (Coord m) := Metric.sphere 0 1
    let q : Coord m → ℝ := fun x ↦
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫_ℝ
    have hScompact : IsCompact S := isCompact_sphere _ _
    have hSne : S.Nonempty := by
      let i : Fin m := ⟨0, hmpos⟩
      refine ⟨EuclideanSpace.single i 1, ?_⟩
      simp [S]
    have hcont : Continuous q :=
      continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) A).continuous
    obtain ⟨y, hyS, hymin⟩ :=
      hScompact.exists_isMinOn hSne hcont.continuousOn
    refine ⟨q y, ?_, fun x ↦ ?_⟩
    · change 0 < qform A y
      apply qform_pos_of_posDef hA
      intro hy
      subst y
      simp [S] at hyS
    · by_cases hx : x = 0
      · subst x
        simp [q, qform]
      · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let z : Coord m := ‖x‖⁻¹ • x
        have hzS : z ∈ S := by
          simp [S, z, norm_smul, hxnorm.ne']
        have hmin : q y ≤ q z := hymin hzS
        have hxz : ‖x‖ • z = x := by
          simp [z, smul_smul, hx]
        change q y * ‖x‖ ^ 2 ≤ q x
        calc
          q y * ‖x‖ ^ 2 ≤ q z * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖x‖)
          _ = q x := by
            rw [mul_comm]
            change ‖x‖ ^ 2 * qform A z = qform A x
            rw [← qform_smul, hxz]

end WeakSimplex
