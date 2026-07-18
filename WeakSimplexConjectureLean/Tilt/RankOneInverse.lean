import WeakSimplexConjectureLean.Core.QuadraticCoercivity

/-!
# Rank-one inverse bound

This module proves the inverse quadratic bound forced by weak-simplex covariance domination. The
proof evaluates the semidefinite difference at the inverse image of the all-ones vector.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace WeakSimplex

private theorem qform_sub
    {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) :
    qform (A - B) x = qform A x - qform B x := by
  simp [qform, matrixMul, inner_sub_right]

private theorem qform_smul_matrix
    {m : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) :
    qform (c • A) x = c * qform A x := by
  simp [qform, matrixMul, real_inner_smul_right]

private theorem qform_allOnesMatrix {m : ℕ} (x : Coord m) :
    qform (allOnesMatrix m) x = (∑ i, x i) ^ 2 := by
  rw [qform_eq_dotProduct]
  simp [allOnesMatrix, Matrix.mulVec, dotProduct, Coord.toFun, pow_two,
    Finset.sum_mul]

private theorem inner_allOnesVector {m : ℕ} (x : Coord m) :
    ⟪allOnesVector m, x⟫_ℝ = ∑ i, x i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [allOnesVector, dotProduct]

private theorem allOnesVector_ne_zero {m : ℕ} (hm : 0 < m) :
    allOnesVector m ≠ 0 := by
  intro h
  let i : Fin m := ⟨0, hm⟩
  have hi := congrArg (fun x : Coord m ↦ x i) h
  change (1 : ℝ) = 0 at hi
  exact one_ne_zero hi

/-- The weak-simplex rank-one domination bounds the inverse quadratic form at the all-ones
vector. -/
theorem rankOne_inverse_bound
    {m : ℕ} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : R.PosDef)
    (hdom : (R - (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef) :
    qform R⁻¹ (allOnesVector m) ≤ (m : ℝ) := by
  classical
  let one : Coord m := allOnesVector m
  let x : Coord m := matrixMul R⁻¹ one
  let t : ℝ := qform R⁻¹ one
  have hone : one ≠ 0 := by
    simpa only [one] using allOnesVector_ne_zero hm
  have htpos : 0 < t := by
    exact qform_pos_of_posDef hR.inv hone
  have hRx : matrixMul R x = one := by
    exact matrixMul_inv_right hR one
  have hqRx : qform R x = t := by
    calc
      qform R x = ⟪x, matrixMul R x⟫_ℝ := rfl
      _ = ⟪x, one⟫_ℝ := by rw [hRx]
      _ = ⟪one, x⟫_ℝ := (real_inner_comm x one).symm
      _ = t := rfl
  have hsum : (∑ i, x i) = t := by
    calc
      (∑ i, x i) = ⟪one, x⟫_ℝ := by
        simpa only [one] using (inner_allOnesVector x).symm
      _ = t := rfl
  have hnonneg := qform_nonneg_of_posSemidef hdom x
  rw [qform_sub, qform_smul_matrix, hqRx, qform_allOnesMatrix, hsum] at hnonneg
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := hmr.ne'
  have hscaled : 0 ≤ (t - (1 / (m : ℝ)) * t ^ 2) * (m : ℝ) :=
    mul_nonneg hnonneg hmr.le
  have hfactor :
      (t - (1 / (m : ℝ)) * t ^ 2) * (m : ℝ) = t * ((m : ℝ) - t) := by
    field_simp
  rw [hfactor] at hscaled
  change t ≤ (m : ℝ)
  nlinarith

end WeakSimplex
