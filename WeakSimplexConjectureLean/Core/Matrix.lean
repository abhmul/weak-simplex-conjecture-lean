import WeakSimplexConjectureLean.Core.Euclidean
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Matrix action and quadratic forms

This module fixes the project's all-ones matrix, Euclidean matrix action, and real quadratic-form
representation.
-/

noncomputable section

open scoped InnerProductSpace

namespace WeakSimplex

/-- The square matrix whose entries are all one. -/
def allOnesMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun _ _ ↦ 1

@[simp]
theorem allOnesMatrix_apply (m : ℕ) (i j : Fin m) : allOnesMatrix m i j = 1 :=
  rfl

/-- Apply a square real matrix to a Euclidean coordinate vector. -/
def matrixMul {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) : Coord m :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) R x

@[simp]
theorem matrixMul_ofFun {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    matrixMul R (Coord.ofFun x) = Coord.ofFun (R.mulVec x) :=
  Matrix.toEuclideanCLM_toLp R x

/-- The quadratic form of a real matrix on Euclidean coordinate space. -/
def qform {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) : ℝ :=
  ⟪x, matrixMul R x⟫_ℝ

/-- Express the project quadratic form as a finite dot product. -/
theorem qform_eq_dotProduct {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) :
    qform R x = Coord.toFun x ⬝ᵥ R.mulVec (Coord.toFun x) := by
  simpa only [qform, matrixMul, Coord.toFun] using Matrix.inner_toEuclideanCLM R x x

end WeakSimplex
