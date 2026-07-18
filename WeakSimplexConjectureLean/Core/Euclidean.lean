import WeakSimplexConjectureLean.Core.Finite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Euclidean coordinates and lower orthants

This module centralizes conversion between finite functions and Euclidean space and defines the
equal-threshold lower orthant.
-/

noncomputable section

namespace WeakSimplex

/-- The real Euclidean coordinate space indexed by `Fin m`. -/
abbrev Coord (m : ℕ) := EuclideanSpace ℝ (Fin m)

namespace Coord

/-- Regard a finite real-valued function as a Euclidean coordinate vector. -/
def ofFun {m : ℕ} (x : Fin m → ℝ) : Coord m :=
  WithLp.toLp 2 x

/-- Regard a Euclidean coordinate vector as a finite real-valued function. -/
def toFun {m : ℕ} (x : Coord m) : Fin m → ℝ :=
  WithLp.ofLp x

@[simp]
theorem ofFun_apply {m : ℕ} (x : Fin m → ℝ) (i : Fin m) : ofFun x i = x i :=
  rfl

@[simp]
theorem toFun_apply {m : ℕ} (x : Coord m) (i : Fin m) : toFun x i = x i :=
  rfl

@[simp]
theorem ofFun_toFun {m : ℕ} (x : Coord m) : ofFun (toFun x) = x :=
  WithLp.toLp_ofLp 2 x

@[simp]
theorem toFun_ofFun {m : ℕ} (x : Fin m → ℝ) : toFun (ofFun x) = x :=
  WithLp.ofLp_toLp 2 x

end Coord

/-- Apply a scalar function coordinatewise to a Euclidean vector. -/
def coordinateMap {m : ℕ} (f : ℝ → ℝ) (x : Coord m) : Coord m :=
  Coord.ofFun (fun i ↦ f (x i))

@[simp]
theorem coordinateMap_apply {m : ℕ} (f : ℝ → ℝ) (x : Coord m) (i : Fin m) :
    coordinateMap f x i = f (x i) :=
  rfl

/-- The Euclidean vector whose coordinates are all one. -/
def allOnesVector (m : ℕ) : Coord m :=
  Coord.ofFun (fun _ ↦ 1)

@[simp]
theorem allOnesVector_apply (m : ℕ) (i : Fin m) : allOnesVector m i = 1 :=
  rfl

/-- The set of vectors whose coordinates are all at most `c`. -/
def lowerOrthant {m : ℕ} (c : ℝ) : Set (Coord m) :=
  {x | ∀ i, x i ≤ c}

/-- An equal-threshold lower orthant is measurable. -/
theorem measurableSet_lowerOrthant {m : ℕ} (c : ℝ) :
    MeasurableSet (lowerOrthant (m := m) c) := by
  rw [lowerOrthant, Set.setOf_forall]
  refine MeasurableSet.iInter fun i ↦ measurableSet_le ?_ measurable_const
  simpa only [EuclideanSpace.coe_proj] using
    (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

end WeakSimplex
