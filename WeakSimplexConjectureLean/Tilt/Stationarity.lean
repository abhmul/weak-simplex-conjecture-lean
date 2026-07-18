import WeakSimplexConjectureLean.Tilt.CompactMaximizer
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Coordinate stationarity of the adaptive potential

This module differentiates the adaptive potential along one coordinate line, derives the
stationarity and compatibility equations at a global maximizer, and rewrites its value in the
adaptive-witness form.
-/

namespace WeakSimplex

noncomputable section

open scoped BigOperators InnerProductSpace

private def coordinateLineApply {m : ℕ}
    (s : Coord m) (i j : Fin m) : ℝ → ℝ :=
  (fun _ => s j) + fun t => t * if j = i then 1 else 0

/-- The affine line through `s` in the `i`-th coordinate direction. -/
def coordinateLine {m : ℕ}
    (s : Coord m) (i : Fin m) (t : ℝ) : Coord m :=
  Coord.ofFun fun j => s j + t * if j = i then 1 else 0

/-- Evaluation of a coordinate line at a coordinate. -/
@[simp]
lemma coordinateLine_apply {m : ℕ}
    (s : Coord m) (i j : Fin m) (t : ℝ) :
    coordinateLine s i t j = s j + t * if j = i then 1 else 0 :=
  rfl

/-- A coordinate line passes through its base point at parameter zero. -/
@[simp]
lemma coordinateLine_zero {m : ℕ} (s : Coord m) (i : Fin m) :
    coordinateLine s i 0 = s := by
  apply PiLp.ext
  intro j
  simp

private lemma hasDerivAt_coordinateLineApply {m : ℕ}
    (s : Coord m) (i j : Fin m) :
    HasDerivAt (coordinateLineApply s i j) (if j = i then 1 else 0) 0 := by
  have h :=
    (hasDerivAt_const (x := (0 : ℝ)) (s j)).add
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (if j = i then 1 else 0))
  simpa only [coordinateLineApply, id_eq, zero_add, one_mul] using h

private def coordinateLineH {m : ℕ}
    (s : Coord m) (i j : Fin m) : ℝ → ℝ :=
  H ∘ coordinateLineApply s i j

private def coordinateLineLocalLogMass {m : ℕ}
    (s : Coord m) (i j : Fin m) : ℝ → ℝ :=
  localLogMass ∘ coordinateLineApply s i j

private lemma hasDerivAt_H_coordinateLineApply {m : ℕ}
    (s : Coord m) (i j : Fin m) :
    HasDerivAt (coordinateLineH s i j)
      ((1 - s j * r (s j) - (r (s j)) ^ 2) * if j = i then 1 else 0) 0 := by
  have h := (hasDerivAt_H (coordinateLineApply s i j 0)).comp 0
    (hasDerivAt_coordinateLineApply s i j)
  simpa only [coordinateLineH, coordinateLineApply, Pi.add_apply, id_eq, zero_mul,
    add_zero] using h

private lemma hasDerivAt_localLogMass_coordinateLineApply {m : ℕ}
    (s : Coord m) (i j : Fin m) :
    HasDerivAt (coordinateLineLocalLogMass s i j)
      (r (s j) * (1 - s j * r (s j) - (r (s j)) ^ 2) *
        if j = i then 1 else 0) 0 := by
  have h := (hasDerivAt_localLogMass (coordinateLineApply s i j 0)).comp 0
    (hasDerivAt_coordinateLineApply s i j)
  simpa only [coordinateLineLocalLogMass, coordinateLineApply, Pi.add_apply, id_eq,
    zero_mul, add_zero] using h

private def coordinateLineLocalSum {m : ℕ}
    (s : Coord m) (i : Fin m) : ℝ → ℝ :=
  fun t => ∑ j, coordinateLineLocalLogMass s i j t

private lemma hasDerivAt_coordinateLineLocalSum {m : ℕ}
    (s : Coord m) (i : Fin m) :
    HasDerivAt (coordinateLineLocalSum s i)
      (r (s i) * (1 - s i * r (s i) - (r (s i)) ^ 2)) 0 := by
  classical
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    hasDerivAt_localLogMass_coordinateLineApply s i j
  have hderiv :
      (∑ j, r (s j) * (1 - s j * r (s j) - (r (s j)) ^ 2) *
        if j = i then 1 else 0) =
        r (s i) * (1 - s i * r (s i) - (r (s i)) ^ 2) := by
    simp
  exact (hsum.congr_deriv hderiv).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

private lemma matrixMul_apply_sum {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (x : Coord m) (j : Fin m) :
    matrixMul A x j = ∑ k, A j k * x k := by
  rw [show x = Coord.ofFun (fun k => x k) by
    exact (Coord.ofFun_toFun x).symm]
  simp [Matrix.mulVec, dotProduct]

private def coordinateLineDisplacement {m : ℕ}
    (c : ℝ) (s : Coord m) (i j : Fin m) : ℝ → ℝ :=
  fun t => coordinateLineH s i j t - c

private lemma coordinateLineDisplacement_zero {m : ℕ}
    (c : ℝ) (s : Coord m) (i j : Fin m) :
    coordinateLineDisplacement c s i j 0 = displacement c s j := by
  simp [coordinateLineDisplacement, coordinateLineH, coordinateLineApply, displacement]

private lemma hasDerivAt_coordinateLineDisplacement {m : ℕ}
    (c : ℝ) (s : Coord m) (i j : Fin m) :
    HasDerivAt (coordinateLineDisplacement c s i j)
      ((1 - s j * r (s j) - (r (s j)) ^ 2) * if j = i then 1 else 0) 0 := by
  have h := (hasDerivAt_H_coordinateLineApply s i j).sub_const c
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

private def coordinateLineMatrixRow {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i j : Fin m) : ℝ → ℝ :=
  fun t => ∑ k, A j k * coordinateLineDisplacement c s i k t

private lemma coordinateLineMatrixRow_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i j : Fin m) :
    coordinateLineMatrixRow A c s i j 0 = matrixMul A (displacement c s) j := by
  simp only [coordinateLineMatrixRow, coordinateLineDisplacement_zero]
  exact (matrixMul_apply_sum A (displacement c s) j).symm

private lemma hasDerivAt_coordinateLineMatrixRow {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i j : Fin m) :
    HasDerivAt (coordinateLineMatrixRow A c s i j)
      (A j i * (1 - s i * r (s i) - (r (s i)) ^ 2)) 0 := by
  classical
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_coordinateLineDisplacement c s i k).const_mul (A j k)
  have hderiv :
      (∑ k, A j k *
        ((1 - s k * r (s k) - (r (s k)) ^ 2) * if k = i then 1 else 0)) =
        A j i * (1 - s i * r (s i) - (r (s i)) ^ 2) := by
    simp
  exact (hsum.congr_deriv hderiv).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

private def coordinateLineQformTerm {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i j : Fin m) : ℝ → ℝ :=
  coordinateLineDisplacement c s i j * coordinateLineMatrixRow A c s i j

private lemma hasDerivAt_coordinateLineQformTerm {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i j : Fin m) :
    HasDerivAt (coordinateLineQformTerm A c s i j)
      (((1 - s j * r (s j) - (r (s j)) ^ 2) * if j = i then 1 else 0) *
          matrixMul A (displacement c s) j +
        displacement c s j *
          (A j i * (1 - s i * r (s i) - (r (s i)) ^ 2))) 0 := by
  have h := (hasDerivAt_coordinateLineDisplacement c s i j).mul
    (hasDerivAt_coordinateLineMatrixRow A c s i j)
  simpa only [coordinateLineQformTerm, coordinateLineDisplacement_zero,
    coordinateLineMatrixRow_zero] using h

private def coordinateLineQform {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i : Fin m) : ℝ → ℝ :=
  fun t => ∑ j, coordinateLineQformTerm A c s i j t

private lemma hasDerivAt_coordinateLineQform {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm)
    (c : ℝ) (s : Coord m) (i : Fin m) :
    HasDerivAt (coordinateLineQform A c s i)
      (2 * (1 - s i * r (s i) - (r (s i)) ^ 2) *
        matrixMul A (displacement c s) i) 0 := by
  classical
  let D : Fin m → ℝ := fun j => 1 - s j * r (s j) - (r (s j)) ^ 2
  let w : Coord m := displacement c s
  let v : Coord m := matrixMul A w
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    hasDerivAt_coordinateLineQformTerm A c s i j
  have hfirst :
      (∑ j, (D j * (if j = i then 1 else 0)) * v j) = D i * v i := by
    simp
  have hsecond :
      (∑ j, w j * (A j i * D i)) = D i * v i := by
    rw [show v i = ∑ j, A i j * w j by
      exact matrixMul_apply_sum A w i]
    calc
      (∑ j, w j * (A j i * D i)) = ∑ j, D i * (A i j * w j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hA.apply i j]
        ring
      _ = D i * ∑ j, A i j * w j := by rw [Finset.mul_sum]
  have hderiv :
      (∑ j,
        ((D j * (if j = i then 1 else 0)) * v j + w j * (A j i * D i))) =
        2 * D i * v i := by
    rw [Finset.sum_add_distrib, hfirst, hsecond]
    ring
  have hsum' := hsum.congr_deriv (by simpa only [D, w, v] using hderiv)
  exact hsum'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

private lemma coordinateLineQform_eq {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i : Fin m) (t : ℝ) :
    coordinateLineQform A c s i t =
      qform A (displacement c (coordinateLine s i t)) := by
  rw [qform_eq_dotProduct]
  simp [coordinateLineQform, coordinateLineQformTerm, coordinateLineMatrixRow,
    coordinateLineDisplacement, coordinateLineH, coordinateLine, coordinateLineApply,
    displacement, dotProduct, Matrix.mulVec]

private lemma coordinateLineLocalSum_eq {m : ℕ}
    (s : Coord m) (i : Fin m) (t : ℝ) :
    coordinateLineLocalSum s i t =
      ∑ j, localLogMass (coordinateLine s i t j) := by
  rfl

/-- The adaptive potential restricted to the `i`-th coordinate line through `s`. -/
def adaptivePotentialCoordinateLine {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (s : Coord m) (i : Fin m) : ℝ → ℝ :=
  fun t => adaptivePotential R c (coordinateLine s i t)

/-- The coordinate-line derivative of the adaptive potential at its base point. -/
lemma hasDerivAt_adaptivePotentialCoordinateLine
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c : ℝ) (s : Coord m) (i : Fin m) :
    HasDerivAt (adaptivePotentialCoordinateLine R c s i)
      ((1 - s i * r (s i) - (r (s i)) ^ 2) *
        (r (s i) - matrixMul R⁻¹ (displacement c s) i)) 0 := by
  have hsymm : (R⁻¹).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp hR.inv.isHermitian
  have hlocal := hasDerivAt_coordinateLineLocalSum s i
  have hq := hasDerivAt_coordinateLineQform hsymm c s i
  have h := hlocal.sub (hq.const_mul (1 / 2))
  have hderiv :
      r (s i) * (1 - s i * r (s i) - (r (s i)) ^ 2) -
          (1 / 2) *
            (2 * (1 - s i * r (s i) - (r (s i)) ^ 2) *
              matrixMul R⁻¹ (displacement c s) i) =
        (1 - s i * r (s i) - (r (s i)) ^ 2) *
          (r (s i) - matrixMul R⁻¹ (displacement c s) i) := by
    ring
  apply (h.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with t
  simp only [Pi.sub_apply]
  unfold adaptivePotentialCoordinateLine adaptivePotential
  rw [← coordinateLineLocalSum_eq, ← coordinateLineQform_eq]

/-- Every coordinate derivative of the adaptive potential vanishes at a global maximizer. -/
lemma adaptivePotential_stationary_coordinate
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c : ℝ) (s : Coord m)
    (hmax : ∀ t : Coord m,
      adaptivePotential R c t ≤ adaptivePotential R c s)
    (i : Fin m) :
    r (s i) = matrixMul R⁻¹ (displacement c s) i := by
  have hlocal : IsLocalMax (adaptivePotentialCoordinateLine R c s i) 0 := by
    filter_upwards with t
    unfold adaptivePotentialCoordinateLine
    simpa only [coordinateLine_zero] using hmax (coordinateLine s i t)
  have hzero := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_adaptivePotentialCoordinateLine hR c s i)
  nlinarith [H_deriv_pos (s i)]

/-- Coordinate stationarity as a vector inverse-displacement identity. -/
lemma coordinateMap_r_eq_inv_displacement
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c : ℝ) (s : Coord m)
    (hmax : ∀ t : Coord m,
      adaptivePotential R c t ≤ adaptivePotential R c s) :
    coordinateMap r s = matrixMul R⁻¹ (displacement c s) := by
  apply PiLp.ext
  intro i
  exact adaptivePotential_stationary_coordinate hR c s hmax i

/-- A global maximizer and its reciprocal-Mills coordinates satisfy adaptive compatibility. -/
lemma adaptivePotential_compatibility
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c : ℝ) (s : Coord m)
    (hmax : ∀ t : Coord m,
      adaptivePotential R c t ≤ adaptivePotential R c s) :
    s + coordinateMap r s - matrixMul R (coordinateMap r s) =
      c • allOnesVector m := by
  have hinv := coordinateMap_r_eq_inv_displacement hR c s hmax
  have hmul : matrixMul R (coordinateMap r s) = displacement c s := by
    rw [hinv]
    exact matrixMul_inv_right hR (displacement c s)
  rw [hmul]
  apply PiLp.ext
  intro i
  simp [displacement, H]

/-- Rewrite the adaptive-potential value at a global maximizer in witness coordinates. -/
lemma adaptivePotential_value_identity
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosDef)
    (c : ℝ) (s : Coord m)
    (hmax : ∀ t : Coord m,
      adaptivePotential R c t ≤ adaptivePotential R c s) :
    adaptivePotential R c s =
      (∑ i, Real.log (normalCDF (s i))) +
        (⟪coordinateMap r s, coordinateMap r s⟫_ℝ -
          ⟪coordinateMap r s, matrixMul R (coordinateMap r s)⟫_ℝ) / 2 := by
  let a : Coord m := coordinateMap r s
  have hinv : a = matrixMul R⁻¹ (displacement c s) := by
    exact coordinateMap_r_eq_inv_displacement hR c s hmax
  have hmul : matrixMul R a = displacement c s := by
    rw [hinv]
    exact matrixMul_inv_right hR (displacement c s)
  have hq : qform R⁻¹ (displacement c s) = ⟪a, matrixMul R a⟫_ℝ := by
    calc
      qform R⁻¹ (displacement c s) =
          ⟪displacement c s, matrixMul R⁻¹ (displacement c s)⟫_ℝ := rfl
      _ = ⟪matrixMul R a, a⟫_ℝ := by rw [hmul, hinv]
      _ = ⟪a, matrixMul R a⟫_ℝ := real_inner_comm _ _
  have hsquares : (∑ i, (r (s i)) ^ 2) = ⟪a, a⟫_ℝ := by
    rw [PiLp.inner_apply]
    simp [a, pow_two]
  have hlocal :
      (∑ i, localLogMass (s i)) =
        (∑ i, Real.log (normalCDF (s i))) + ⟪a, a⟫_ℝ / 2 := by
    simp only [localLogMass, Finset.sum_add_distrib]
    rw [← Finset.sum_div]
    rw [hsquares]
  rw [adaptivePotential, hlocal, hq]
  dsimp only [a]
  ring

end

end WeakSimplex
