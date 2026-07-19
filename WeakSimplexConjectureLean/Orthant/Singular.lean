import WeakSimplexConjectureLean.Gaussian.Regularization
import WeakSimplexConjectureLean.Orthant.PositiveDefinite

/-!
# Singular covariance

This module obtains the lower-orthant comparison for positive-semidefinite covariance matrices by
regularizing to the positive-definite case and passing to the limit.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology

namespace WeakSimplex

private def coordinateHalfspace {m : ℕ} (i : Fin m) (c : ℝ) : Set (Coord m) :=
  (fun x ↦ x i) ⁻¹' Set.Iic c

private theorem frontier_biInter_finset_subset_biUnion_frontier
    {α X : Type*} [TopologicalSpace X]
    (A : α → Set X) (s : Finset α) :
    frontier (⋂ i ∈ s, A i) ⊆ ⋃ i ∈ s, frontier (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hstep :
          frontier (A a ∩ ⋂ i ∈ s, A i) ⊆
            frontier (A a) ∪ ⋃ i ∈ s, frontier (A i) :=
        (frontier_inter_subset (A a) (⋂ i ∈ s, A i)).trans
          (Set.union_subset
            (Set.inter_subset_left.trans Set.subset_union_left)
            (Set.inter_subset_right.trans (ih.trans Set.subset_union_right)))
      simpa [ha] using hstep

private theorem frontier_coordinateHalfspace_subset_hyperplane
    {m : ℕ} (i : Fin m) (c : ℝ) :
    frontier (coordinateHalfspace i c) ⊆ {x : Coord m | x i = c} := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.frontier_preimage_subset
    (Set.Iic c)
  rw [frontier_Iic] at h
  refine h.trans ?_
  intro x hx
  simpa [coordinateHalfspace, EuclideanSpace.coe_proj] using hx

private theorem frontier_lowerOrthant_subset_iUnion_hyperplane
    {m : ℕ} (c : ℝ) :
    frontier (lowerOrthant (m := m) c) ⊆ ⋃ i : Fin m, {x : Coord m | x i = c} := by
  have horthant :
      lowerOrthant (m := m) c = ⋂ i ∈ Finset.univ, coordinateHalfspace i c := by
    ext x
    simp [lowerOrthant, coordinateHalfspace]
  rw [horthant]
  refine (frontier_biInter_finset_subset_biUnion_frontier
    (fun i : Fin m ↦ coordinateHalfspace i c) Finset.univ).trans ?_
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨i, _, hi⟩ := hx
  exact ⟨i, frontier_coordinateHalfspace_subset_hyperplane i c hi⟩

private theorem measure_coordinateHyperplane_multivariateGaussian_eq_zero
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R)
    (i : Fin m) (c : ℝ) :
    multivariateGaussian (0 : Coord m) R {x : Coord m | x i = c} = 0 := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  have hmap := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord m)) hR.1.1 (i := i)).map_eq
  have happly := congrArg (fun μ : Measure ℝ ↦ μ {c}) hmap
  have hcoordmeas : Measurable (fun x : Coord m ↦ x i) := by fun_prop
  rw [Measure.map_apply_of_aemeasurable
    hcoordmeas.aemeasurable (measurableSet_singleton c)] at happly
  have hpre :
      multivariateGaussian (0 : Coord m) R ((fun x : Coord m ↦ x i) ⁻¹' {c}) = 0 := by
    simpa [hR.1.2 i] using happly
  rw [show {x : Coord m | x i = c} = (fun x : Coord m ↦ x i) ⁻¹' {c} by
    ext x
    simp]
  exact hpre

private theorem measure_frontier_lowerOrthant_multivariateGaussian_eq_zero
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R) (c : ℝ) :
    multivariateGaussian (0 : Coord m) R (frontier (lowerOrthant c)) = 0 := by
  apply measure_mono_null (frontier_lowerOrthant_subset_iUnion_hyperplane c)
  exact measure_iUnion_null fun i ↦
    measure_coordinateHyperplane_multivariateGaussian_eq_zero R hR i c

/-- The lower-orthant comparison for every admissible weak-simplex covariance matrix. -/
theorem lowerOrthant_ge_iid
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    (multivariateGaussian 0 R) (lowerOrthant c) ≥
      (gaussianReal 0 1) (Set.Iic c) ^ m := by
  have hconv : TendstoInDistribution (fun _ : ℕ ↦ id) atTop id
      (fun n ↦ multivariateGaussian (0 : Coord m)
        (regularizedCovariance R (regularizationEpsilon n)))
      (multivariateGaussian (0 : Coord m) R) := by
    simpa only [regularizedCovariance, regularizationEpsilon] using
      tendstoInDistribution_regularized_multivariateGaussian R hR.1.1
  have hmeasure : Tendsto
      (fun n ↦ (multivariateGaussian (0 : Coord m)
        (regularizedCovariance R (regularizationEpsilon n))) (lowerOrthant c))
      atTop (𝓝 ((multivariateGaussian (0 : Coord m) R) (lowerOrthant c))) := by
    have hfrontier :
        (Measure.map id (multivariateGaussian (0 : Coord m) R))
          (frontier (lowerOrthant c)) = 0 := by
      simpa using measure_frontier_lowerOrthant_multivariateGaussian_eq_zero R hR c
    have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (E := lowerOrthant c) hconv.tendsto hfrontier
    simpa using ht
  apply ge_of_tendsto hmeasure
  filter_upwards [] with n
  have hε0 := regularizationEpsilon_pos n
  have hε1 := (regularizationEpsilon_lt_one n).le
  exact lowerOrthant_ge_iid_of_posDef hm
    (regularizedCovariance R (regularizationEpsilon n))
    (regularizedCovariance_isWeakSimplexCov hm R hR hε0 hε1)
    (regularizedCovariance_posDef R hR.1.1 hε0 hε1) c

end WeakSimplex
