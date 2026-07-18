import WeakSimplexConjectureLean.Core.Euclidean
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false

noncomputable section

namespace WeakSimplex

/-- The largest coordinate of a nonempty Euclidean coordinate vector. -/
def coordinateMax {m : ℕ} (hm : 0 < m) (x : Coord m) : ℝ :=
  Finset.univ.sup'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm))
    (fun i ↦ x i)

/-- The coordinate maximum is continuous. -/
theorem continuous_coordinateMax {m : ℕ} (hm : 0 < m) :
    Continuous (coordinateMax hm) := by
  unfold coordinateMax
  exact Continuous.finset_sup'_apply _ fun i _ ↦ by fun_prop

/-- A coordinate maximum is at most `c` exactly on the lower orthant at `c`. -/
theorem coordinateMax_le_iff_mem_lowerOrthant
    {m : ℕ} (hm : 0 < m) (x : Coord m) (c : ℝ) :
    coordinateMax hm x ≤ c ↔ x ∈ lowerOrthant c := by
  rw [coordinateMax, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, forall_const, lowerOrthant, Set.mem_setOf_eq]

end WeakSimplex
