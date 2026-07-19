import WeakSimplexConjectureLean.Core.Correlation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

/-!
# Gram normalization and the regular simplex

This module supplies the matrix normalization that connects correlation matrices to admissible
weak-simplex covariances and identifies the regular simplex with the identity covariance.
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

namespace WeakSimplex

private def normalizationScale (m : ℕ) : ℝ :=
  ((m : ℝ) - 1) / (m : ℝ)

private def normalizedCovariance {m : ℕ}
    (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  normalizationScale m • G + (1 / (m : ℝ)) • allOnesMatrix m

/-- The Gram matrix of a regular simplex with `m` unit vertices. -/
def regularSimplexGram (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ((m : ℝ) / ((m : ℝ) - 1)) •
    ((1 : Matrix (Fin m) (Fin m) ℝ) -
      (1 / (m : ℝ)) • allOnesMatrix m)

private theorem natCast_pos_of_one_lt {m : ℕ} (hm : 1 < m) : 0 < (m : ℝ) := by
  exact_mod_cast (Nat.zero_lt_of_lt hm)

private theorem natCast_sub_one_pos {m : ℕ} (hm : 1 < m) : 0 < (m : ℝ) - 1 := by
  have hmR : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  linarith

private theorem normalizationScale_pos {m : ℕ} (hm : 1 < m) :
    0 < normalizationScale m := by
  exact div_pos (natCast_sub_one_pos hm) (natCast_pos_of_one_lt hm)

private theorem centeredIdentity_posSemidef {m : ℕ} (hm : 0 < m) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) -
      (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub Matrix.isHermitian_one ?_
    apply Matrix.IsHermitian.smul
    · ext i j
      simp [allOnesMatrix]
    · simp
  · intro x
    have hrewrite :
        star x ⬝ᵥ (((1 : Matrix (Fin m) (Fin m) ℝ) -
          (1 / (m : ℝ)) • allOnesMatrix m).mulVec x) =
          (∑ i, x i ^ 2) - (1 / (m : ℝ)) * (∑ i, x i) ^ 2 := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply]
      calc
        (∑ i, x i * ∑ j,
          ((if i = j then 1 else 0) - (1 / (m : ℝ)) * 1) * x j) =
            ∑ i, x i * (x i - (1 / (m : ℝ)) * ∑ j, x j) := by
              apply Finset.sum_congr rfl
              intro i _
              congr 1
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
              simp only [mul_one]
              rw [show (∑ j, (if i = j then 1 else 0) * x j) = x i by simp]
              rw [← Finset.mul_sum]
        _ = (∑ i, x i ^ 2) - (1 / (m : ℝ)) * (∑ i, x i) ^ 2 := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              congr 1
              · simp only [pow_two]
              · rw [← Finset.sum_mul]
                ring
    rw [hrewrite]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hcs : (∑ i, x i) ^ 2 ≤ (m : ℝ) * ∑ i, x i ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
    have hdiv : (∑ i, x i) ^ 2 / (m : ℝ) ≤ ∑ i, x i ^ 2 :=
      (div_le_iff₀ hmR).2 (by simpa [mul_comm] using hcs)
    rw [sub_nonneg]
    simpa [div_eq_inv_mul, mul_comm] using hdiv

private theorem allOnesMatrix_posSemidef (m : ℕ) :
    (allOnesMatrix m).PosSemidef := by
  have heq : allOnesMatrix m =
      Matrix.vecMulVec (fun _ : Fin m ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
    ext i j
    simp [allOnesMatrix, Matrix.vecMulVec_apply]
  rw [heq]
  exact Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin m ↦ (1 : ℝ))

private theorem normalizedCovariance_isWeakSimplexCov
    {m : ℕ} (hm : 1 < m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G) : IsWeakSimplexCov (normalizedCovariance G) := by
  have hscale : 0 ≤ normalizationScale m := (normalizationScale_pos hm).le
  refine ⟨⟨(hG.1.smul hscale).add
      ((allOnesMatrix_posSemidef m).smul (by positivity)), ?_⟩, ?_⟩
  · intro i
    simp [normalizedCovariance, normalizationScale, hG.2 i]
    field_simp
    ring
  · have heq :
        normalizedCovariance G - (1 / (m : ℝ)) • allOnesMatrix m =
          normalizationScale m • G := by
      ext i j
      simp [normalizedCovariance]
    rw [heq]
    exact hG.1.smul hscale

private theorem regularSimplexGram_posSemidef {m : ℕ} (hm : 1 < m) :
    (regularSimplexGram m).PosSemidef := by
  exact (centeredIdentity_posSemidef (Nat.zero_lt_of_lt hm)).smul
    (div_nonneg (Nat.cast_nonneg m) (natCast_sub_one_pos hm).le)

private theorem regularSimplexGram_diagonal {m : ℕ} (hm : 1 < m) (i : Fin m) :
    regularSimplexGram m i i = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (natCast_pos_of_one_lt hm)
  have hm1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (natCast_sub_one_pos hm)
  simp [regularSimplexGram]
  field_simp

private theorem regularSimplexGram_isCorrelation {m : ℕ} (hm : 1 < m) :
    IsCorrelation (regularSimplexGram m) := by
  exact ⟨regularSimplexGram_posSemidef hm, regularSimplexGram_diagonal hm⟩

private theorem regularSimplex_normalizedCov_eq_one {m : ℕ} (hm : 1 < m) :
    normalizedCovariance (regularSimplexGram m) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (natCast_pos_of_one_lt hm)
  have hm1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (natCast_sub_one_pos hm)
  ext i j
  simp [normalizedCovariance, normalizationScale, regularSimplexGram]
  field_simp
  ring

/-- The normalized covariance is admissible, and the regular simplex normalizes to identity. -/
theorem gramNormalization
    {m : ℕ} (hm : 1 < m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : IsCorrelation G) :
    IsWeakSimplexCov
        ((((m : ℝ) - 1) / (m : ℝ)) • G +
          (1 / (m : ℝ)) • allOnesMatrix m) ∧
      IsCorrelation (regularSimplexGram m) ∧
      (((m : ℝ) - 1) / (m : ℝ)) • regularSimplexGram m +
          (1 / (m : ℝ)) • allOnesMatrix m =
        (1 : Matrix (Fin m) (Fin m) ℝ) := by
  change IsWeakSimplexCov (normalizedCovariance G) ∧
    IsCorrelation (regularSimplexGram m) ∧
      normalizedCovariance (regularSimplexGram m) = 1
  exact ⟨normalizedCovariance_isWeakSimplexCov hm G hG,
    regularSimplexGram_isCorrelation hm, regularSimplex_normalizedCov_eq_one hm⟩

/-- The normalization equals identity exactly at the regular-simplex Gram matrix. -/
theorem gramNormalization_eq_one_iff
    {m : ℕ} (hm : 1 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) :
    ((((m : ℝ) - 1) / (m : ℝ)) • G +
        (1 / (m : ℝ)) • allOnesMatrix m =
      (1 : Matrix (Fin m) (Fin m) ℝ)) ↔
      G = regularSimplexGram m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have hmR : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  constructor
  · intro hnormalization
    ext i j
    have hij := congr_fun (congr_fun hnormalization i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
      Matrix.one_apply] at hij
    simp only [regularSimplexGram, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      allOnesMatrix_apply, smul_eq_mul]
    field_simp at hij ⊢
    linarith
  · rintro rfl
    ext i j
    simp only [regularSimplexGram, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, allOnesMatrix_apply, smul_eq_mul]
    field_simp
    ring

end WeakSimplex
