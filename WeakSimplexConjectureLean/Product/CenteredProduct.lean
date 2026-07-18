import WeakSimplexConjectureLean.Product.PositiveLowerBound
import WeakSimplexConjectureLean.Product.CenteredProperty
import WeakSimplexConjectureLean.Product.SumDifference

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace WeakSimplex

private theorem isBounded_range_const_mul_wp17
    {f : ℝ → ℝ} (hf : Bornology.IsBounded (Set.range f)) (a : ℝ) :
    Bornology.IsBounded (Set.range (fun x ↦ a * f x)) := by
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖a‖ * C, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC _ (Set.mem_range_self x)) (norm_nonneg a)

private theorem isLogConcave_const_mul_of_nonneg_wp17
    {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : IsLogConcave (fun x ↦ ENNReal.ofReal (f x))) :
    IsLogConcave (fun x ↦ ENNReal.ofReal (a * f x)) := by
  have h := (isLogConcave_const (E := ℝ) (ENNReal.ofReal a)).mul hf
  convert h using 1
  funext x
  exact ENNReal.ofReal_mul ha

private theorem iterated_product_integral_nonneg
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (h : Fin m → ℝ → ℝ)
    (hh_nonneg : ∀ i x, 0 ≤ h i x) (r : ℕ) :
    0 ≤ ∫ x, ∏ i, iteratedNormalizedSelfConvolution (h i) r (x i)
      ∂multivariateGaussian (0 : Coord m) R := by
  apply integral_nonneg
  intro x
  exact Finset.prod_nonneg fun i _ ↦
    iteratedNormalizedSelfConvolution_nonneg (hh_nonneg i) r (x i)

private theorem iterated_product_integral_le_dyadic_pow
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x))) (r : ℕ) :
    (∫ x, ∏ i, iteratedNormalizedSelfConvolution (h i) r (x i)
        ∂multivariateGaussian (0 : Coord m) R) ≤
      (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R) ^ (2 ^ r) := by
  let Z : ℕ → ℝ := fun s ↦
    ∫ x, ∏ i, iteratedNormalizedSelfConvolution (h i) s (x i)
      ∂multivariateGaussian (0 : Coord m) R
  have hZ_nonneg (s : ℕ) : 0 ≤ Z s := by
    exact iterated_product_integral_nonneg R h hh_nonneg s
  have hstep (s : ℕ) : Z (s + 1) ≤ Z s ^ 2 := by
    simpa only [Z, iteratedNormalizedSelfConvolution] using
      normalizedSelfConvolution_product_deficit_of_posDef R hR hdiag
        (fun i ↦ iteratedNormalizedSelfConvolution (h i) s)
        (fun i ↦ measurable_iteratedNormalizedSelfConvolution (hh_meas i) s)
        (fun i x ↦ iteratedNormalizedSelfConvolution_nonneg (hh_nonneg i) s x)
        (fun i ↦ isBounded_range_iteratedNormalizedSelfConvolution
          (hh_nonneg i) (hh_bounded i) s)
        (fun i ↦ isLogConcave_iteratedNormalizedSelfConvolution
          (hh_meas i) (hh_nonneg i) (hh_bounded i) (hh_lc i) s)
  change Z r ≤ Z 0 ^ (2 ^ r)
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        Z (r + 1) ≤ Z r ^ 2 := hstep r
        _ ≤ (Z 0 ^ (2 ^ r)) ^ 2 :=
          (sq_le_sq₀ (hZ_nonneg r) (pow_nonneg (hZ_nonneg 0) _)).2 ih
        _ = Z 0 ^ (2 ^ (r + 1)) := by rw [← pow_mul, pow_succ]

private theorem one_le_normalized_product_integral
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x)))
    (hh_mass : ∀ i, ∫ x, h i x ∂gaussianReal 0 1 = 1)
    (hh_barycenter : ∀ i, ∫ x, x * h i x ∂gaussianReal 0 1 = 0) :
    1 ≤ ∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R := by
  let Z : ℕ → ℝ := fun r ↦
    ∫ x, ∏ i, iteratedNormalizedSelfConvolution (h i) r (x i)
      ∂multivariateGaussian (0 : Coord m) R
  have hZ_nonneg (r : ℕ) : 0 ≤ Z r := by
    exact iterated_product_integral_nonneg R h hh_nonneg r
  have hupper (r : ℕ) : Z r ≤ Z 0 ^ (2 ^ r) := by
    exact iterated_product_integral_le_dyadic_pow R hR hdiag h hh_meas hh_nonneg
      hh_bounded hh_lc r
  obtain ⟨c, hc, hc_eventually⟩ :=
    exists_eventual_pos_lower_bound_integral_iteratedNormalizedSelfConvolution
      R hR h hh_meas hh_nonneg hh_bounded hh_mass hh_barycenter
  change 1 ≤ Z 0
  by_contra hnot
  have hlt : Z 0 < 1 := lt_of_not_ge hnot
  have hpow : Tendsto (fun r : ℕ ↦ Z 0 ^ (2 ^ r)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hZ_nonneg 0) hlt).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hpow_lt : ∀ᶠ r : ℕ in atTop, Z 0 ^ (2 ^ r) < c :=
    hpow.eventually (Iio_mem_nhds hc)
  obtain ⟨r, hcr, hr⟩ := (hc_eventually.and hpow_lt).exists
  exact (not_lt_of_ge (hcr.trans (hupper r))) hr

/-- The centered product inequality for every positive-definite correlation matrix. -/
theorem centered_product_of_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (hdiag : ∀ i, R i i = 1) :
    CenteredProductProperty R := by
  classical
  intro f hf_meas hf_nonneg hf_bounded hf_lc hf_mass_pos hf_barycenter
  let mass : Fin m → ℝ := fun i ↦ ∫ x, f i x ∂gaussianReal 0 1
  let h : Fin m → ℝ → ℝ := fun i x ↦ (mass i)⁻¹ * f i x
  have hmass_pos (i : Fin m) : 0 < mass i := hf_mass_pos i
  have hmass_ne (i : Fin m) : mass i ≠ 0 := (hmass_pos i).ne'
  have hh_meas : ∀ i, Measurable (h i) := fun i ↦ by
    exact (hf_meas i).const_mul (mass i)⁻¹
  have hh_nonneg : ∀ i x, 0 ≤ h i x := fun i x ↦ by
    exact mul_nonneg (inv_nonneg.mpr (hmass_pos i).le) (hf_nonneg i x)
  have hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)) := fun i ↦ by
    exact isBounded_range_const_mul_wp17 (hf_bounded i) (mass i)⁻¹
  have hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x)) := fun i ↦ by
    exact isLogConcave_const_mul_of_nonneg_wp17
      (inv_nonneg.mpr (hmass_pos i).le) (hf_lc i)
  have hh_mass : ∀ i, ∫ x, h i x ∂gaussianReal 0 1 = 1 := fun i ↦ by
    rw [show (fun x ↦ h i x) = fun x ↦ (mass i)⁻¹ * f i x by rfl, integral_const_mul]
    exact inv_mul_cancel₀ (hmass_ne i)
  have hh_barycenter : ∀ i, ∫ x, x * h i x ∂gaussianReal 0 1 = 0 := fun i ↦ by
    calc
      (∫ x, x * h i x ∂gaussianReal 0 1) =
          ∫ x, (mass i)⁻¹ * (x * f i x) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [h]
        ring
      _ = (mass i)⁻¹ * ∫ x, x * f i x ∂gaussianReal 0 1 := by
        rw [integral_const_mul]
      _ = 0 := by rw [hf_barycenter i, mul_zero]
  have hone : 1 ≤ ∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R :=
    one_le_normalized_product_integral R hR hdiag h hh_meas hh_nonneg hh_bounded
      hh_lc hh_mass hh_barycenter
  have hprod_mass_pos : 0 < ∏ i, mass i := Finset.prod_pos fun i _ ↦ hmass_pos i
  calc
    (∏ i, ∫ x, f i x ∂gaussianReal 0 1) = ∏ i, mass i := rfl
    _ = (∏ i, mass i) * 1 := by rw [mul_one]
    _ ≤ (∏ i, mass i) *
        (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R) :=
      mul_le_mul_of_nonneg_left hone hprod_mass_pos.le
    _ = ∫ x, ∏ i, f i (x i) ∂multivariateGaussian (0 : Coord m) R := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [h]
      rw [← mul_assoc, mul_inv_cancel₀ (hmass_ne i), one_mul]

end WeakSimplex
