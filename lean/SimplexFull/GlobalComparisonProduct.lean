import SimplexUniquenessLean.StrictProduct

/-!
Public quantitative-assembly interface extracted from the actual PSD Q1 proof
inside StrictProduct.lean, lines 789-868, original repository
E:/claude-lean-work/simplex-uniqueness-lean, commit
54eaa804e722cf3e763c87492056b27702ac526e, MIT license.
The vendor file remains unchanged. The proof uses the proved centered product
inequality on positive-definite regularizations, continuity and boundedness of
the actual normalized self-convolutions, and the proved PSD weak limit.
-/
noncomputable section
namespace SimplexFull.GlobalComparison
open MeasureTheory Set WeakSimplex ProbabilityTheory SimplexUniqueness
open scoped ENNReal Matrix BigOperators

private theorem exists_norm_bound
    {X : Type*} {f : X → ℝ} (hf : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf
  refine ⟨C, fun x ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self x)

/-- Actual PSD centered-product lower bound for normalized self-convolutions
of centered truncated exponentials. No invertibility of S is assumed. -/
theorem normalizedSelfConvolution_product_ge_one
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsCorrelation S)
    (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (hcent : ∀ i, ∫ x, x * tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1 = 0) :
    let M : Fin m → ℝ := fun i ↦ ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1
    let h : Fin m → ℝ → ℝ := fun i x ↦ (M i)⁻¹ * tiltedHalfLine (a i) (b i) x
    1 ≤ ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
      ∂multivariateGaussian (0 : Coord m) S := by
  classical
  let M : Fin m → ℝ := fun i ↦ ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1
  have hM : ∀ i, 0 < M i := by
    intro i
    have h := integral_tiltedHalfLine (a := a i) (s := b i - a i) (ha i).le
    rw [sub_add_cancel] at h
    show 0 < ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1
    rw [h]
    exact mul_pos (Real.exp_pos _) (normalCDF_pos _)
  let h : Fin m → ℝ → ℝ := fun i x ↦ (M i)⁻¹ * tiltedHalfLine (a i) (b i) x
  have hh_meas : ∀ i, Measurable (h i) := fun i ↦
    (measurable_tiltedHalfLine _ _).const_mul _
  have hh_nonneg : ∀ i x, 0 ≤ h i x := fun i x ↦
    mul_nonneg (inv_pos.2 (hM i)).le (tiltedHalfLine_nonneg _ _ _)
  have hh_bdd : ∀ i, Bornology.IsBounded (Set.range (h i)) := fun i ↦
    Deficit.isBounded_range_const_mul (isBounded_range_tiltedHalfLine (ha i).le) _
  have hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x)) := fun i ↦
    Deficit.isLogConcave_const_mul_of_nonneg (inv_pos.2 (hM i)).le
      (isLogConcave_tiltedHalfLine _ _)
  have hh_mass : ∀ i, ∫ x, h i x ∂gaussianReal 0 1 = 1 := by
    intro i
    simp only [h]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (hM i).ne'
  have hh_bary : ∀ i, ∫ x, x * h i x ∂gaussianReal 0 1 = 0 := by
    intro i
    simp only [h]
    simp_rw [mul_left_comm _ (M i)⁻¹]
    rw [integral_const_mul, hcent i, mul_zero]
  have hDc : ∀ i, Continuous (normalizedSelfConvolution (h i)) := fun i ↦
    Deficit.continuous_normalizedSelfConvolution_tilted (a i) (b i) (M i) (ha i).le (hM i)
  have hDbdd : ∀ i, Bornology.IsBounded (Set.range (normalizedSelfConvolution (h i))) := fun i ↦
    isBounded_range_normalizedSelfConvolution (hh_nonneg i) (hh_bdd i)
  choose C hC using fun i ↦ exists_norm_bound (hDbdd i)
  -- the self-convolutions are admissible for the centered product inequality
  have hQ1pd : ∀ R : Matrix (Fin m) (Fin m) ℝ, R.PosDef → (∀ i, R i i = 1) →
      1 ≤ ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R := by
    intro R hpd hdiag
    have hc := centered_product_of_posDef R hpd hdiag (fun i ↦ normalizedSelfConvolution (h i))
      (fun i ↦ measurable_normalizedSelfConvolution (hh_meas i))
      (fun i x ↦ normalizedSelfConvolution_nonneg _ _)
      (fun i ↦ isBounded_range_normalizedSelfConvolution (hh_nonneg i) (hh_bdd i))
      (fun i ↦ isLogConcave_normalizedSelfConvolution (hh_meas i) (hh_nonneg i) (hh_bdd i)
        (hh_lc i))
      (fun i ↦ by
        rw [integral_normalizedSelfConvolution_eq_one (hh_meas i) (hh_nonneg i) (hh_bdd i)
          (hh_mass i)]
        exact one_pos)
      (fun i ↦ integral_mul_normalizedSelfConvolution_eq_zero (hh_meas i) (hh_nonneg i)
        (hh_bdd i) (hh_mass i) (hh_bary i))
    simpa [integral_normalizedSelfConvolution_eq_one (hh_meas _) (hh_nonneg _) (hh_bdd _)
      (hh_mass _)] using hc
  -- regularize `S` to positive-definite correlation matrices and pass to the limit
  have hQ1 : 1 ≤ ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
      ∂multivariateGaussian (0 : Coord m) S := by
    refine Regularize.le_integral_of_regularized S hS.1
      (fun u ↦ ∏ i, normalizedSelfConvolution (h i) (u i))
      (continuous_finsetProd _ fun i _ ↦ (hDc i).comp (EuclideanSpace.proj i).continuous)
      (∏ i, |C i|) ?_ 1 ?_
    · intro u
      rw [Real.norm_eq_abs, Finset.abs_prod]
      refine Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
      exact (hC i (u i)).trans (le_abs_self _)
    · intro n
      have hε0 : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
      have hε1 : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      refine hQ1pd _ ?_ ?_
      · exact Matrix.PosDef.posSemidef_add (hS.1.smul (by linarith))
          (Matrix.PosDef.one.smul hε0)
      · intro i
        simp [Matrix.add_apply, hS.2 i]
  exact hQ1

#print axioms normalizedSelfConvolution_product_ge_one
end SimplexFull.GlobalComparison
