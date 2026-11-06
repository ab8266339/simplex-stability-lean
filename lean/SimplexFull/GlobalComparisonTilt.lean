import SimplexFull.GlobalComparisonBox
noncomputable section
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators
namespace SimplexFull.GlobalComparison
open Rotation

/-- Quantitative doubling for actual normalized truncated exponential factors. -/
theorem tilt_doubling_lower {m : ℕ} (hm : 2 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R) (hne : R ≠ 1)
    (a b M : Fin m → ℝ) {A beta B : ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hM : ∀ i, 0 < M i) (hM1 : ∀ i, M i ≤ 1)
    (hb : 0 < beta) (hlo : ∀ i, beta ≤ b i) (hhi : ∀ i, b i ≤ B) :
    Real.exp (-(m : ℝ)*A*beta) *
      GlobalRectangle.rectangleK m (beta/Real.sqrt 2) (Real.sqrt 2*B+beta/Real.sqrt 2) *
      (centralMass (beta/Real.sqrt 2))^m * covarianceDefect R ≤
    (∫ x, ∏ i, normalizedTilt (a i) (b i) (M i) (x i)
      ∂multivariateGaussian (0 : Coord m) R)^2 -
    (∫ u, ∏ i, normalizedSelfConvolution (normalizedTilt (a i) (b i) (M i)) (u i)
      ∂multivariateGaussian (0 : Coord m) R) := by
  classical
  let ell := beta/Real.sqrt 2
  let T := Real.sqrt 2*B+ell
  let E := symmetricRectangle (fun _ : Fin m => ell)
  let k := GlobalRectangle.rectangleK m ell T
  let e := Real.exp (-(m : ℝ)*A*beta)
  let H := fun i => normalizedTilt (a i) (b i) (M i)
  have hell : 0 < ell := div_pos hb (Real.sqrt_pos.mpr (by norm_num))
  have hk : 0 ≤ k := (GlobalRectangle.rectangleK_pos hm hell).le
  have hd : 0 ≤ covarianceDefect R :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hgap : ∀ u, E.indicator (fun _ => e*k*covarianceDefect R) u ≤
      (∫ v, ∏ i, fixedAverageFactor (H i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) R) -
      ∏ i, normalizedSelfConvolution (H i) (u i) := by
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu]
      change e*k*covarianceDefect R ≤ _
      rw [tilt_gap_formula R a b M ha hM u]
      obtain ⟨hrlo,hrhi⟩ := fixed_radii_bounds b hlo hhi u hu
      have hr := GlobalRectangle.symmetricRectangle_gap hm R hR.1 hR.2
        (fun i => Real.sqrt 2*b i-u i) hell hrlo hrhi
      have hw := tilt_weights_lower a M ha haA hM hM1 hb u hu
      have hprod0 : 0 ≤ ∏ i, (M i)⁻¹^2*Real.exp (Real.sqrt 2*a i*u i) :=
        Finset.prod_nonneg fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
      calc
        e*k*covarianceDefect R = e*(k*covarianceDefect R) := by ring
        _ ≤ (∏ i, (M i)⁻¹^2*Real.exp (Real.sqrt 2*a i*u i))*
            (k*covarianceDefect R) := mul_le_mul_of_nonneg_right hw (mul_nonneg hk hd)
        _ ≤ _ := mul_le_mul_of_nonneg_left hr hprod0
    · rw [Set.indicator_of_notMem hu]
      exact tilt_gap_nonneg R hR hne a b M ha hM u
  have hmain := doubling_lower_of_indicator R H
    (fun i => normalizedTilt_measurable _ _ _)
    (fun i => normalizedTilt_nonneg (hM i))
    (fun i => normalizedTilt_bounded (ha i))
    E (measurableSet_symmetricRectangle _) (e*k*covarianceDefect R) hgap
  have hmass := central_box_mass_lower hm R hR hell
  have hmul := mul_le_mul_of_nonneg_right hmass (mul_nonneg (mul_nonneg he hk) hd)
  calc
    _ = (centralMass ell)^m*(e*k*covarianceDefect R) := by dsimp [ell,k,e,T]; ring
    _ ≤ _ := hmul
    _ ≤ _ := hmain

#print axioms tilt_doubling_lower
end SimplexFull.GlobalComparison
