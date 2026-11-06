import SimplexFull.GlobalMeanWidthGeometry
noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]

theorem normalizedGaussianWidth_deficit {d : ℕ} (X V : Config m d) :
    normalizedGaussianWidth V-normalizedGaussianWidth X =
      (2 / gaussianRadiusMean d) * (configGaussianMax V-configGaussianMax X) := by
  unfold normalizedGaussianWidth
  ring

/-- Normalized Gaussian-width bounds transferred from the explicitly stated
unit Gaussian comparison to an actual ball configuration and actual reference.
The common radial expectation belongs to their original ambient dimension. -/
theorem ball_normalized_width_bounds_of_unit {d : ℕ} (hd : 1 ≤ d)
    {bg bs : ℝ} (hunit : UnitGaussianMaxBounds m bg bs)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    (2 / gaussianRadiusMean d) * bg *
        frobSq (gram (orthogonalUnitLift X)-simplexGram m) ≤
          normalizedGaussianWidth V-normalizedGaussianWidth X ∧
    (2 / gaussianRadiusMean d) * bs *
        (‖∑ i, X i‖^2 + ∑ i, energyDeficit X i) ≤
          normalizedGaussianWidth V-normalizedGaussianWidth X := by
  obtain ⟨hg,hs⟩ := ball_gaussian_max_bounds_of_unit hunit X V hX hV
  have hscale : 0 ≤ 2 / gaussianRadiusMean d :=
    div_nonneg (by norm_num) (gaussianRadiusMean_pos hd).le
  rw [normalizedGaussianWidth_deficit]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg hscale
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hscale

theorem ball_normalized_width_procrustes_of_unit {d : ℕ}
    (hm : 2 ≤ m) (hd : 1 ≤ d)
    {bg bs : ℝ} (hbg : 0 < bg) (hbs : 0 < bs)
    (hunit : UnitGaussianMaxBounds m bg bs)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    (2 / gaussianRadiusMean d) * (alpha m / bg + 1 / bs)⁻¹ *
        procrustesSq X V ≤ normalizedGaussianWidth V-normalizedGaussianWidth X := by
  have h := ball_gaussian_max_procrustes_of_unit hm hbg hbs hunit X V hX hV
  have hscale : 0 ≤ 2 / gaussianRadiusMean d :=
    div_nonneg (by norm_num) (gaussianRadiusMean_pos hd).le
  rw [normalizedGaussianWidth_deficit]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hscale

theorem ball_normalized_width_unused_energy_of_unit {d : ℕ}
    (hd : 1 ≤ d) {bg bs : ℝ} (hbs : 0 ≤ bs)
    (hunit : UnitGaussianMaxBounds m bg bs)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    (2 / gaussianRadiusMean d) * bs * (∑ i, (1-‖X i‖^2)) ≤
      normalizedGaussianWidth V-normalizedGaussianWidth X := by
  have h := (ball_normalized_width_bounds_of_unit hd hunit X V hX hV).2
  have hs : 0 ≤ (2 / gaussianRadiusMean d) * bs :=
    mul_nonneg (div_nonneg (by norm_num) (gaussianRadiusMean_pos hd).le) hbs
  have hc := mul_nonneg hs (sq_nonneg ‖∑ i, X i‖)
  simp only [energyDeficit] at h
  nlinarith

/-- The original m>=2, d>=m-1 mean-width geometry and unused-energy conclusions.
This is intentionally marked as a transfer theorem: hunit must be discharged by
the actual global Gaussian/CDF comparison before claiming the full theorem. -/
theorem ball_mean_width_of_unit_bounds {d : ℕ}
    (hm : 2 ≤ m) (hd : m-1 ≤ d)
    {bg bs : ℝ} (hbg : 0 < bg) (hbs : 0 < bs)
    (hunit : UnitGaussianMaxBounds m bg bs)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    (2 / gaussianRadiusMean d) * (alpha m / bg + 1 / bs)⁻¹ *
        procrustesSq X V ≤ normalizedGaussianWidth V-normalizedGaussianWidth X ∧
    (2 / gaussianRadiusMean d) * bs * (∑ i, (1-‖X i‖^2)) ≤
        normalizedGaussianWidth V-normalizedGaussianWidth X := by
  have hd1 : 1 ≤ d := by omega
  exact ⟨ball_normalized_width_procrustes_of_unit hm hd1 hbg hbs hunit X V hX hV,
    ball_normalized_width_unused_energy_of_unit hd1 hbs.le hunit X V hX hV⟩

#print axioms ball_normalized_width_bounds_of_unit
#print axioms ball_normalized_width_procrustes_of_unit
#print axioms ball_normalized_width_unused_energy_of_unit
#print axioms ball_mean_width_of_unit_bounds
end SimplexFull.Geometry
