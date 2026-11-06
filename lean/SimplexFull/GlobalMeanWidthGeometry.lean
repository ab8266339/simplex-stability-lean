import SimplexFull.GlobalMeanWidthLift
import SimplexFull.GlobalMeanWidthNoise
noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull.Geometry

theorem energyDeficit_sq_sum_le {m d : ℕ} (X : Config m d) (hX : BallConfig X) :
    (∑ i, (energyDeficit X i)^2) ≤ ∑ i, energyDeficit X i := by
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨h0,h1⟩ := energyDeficit_bounds X hX i
  nlinarith

theorem global_procrustesSq_le_lift_errors {m d : ℕ} (hm : 2 ≤ m)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    procrustesSq X V ≤
      alpha m * frobSq (gram (orthogonalUnitLift X)-simplexGram m) +
        ‖∑ i, orthogonalUnitLift X i‖^2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have ha0 : 0 ≤ alpha m := alpha_nonneg (by omega)
  have ha1 : alpha m ≤ 1 := by
    rw [alpha_eq_one_sub_inv m (by omega)]
    have h := inv_nonneg.mpr hmR.le
    linarith
  have hs0 : 0 ≤ ∑ i, energyDeficit X i :=
    Finset.sum_nonneg (fun i _ => (energyDeficit_bounds X hX i).1)
  have he : alpha m * (∑ i, (energyDeficit X i)^2) ≤ ∑ i, energyDeficit X i := by
    have h1 := mul_le_mul_of_nonneg_left (energyDeficit_sq_sum_le X hX) ha0
    have h2 := mul_le_mul_of_nonneg_right ha1 hs0
    simpa using h1.trans h2
  have hc : ‖∑ i, X i‖^2 / (m : ℝ) ≤ ‖∑ i, X i‖^2 := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith [sq_nonneg ‖∑ i, X i‖]
  have hg := global_procrustesSq_le_gram_centroid hm X V hV
  rw [frobSq_gram_lift_identity hm X hX] at hg
  rw [centroid_sq_orthogonalUnitLift X hX]
  nlinarith

variable {m : ℕ} [NeZero m]

theorem configGaussianMax_le_orthogonalUnitLift {d : ℕ}
    (X : Config m d) (hX : BallConfig X) :
    configGaussianMax X ≤ configGaussianMax (orthogonalUnitLift X) := by
  have hn : (Matrix.diagonal (energyDeficit X)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact (energyDeficit_bounds X hX i).1
  unfold configGaussianMax
  rw [gram_orthogonalUnitLift X hX]
  exact gaussianMaxMean_le_add (gram X) _ (gram_posSemidef X) hn

/-- Explicit modular interface to the unit-covariance quantitative Gaussian
comparison. This predicate is discharged by the independent CDF/integral chain,
not assumed as a completed global theorem by this module. -/
def UnitGaussianMaxBounds (m : ℕ) [NeZero m] (bg bs : ℝ) : Prop :=
  ∀ G : Matrix (Fin m) (Fin m) ℝ, G.PosSemidef → (∀ i, G i i = 1) →
    bg * frobSq (G-simplexGram m) ≤ gaussianMaxMean (simplexGram m)-gaussianMaxMean G ∧
    bs * entrySum G ≤ gaussianMaxMean (simplexGram m)-gaussianMaxMean G

/-- Transfer of actual unit-covariance bounds to arbitrary configurations in
the unit ball, using the concrete orthogonal-coordinate lift. -/
theorem ball_gaussian_max_bounds_of_unit {d : ℕ} {bg bs : ℝ}
    (hunit : UnitGaussianMaxBounds m bg bs)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    bg * frobSq (gram (orthogonalUnitLift X)-simplexGram m) ≤
        configGaussianMax V-configGaussianMax X ∧
    bs * (‖∑ i, X i‖^2 + ∑ i, energyDeficit X i) ≤
        configGaussianMax V-configGaussianMax X := by
  have hu := hunit (gram (orthogonalUnitLift X)) (gram_posSemidef _)
    (gram_diagonal_unit _ (unitConfig_orthogonalUnitLift X hX))
  have hm := configGaussianMax_le_orthogonalUnitLift X hX
  have hv : configGaussianMax V = gaussianMaxMean (simplexGram m) := by
    simp only [configGaussianMax, hV]
  have hl : gaussianMaxMean (gram (orthogonalUnitLift X)) = configGaussianMax (orthogonalUnitLift X) := rfl
  rw [global_entrySum_gram, centroid_sq_orthogonalUnitLift X hX] at hu
  rw [← hv, hl] at hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- Harmonic combination for the actual configuration distance. The only
remaining modular input is explicitly the unit Gaussian comparison. -/
theorem ball_gaussian_max_procrustes_of_unit {d : ℕ} (hm : 2 ≤ m)
    {bg bs : ℝ} (hbg : 0 < bg) (hbs : 0 < bs)
    (hunit : UnitGaussianMaxBounds m bg bs)
    (X V : Config m d) (hX : BallConfig X) (hV : gram V = simplexGram m) :
    (alpha m / bg + 1 / bs)⁻¹ * procrustesSq X V ≤
      configGaussianMax V-configGaussianMax X := by
  have ha : 0 ≤ alpha m := alpha_nonneg (by omega)
  have hden : 0 < alpha m / bg + 1 / bs :=
    add_pos_of_nonneg_of_pos (div_nonneg ha hbg.le) (one_div_pos.mpr hbs)
  obtain ⟨hg,hs⟩ := ball_gaussian_max_bounds_of_unit hunit X V hX hV
  have hgp := (le_div_iff₀ hbg).mpr (by simpa [mul_comm] using hg)
  have hsp := (le_div_iff₀ hbs).mpr (by simpa [mul_comm] using hs)
  have hgeom := global_procrustesSq_le_lift_errors hm X V hX hV
  rw [centroid_sq_orthogonalUnitLift X hX] at hgeom
  have hcomb : procrustesSq X V ≤
      (alpha m / bg + 1 / bs) * (configGaussianMax V-configGaussianMax X) := by
    have hmul := mul_le_mul_of_nonneg_left hgp ha
    calc
      procrustesSq X V ≤
          alpha m * frobSq (gram (orthogonalUnitLift X)-simplexGram m) +
            (‖∑ i, X i‖^2 + ∑ i, energyDeficit X i) := hgeom
      _ ≤ alpha m * ((configGaussianMax V-configGaussianMax X)/bg) +
          (configGaussianMax V-configGaussianMax X)/bs := add_le_add hmul hsp
      _ = (alpha m / bg + 1 / bs) * (configGaussianMax V-configGaussianMax X) := by ring
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hcomb)

#print axioms global_procrustesSq_le_lift_errors
#print axioms configGaussianMax_le_orthogonalUnitLift
#print axioms ball_gaussian_max_bounds_of_unit
#print axioms ball_gaussian_max_procrustes_of_unit
end SimplexFull.Geometry
