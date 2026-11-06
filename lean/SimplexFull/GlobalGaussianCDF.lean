import SimplexFull.GlobalTailBounds
import SimplexFull.GlobalCentroidOrthant
import SimplexFull.GlobalFoundationBridge
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Set WeakSimplex
namespace SimplexFull.GlobalTail
variable {m : ℕ} [NeZero m]

theorem maxCoord_sublevel (c : ℝ) :
    {x : Coord m | maxCoord x ≤ c} = lowerOrthant c := by
  ext x
  rw [← GlobalFoundation.coordinateMax_eq_maxCoord (NeZero.pos m)]
  exact coordinateMax_le_iff_mem_lowerOrthant (NeZero.pos m) x c

/-- The product-law calculation follows the MIT-licensed upstream
WeakSimplexConjectureLean.Maxima.StochasticOrder identity. -/
theorem identity_orthant_mass (c : ℝ) :
    (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ))
      (lowerOrthant c) = (gaussianReal 0 1 (Iic c))^m := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]
  rw [Measure.map_apply (by fun_prop) (measurableSet_lowerOrthant c)]
  rw [show (WithLp.toLp 2) ⁻¹' lowerOrthant c =
      Set.pi Set.univ (fun _ : Fin m => Iic c) by
    ext x
    simp only [Set.mem_preimage, lowerOrthant, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Iic]]
  rw [Measure.pi_pi]
  exact Fin.prod_const m ((gaussianReal 0 1) (Iic c))

theorem identity_orthantCDF (c : ℝ) :
    GlobalCentroid.orthantCDF (1 : Matrix (Fin m) (Fin m) ℝ) c = (Phi c)^m := by
  unfold GlobalCentroid.orthantCDF
  rw [identity_orthant_mass, ← normalCDF_eq_measure_Iic, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (show 0 ≤ normalCDF c from (Phi_pos c).le)]
  rfl
  
theorem cdf_gap_eq_thresholdDeficit (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    (multivariateGaussian (0 : Coord m) R).real {x | maxCoord x ≤ c} -
      (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ)).real
        {x | maxCoord x ≤ c} = GlobalCentroid.thresholdDeficit R c := by
  rw [maxCoord_sublevel]
  change GlobalCentroid.orthantCDF R c - GlobalCentroid.orthantCDF 1 c = _
  rw [identity_orthantCDF]
  rfl

theorem maxCoord_cdf_domination (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) (c : ℝ) :
    (multivariateGaussian (0 : Coord m) (1 : Matrix (Fin m) (Fin m) ℝ)).real
        {x | maxCoord x ≤ c} ≤
      (multivariateGaussian (0 : Coord m) R).real {x | maxCoord x ≤ c} := by
  have h := GlobalCentroid.thresholdDeficit_nonneg (NeZero.pos m) hR c
  rw [← cdf_gap_eq_thresholdDeficit] at h
  exact sub_nonneg.mp h

theorem gaussianMaxMean_gap_ge_of_thresholdDeficit
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R)
    {A : ℝ} (hA : 0 ≤ A)
    (hl : ∀ c ∈ Icc (0 : ℝ) 1, A ≤ GlobalCentroid.thresholdDeficit R c) :
    A ≤ gaussianMaxMean (1 : Matrix (Fin m) (Fin m) ℝ) - gaussianMaxMean R := by
  apply gaussianMaxMean_gap_ge_of_cdf R 1 (maxCoord_cdf_domination R hR) hA
  intro c hc
  rw [cdf_gap_eq_thresholdDeficit]
  exact hl c hc

#print axioms gaussianMaxMean_gap_ge_of_thresholdDeficit
end SimplexFull.GlobalTail
