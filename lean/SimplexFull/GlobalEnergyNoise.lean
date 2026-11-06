import SimplexFull.GlobalEnergyBase
noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull
variable {m : ℕ} [NeZero m]

theorem energyLikelihood_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (lam : ℝ) (i : Fin m) (x y : EuclideanSpace ℝ (Fin m)) :
    energyLikelihood (G+H) lam i (x+y) =
      energyLikelihood G lam i x * energyLikelihood H lam i y := by
  unfold energyLikelihood
  rw [← Real.exp_add]
  simp only [PiLp.add_apply, Matrix.add_apply]
  congr 1
  ring

theorem integrable_energyLikelihood_const_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.PosSemidef) (lam : ℝ) (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y => energyLikelihood (G+H) lam i (x+y)) (multivariateGaussian 0 H) := by
  simp_rw [energyLikelihood_add]
  exact (integrable_energyLikelihood H hH lam i).const_mul _

theorem integral_energyLikelihood_const_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.PosSemidef) (lam : ℝ) (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    (∫ y, energyLikelihood (G+H) lam i (x+y) ∂multivariateGaussian 0 H) =
      energyLikelihood G lam i x := by
  simp_rw [energyLikelihood_add]
  rw [integral_const_mul, integral_energyLikelihood_eq_one H hH lam i, mul_one]

theorem integrable_energyLikelihoodMax_const_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.PosSemidef) (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y => energyLikelihoodMax (G+H) lam (x+y)) (multivariateGaussian 0 H) := by
  have hs : Integrable (fun y => ∑ i, energyLikelihood (G+H) lam i (x+y))
      (multivariateGaussian 0 H) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_energyLikelihood_const_add G H hH lam i x)
  apply hs.mono_nonneg
  · exact ((measurable_energyLikelihoodMax (G+H) lam).comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun y => energyLikelihoodMax_nonneg (G+H) lam (x+y))
  · apply ae_of_all
    intro y
    exact Finset.sup'_le univNonempty _ (fun i hi =>
      Finset.single_le_sum (fun j _ =>
        (show 0 ≤ energyLikelihood (G+H) lam j (x+y) from Real.exp_nonneg _)) hi)

/-- Finite-max Jensen at the genuine nonunit likelihood level. Each added
Gaussian likelihood factor is normalized to integral one. -/
theorem energyLikelihoodMax_le_integral_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.PosSemidef) (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    energyLikelihoodMax G lam x ≤
      ∫ y, energyLikelihoodMax (G+H) lam (x+y) ∂multivariateGaussian 0 H := by
  obtain ⟨i,hi,hx⟩ := Finset.exists_mem_eq_sup' univNonempty
    (fun i => energyLikelihood G lam i x)
  have hmax : energyLikelihoodMax G lam x = energyLikelihood G lam i x := hx
  rw [hmax, ← integral_energyLikelihood_const_add G H hH lam i x]
  apply integral_mono (integrable_energyLikelihood_const_add G H hH lam i x)
    (integrable_energyLikelihoodMax_const_add G H hH lam x)
  intro y
  exact Finset.le_sup' (fun j => energyLikelihood (G+H) lam j (x+y)) (Finset.mem_univ i)

theorem integrable_energyLikelihoodMax_add_prod (G H : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (hH : H.PosSemidef) (lam : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      energyLikelihoodMax (G+H) lam (p.1+p.2))
      ((multivariateGaussian 0 G).prod (multivariateGaussian 0 H)) := by
  have hp : MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => p.1+p.2)
      ((multivariateGaussian 0 G).prod (multivariateGaussian 0 H))
      (multivariateGaussian 0 (G+H)) :=
    ⟨by fun_prop, map_add_eq_multivariateGaussian G H hG hH⟩
  exact hp.integrable_comp_of_integrable (integrable_energyLikelihoodMax (G+H) (hG.add hH) lam)

/-- Adding independent signal coordinates increases the actual nonunit Bayes
value. This is proved from the likelihood integral, not a data-processing axiom. -/
theorem gaussianBayesValue_le_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (hH : H.PosSemidef) (lam : ℝ) :
    gaussianBayesValue G lam ≤ gaussianBayesValue (G+H) lam := by
  have hp := integrable_energyLikelihoodMax_add_prod G H hG hH lam
  have hiter : (∫ z, energyLikelihoodMax (G+H) lam z ∂multivariateGaussian 0 (G+H)) =
      ∫ x, ∫ y, energyLikelihoodMax (G+H) lam (x+y)
        ∂multivariateGaussian 0 H ∂multivariateGaussian 0 G := by
    rw [← map_add_eq_multivariateGaussian G H hG hH,
      integral_map (by fun_prop) (measurable_energyLikelihoodMax (G+H) lam).aestronglyMeasurable]
    exact integral_prod _ hp
  unfold gaussianBayesValue
  rw [hiter]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (integrable_energyLikelihoodMax G hG lam) hp.integral_prod_left
  exact energyLikelihoodMax_le_integral_add G H hH lam

namespace Geometry

theorem bayesValue_le_orthogonalUnitLift {d : ℕ} (hm : 0 < m)
    (X : Config m d) (hX : BallConfig X) (lam : ℝ) :
    WeakSimplex.bayesValue hm X lam ≤ WeakSimplex.bayesValue hm (orthogonalUnitLift X) lam := by
  have hH : (Matrix.diagonal (energyDeficit X)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => (energyDeficit_bounds X hX i).1)
  rw [bayesValue_eq_gaussianBayesValue, bayesValue_eq_gaussianBayesValue,
    gram_orthogonalUnitLift X hX]
  exact gaussianBayesValue_le_add (gram X) _ (gram_posSemidef X) hH lam

theorem decoderSuccess_le_orthogonalUnitLift {d : ℕ} (hm : 0 < m)
    (X : Config m d) (hX : BallConfig X) (lam : ℝ) :
    WeakSimplex.decoderSuccess hm X lam ≤
      WeakSimplex.decoderSuccess hm (orthogonalUnitLift X) lam := by
  rw [WeakSimplex.mlDecoder_success_eq_bayesValue, WeakSimplex.mlDecoder_success_eq_bayesValue]
  exact bayesValue_le_orthogonalUnitLift hm X hX lam

#print axioms bayesValue_le_orthogonalUnitLift
#print axioms decoderSuccess_le_orthogonalUnitLift
end Geometry
#print axioms energyLikelihoodMax_le_integral_add
#print axioms gaussianBayesValue_le_add
end SimplexFull
