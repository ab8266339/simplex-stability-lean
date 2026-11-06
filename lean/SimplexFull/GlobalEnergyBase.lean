import SimplexFull.GlobalMeanWidthNoise
import SimplexFull.GlobalMeanWidthLift
import WeakSimplexConjectureLean.Coding.MLDecoder

noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull
variable {m : ℕ} [NeZero m]

/-- Nonunit Gaussian class likelihood, retaining the individual energy correction. -/
def energyLikelihood (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.exp (lam*x i-lam^2*G i i/2)

def energyLikelihoodMax (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Finset.univ.sup' univNonempty (fun i => energyLikelihood G lam i x)

/-- Gram representation of the actual uniform-prior Bayes value for arbitrary energies. -/
def gaussianBayesValue (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ) : ℝ :=
  (1/(m : ℝ)) * ∫ x, energyLikelihoodMax G lam x ∂multivariateGaussian 0 G

theorem measurable_energyLikelihoodMax (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ) :
    Measurable (energyLikelihoodMax G lam) := by
  have hc : Continuous (energyLikelihoodMax G lam) := by
    unfold energyLikelihoodMax
    apply Continuous.finset_sup'_apply univNonempty
    intro i hi
    unfold energyLikelihood
    fun_prop
  exact hc.measurable

theorem energyLikelihood_factor (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) :
    energyLikelihood G lam i x =
      Real.exp (-lam^2*G i i/2) * Real.exp (lam*x i) := by
  unfold energyLikelihood
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_energyLikelihood (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (lam : ℝ) (i : Fin m) :
    Integrable (energyLikelihood G lam i) (multivariateGaussian 0 G) := by
  change Integrable (fun x => energyLikelihood G lam i x) (multivariateGaussian 0 G)
  simp_rw [energyLikelihood_factor]
  exact (integrable_exp_mul_coord G hG lam i).const_mul _

theorem energyLikelihoodMax_nonneg (G : Matrix (Fin m) (Fin m) ℝ)
    (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ energyLikelihoodMax G lam x := by
  obtain ⟨i,hi⟩ := univNonempty (m := m)
  exact (Real.exp_nonneg _).trans (Finset.le_sup' (fun i => energyLikelihood G lam i x) hi)

theorem integrable_energyLikelihoodMax (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (lam : ℝ) :
    Integrable (energyLikelihoodMax G lam) (multivariateGaussian 0 G) := by
  have hs : Integrable (fun x => ∑ i, energyLikelihood G lam i x) (multivariateGaussian 0 G) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_energyLikelihood G hG lam i)
  apply hs.mono_nonneg (measurable_energyLikelihoodMax G lam).aestronglyMeasurable
    (ae_of_all _ (energyLikelihoodMax_nonneg G lam))
  apply ae_of_all
  intro x
  exact Finset.sup'_le univNonempty _ (fun i hi =>
    Finset.single_le_sum (fun j _ => (show 0 ≤ energyLikelihood G lam j x from Real.exp_nonneg _)) hi)

theorem integral_energyLikelihood_eq_one (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (lam : ℝ) (i : Fin m) :
    (∫ x, energyLikelihood G lam i x ∂multivariateGaussian 0 G) = 1 := by
  have hp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin m))) hG (i := i)
  have hm := mgf_gaussianReal hp.map_eq lam
  simp only [mgf, PiLp.zero_apply, zero_mul, zero_add,
    Real.coe_toNNReal _ hG.diag_nonneg] at hm
  simp_rw [energyLikelihood_factor]
  rw [integral_const_mul, hm, ← Real.exp_add]
  convert Real.exp_zero using 1 <;> congr 1 <;> ring

theorem classLikelihoodMax_eq_energyLikelihoodMax {d : ℕ} (hm : 0 < m)
    (X : Geometry.Config m d) (lam : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    WeakSimplex.classLikelihoodMax hm X lam z =
      energyLikelihoodMax (Geometry.gram X) lam (scoreMap X z) := by
  unfold WeakSimplex.classLikelihoodMax energyLikelihoodMax
  apply Finset.sup'_congr univNonempty rfl
  intro i hi
  rw [WeakSimplex.classLikelihood_eq_exp_score]
  simp only [energyLikelihood, scoreMap_apply, Geometry.gram_apply, real_inner_self_eq_norm_sq]

theorem bayesValue_eq_gaussianBayesValue {d : ℕ} (hm : 0 < m)
    (X : Geometry.Config m d) (lam : ℝ) :
    WeakSimplex.bayesValue hm X lam = gaussianBayesValue (Geometry.gram X) lam := by
  unfold WeakSimplex.bayesValue gaussianBayesValue
  congr 1
  simp_rw [classLikelihoodMax_eq_energyLikelihoodMax hm X lam]
  rw [← (Geometry.scoreMap_measurePreserving X).map_eq]
  exact (integral_map (by fun_prop)
    (measurable_energyLikelihoodMax (Geometry.gram X) lam).aestronglyMeasurable).symm

theorem decoderSuccess_eq_gaussianBayesValue {d : ℕ} (hm : 0 < m)
    (X : Geometry.Config m d) (lam : ℝ) :
    WeakSimplex.decoderSuccess hm X lam = gaussianBayesValue (Geometry.gram X) lam := by
  rw [WeakSimplex.mlDecoder_success_eq_bayesValue, bayesValue_eq_gaussianBayesValue]

/-- Exact bridge to the existing equal-unit-energy probability objective,
used only under the genuine UnitConfig hypothesis. -/
theorem bayesValue_eq_decodingSuccess_of_unit {d : ℕ} (hm : 0 < m)
    (X : Geometry.Config m d) (hX : Geometry.UnitConfig X) (lam : ℝ) (hlam : 0 ≤ lam) :
    WeakSimplex.bayesValue hm X lam = decodingSuccess (Geometry.gram X) lam := by
  rw [WeakSimplex.bayesValue_eq_gramMgf hm X hX lam hlam]
  unfold decodingSuccess mgf WeakSimplex.coordinateMax maxCoord
  change (1/(m : ℝ)) * Real.exp (-lam^2/2) *
      (∫ x : EuclideanSpace ℝ (Fin m), Real.exp (lam *
        Finset.univ.sup' univNonempty (fun i => x i)) ∂multivariateGaussian 0 (Geometry.gram X)) = _
  ring

theorem decoderSuccess_eq_decodingSuccess_of_unit {d : ℕ} (hm : 0 < m)
    (X : Geometry.Config m d) (hX : Geometry.UnitConfig X) (lam : ℝ) (hlam : 0 ≤ lam) :
    WeakSimplex.decoderSuccess hm X lam = decodingSuccess (Geometry.gram X) lam := by
  rw [WeakSimplex.mlDecoder_success_eq_bayesValue, bayesValue_eq_decodingSuccess_of_unit hm X hX lam hlam]

#print axioms integral_energyLikelihood_eq_one
#print axioms bayesValue_eq_gaussianBayesValue
#print axioms decoderSuccess_eq_gaussianBayesValue
#print axioms bayesValue_eq_decodingSuccess_of_unit
#print axioms decoderSuccess_eq_decodingSuccess_of_unit
end SimplexFull
