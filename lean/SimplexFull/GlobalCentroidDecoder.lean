import SimplexFull.GlobalTailExponentialGaussian
import SimplexFull.GlobalCentroidDecoderNormalization
import SimplexFull.GlobalGaussianCDF
import SimplexFull.GlobalCentroidConfig
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SimplexFull.GlobalTail
variable {m : Nat} [NeZero m]

theorem decodingSuccess_gap_ge_of_thresholdDeficit
    (R : Matrix (Fin m) (Fin m) Real) (hR : WeakSimplex.IsWeakSimplexCov R)
    {a : Real} (ha : 0<a) {A : Real}
    (hl : ∀ c ∈ Icc (0:Real) 1, A ≤ GlobalCentroid.thresholdDeficit R c) :
    expWindowWeight m a*A ≤ decodingSuccess (1 : Matrix (Fin m) (Fin m) Real) a-
      decodingSuccess R a := by
  apply decodingSuccess_gap_ge_of_cdf R 1 hR.1.1 Matrix.PosSemidef.one ha
    (maxCoord_cdf_domination R hR)
  intro c hc
  rw [cdf_gap_eq_thresholdDeficit]
  exact hl c hc

/-- The manuscript constant cs = W eta, with normalized signal lambda / sqrt(alpha). -/
def centroidDecoderConstant (m : Nat) (lam : Real) : Real :=
  expWindowWeight m (lam/Real.sqrt (Geometry.alpha m))*GlobalCentroid.eta m

theorem centroidDecoderConstant_pos (hm : 2≤m) {lam : Real} (hlam : 0<lam) :
    0<centroidDecoderConstant m lam := by
  apply mul_pos
  · exact expWindowWeight_pos (by omega)
      (div_pos hlam (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm)))
  · exact GlobalCentroid.eta_pos hm

/-- Actual unit-configuration decoder stability from the exact centroid penalty. -/
theorem decodingSuccess_centroid_penalty {d : Nat} (hm : 2≤m)
    (X : Geometry.Config m d) (hX : Geometry.UnitConfig X)
    {lam : Real} (hlam : 0<lam) :
    centroidDecoderConstant m lam*‖∑ i, X i‖^2 ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess (Geometry.gram X) lam := by
  have hG := GlobalFoundation.gram_isCorrelation X hX
  have hR := normalizedCovariance_isWeakSimplexCov hm (Geometry.gram X) hG
  have hmu : 0<lam/Real.sqrt (Geometry.alpha m) :=
    div_pos hlam (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm))
  have hh := decodingSuccess_gap_ge_of_thresholdDeficit
    (normalizedCovariance (Geometry.gram X)) hR hmu
    (fun c hc => GlobalCentroid.centroid_penalty hm X hX hc)
  rw [decodingSuccess_simplex_normalized hm,
    decodingSuccess_normalizedCovariance hm _ hG]
  simpa only [centroidDecoderConstant, mul_assoc] using hh

#print axioms decodingSuccess_gap_ge_of_thresholdDeficit
#print axioms decodingSuccess_centroid_penalty
end SimplexFull.GlobalTail
