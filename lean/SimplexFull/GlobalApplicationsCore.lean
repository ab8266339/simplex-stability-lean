import SimplexFull.GlobalComparison
import SimplexFull.GlobalApplicationConstants
noncomputable section
open Set
namespace SimplexFull.GlobalApplication
variable {m : Nat} [NeZero m]

/-- Actual all-PSD covariance comparison on the unit threshold window. -/
theorem thresholdDeficit_ge_kappa (hm : 2≤m)
    (R : Matrix (Fin m) (Fin m) Real) (hR : WeakSimplex.IsWeakSimplexCov R)
    {c : Real} (hc : c ∈ Icc (0:Real) 1) :
    kappa m*Geometry.frobSq (R-1) ≤ GlobalCentroid.thresholdDeficit R c := by
  exact GlobalComparison.orthant_linear_comparison hm R hR 0 1 c hc.1 hc.2

/-- Full unit Gram mean comparison, with no supplied CDF estimate. -/
theorem gaussianMaxMean_gram_penalty (hm : 2≤m)
    (G : Matrix (Fin m) (Fin m) Real) (hG : WeakSimplex.IsCorrelation G) :
    meanGramConstant m*Geometry.frobSq (G-Geometry.simplexGram m) ≤
      gaussianMaxMean (Geometry.simplexGram m)-gaussianMaxMean G := by
  exact GlobalTail.gaussianMaxMean_gram_penalty_of_thresholdDeficit hm G hG (kappa_pos hm).le
    (fun c hc => thresholdDeficit_ge_kappa hm _
      (GlobalTail.normalizedCovariance_isWeakSimplexCov hm G hG) hc)

/-- The exact unit comparison input to the mean-width lift is fully discharged. -/
theorem unitGaussianMaxBounds (hm : 2≤m) :
    Geometry.UnitGaussianMaxBounds m (meanGramConstant m) (GlobalTail.centroidMeanConstant m) := by
  intro G hG hdiag
  exact ⟨gaussianMaxMean_gram_penalty hm G ⟨hG,hdiag⟩,
    GlobalTail.gaussianMaxMean_centroid_penalty hm G ⟨hG,hdiag⟩⟩

/-- Exact global Gram stability constant cg for actual Gaussian decoding. -/
theorem decodingSuccess_gram_penalty (hm : 2≤m)
    (G : Matrix (Fin m) (Fin m) Real) (hG : WeakSimplex.IsCorrelation G)
    {lam : Real} (hlam : 0<lam) :
    gramDecoderConstant m lam*Geometry.frobSq (G-Geometry.simplexGram m) ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess G lam := by
  have hR := GlobalTail.normalizedCovariance_isWeakSimplexCov hm G hG
  have hmu : 0<lam/Real.sqrt (Geometry.alpha m) :=
    div_pos hlam (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm))
  have hh := GlobalTail.decodingSuccess_gap_ge_of_thresholdDeficit
    (GlobalTail.normalizedCovariance G) hR hmu
    (fun c hc => thresholdDeficit_ge_kappa hm _ hR hc)
  rw [GlobalTail.frobSq_normalizedCovariance hm G] at hh
  rw [GlobalTail.decodingSuccess_simplex_normalized hm,
    GlobalTail.decodingSuccess_normalizedCovariance hm _ hG]
  simpa only [gramDecoderConstant, mul_assoc] using hh

#print axioms thresholdDeficit_ge_kappa
#print axioms gaussianMaxMean_gram_penalty
#print axioms unitGaussianMaxBounds
#print axioms decodingSuccess_gram_penalty
end SimplexFull.GlobalApplication
