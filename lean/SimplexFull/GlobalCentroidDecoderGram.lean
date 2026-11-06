import SimplexFull.GlobalCentroidDecoder
import SimplexFull.GlobalNormalizationAlgebra
import SimplexFull.GlobalEnergy
noncomputable section
namespace SimplexFull.GlobalTail
variable {m : Nat} [NeZero m]

theorem decodingSuccess_centroid_entrySum (hm : 2≤m)
    (G : Matrix (Fin m) (Fin m) Real) (hG : WeakSimplex.IsCorrelation G)
    {lam : Real} (hlam : 0<lam) :
    centroidDecoderConstant m lam*Geometry.entrySum G ≤
      decodingSuccess (Geometry.simplexGram m) lam-decodingSuccess G lam := by
  have hR := normalizedCovariance_isWeakSimplexCov hm G hG
  have hmu : 0<lam/Real.sqrt (Geometry.alpha m) :=
    div_pos hlam (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm))
  have hh := decodingSuccess_gap_ge_of_thresholdDeficit
    (normalizedCovariance G) hR hmu (fun c hc => centroid_entrySum_penalty hm G hG hc)
  rw [decodingSuccess_simplex_normalized hm, decodingSuccess_normalizedCovariance hm _ hG]
  simpa only [centroidDecoderConstant, mul_assoc] using hh

/-- Discharges the unit decoder input used by the nonunit energy lift. -/
theorem unitDecoderCentroidBound (hm : 2≤m) {lam : Real} (hlam : 0<lam) :
    Geometry.UnitDecoderCentroidBound m lam (centroidDecoderConstant m lam) := by
  intro G hG hdiag
  exact decodingSuccess_centroid_entrySum hm G ⟨hG,hdiag⟩ hlam

#print axioms decodingSuccess_centroid_entrySum
#print axioms unitDecoderCentroidBound
end SimplexFull.GlobalTail
