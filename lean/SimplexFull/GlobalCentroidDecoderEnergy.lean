import SimplexFull.GlobalCentroidDecoderGram
noncomputable section
open scoped BigOperators
namespace SimplexFull.GlobalTail
variable {m : Nat} [NeZero m]

/-- Actual operational decoder bound for centroid plus unused energy. -/
theorem ball_decoder_centroid_energy {d refdim : Nat}
    (hm : 2≤m) {lam : Real} (hlam : 0<lam)
    (X : Geometry.Config m d) (V : Geometry.Config m refdim)
    (hX : Geometry.BallConfig X) (hV : Geometry.gram V = Geometry.simplexGram m) :
    centroidDecoderConstant m lam * (‖∑ i, X i‖^2 + ∑ i, (1-‖X i‖^2)) ≤
      WeakSimplex.decoderSuccess (NeZero.pos m) V lam -
        WeakSimplex.decoderSuccess (NeZero.pos m) X lam :=
  Geometry.ball_decoder_centroid_energy_of_unit hm hlam.le
    (unitDecoderCentroidBound hm hlam) X V hX hV

/-- Actual operational decoder bound for unused energy; no unit-bound hypothesis remains. -/
theorem ball_decoder_unused_energy {d refdim : Nat}
    (hm : 2≤m) {lam : Real} (hlam : 0<lam)
    (X : Geometry.Config m d) (V : Geometry.Config m refdim)
    (hX : Geometry.BallConfig X) (hV : Geometry.gram V = Geometry.simplexGram m) :
    centroidDecoderConstant m lam * (∑ i, (1-‖X i‖^2)) ≤
      WeakSimplex.decoderSuccess (NeZero.pos m) V lam -
        WeakSimplex.decoderSuccess (NeZero.pos m) X lam :=
  Geometry.ball_decoder_unused_energy_of_unit hm hlam (centroidDecoderConstant_pos hm hlam).le
    (unitDecoderCentroidBound hm hlam) X V hX hV

/-- The same exact unused-energy constant for the actual Bayes value. -/
theorem ball_bayes_unused_energy {d refdim : Nat}
    (hm : 2≤m) {lam : Real} (hlam : 0<lam)
    (X : Geometry.Config m d) (V : Geometry.Config m refdim)
    (hX : Geometry.BallConfig X) (hV : Geometry.gram V = Geometry.simplexGram m) :
    centroidDecoderConstant m lam * (∑ i, (1-‖X i‖^2)) ≤
      WeakSimplex.bayesValue (NeZero.pos m) V lam -
        WeakSimplex.bayesValue (NeZero.pos m) X lam :=
  Geometry.ball_bayes_unused_energy_of_unit hm hlam (centroidDecoderConstant_pos hm hlam).le
    (unitDecoderCentroidBound hm hlam) X V hX hV

#print axioms ball_decoder_centroid_energy
#print axioms ball_decoder_unused_energy
#print axioms ball_bayes_unused_energy
end SimplexFull.GlobalTail
