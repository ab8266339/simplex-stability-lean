import SimplexFull.GlobalEnergyNoise
noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]

/-- Explicit modular input: the actual equal-unit-energy Gaussian decoding
deficit controls the actual Gram entry sum. The independent global comparison
chain must discharge this predicate before the quantitative corollary is final. -/
def UnitDecoderCentroidBound (m : ℕ) [NeZero m] (lam cs : ℝ) : Prop :=
  ∀ G : Matrix (Fin m) (Fin m) ℝ, G.PosSemidef → (∀ i, G i i = 1) →
    cs * entrySum G ≤ decodingSuccess (simplexGram m) lam-decodingSuccess G lam

/-- The actual nonunit ML deficit controls centroid energy plus unused energy.
The original and reference ambient dimensions are independent. -/
theorem ball_decoder_centroid_energy_of_unit {d refdim : ℕ}
    (hm : 2 ≤ m) {lam cs : ℝ} (hlam : 0 ≤ lam)
    (hunit : UnitDecoderCentroidBound m lam cs)
    (X : Config m d) (V : Config m refdim)
    (hX : BallConfig X) (hV : gram V = simplexGram m) :
    cs * (‖∑ i, X i‖^2 + ∑ i, (1-‖X i‖^2)) ≤
      WeakSimplex.decoderSuccess (NeZero.pos m) V lam -
        WeakSimplex.decoderSuccess (NeZero.pos m) X lam := by
  have hu := hunit (gram (orthogonalUnitLift X)) (gram_posSemidef _)
    (gram_diagonal_unit _ (unitConfig_orthogonalUnitLift X hX))
  have hVunit : UnitConfig V := unitConfig_of_simplexGram V (by omega) hV
  have hreference : decodingSuccess (simplexGram m) lam =
      WeakSimplex.decoderSuccess (NeZero.pos m) V lam := by
    rw [decoderSuccess_eq_decodingSuccess_of_unit (NeZero.pos m) V hVunit lam hlam, hV]
  have hlift : decodingSuccess (gram (orthogonalUnitLift X)) lam =
      WeakSimplex.decoderSuccess (NeZero.pos m) (orthogonalUnitLift X) lam := by
    rw [decoderSuccess_eq_decodingSuccess_of_unit (NeZero.pos m) (orthogonalUnitLift X)
      (unitConfig_orthogonalUnitLift X hX) lam hlam]
  have hmono := decoderSuccess_le_orthogonalUnitLift (NeZero.pos m) X hX lam
  rw [global_entrySum_gram, centroid_sq_orthogonalUnitLift X hX,
    hreference, hlift] at hu
  simp only [energyDeficit] at hu
  linarith

/-- Unused-energy corollary for the actual operational maximum-likelihood
success probability of arbitrary nonunit signals in the unit ball.
No equal-energy decoding formula is applied to the original X. -/
theorem ball_decoder_unused_energy_of_unit {d refdim : ℕ}
    (hm : 2 ≤ m) {lam cs : ℝ} (hlam : 0 < lam) (hcs : 0 ≤ cs)
    (hunit : UnitDecoderCentroidBound m lam cs)
    (X : Config m d) (V : Config m refdim)
    (hX : BallConfig X) (hV : gram V = simplexGram m) :
    cs * (∑ i, (1-‖X i‖^2)) ≤
      WeakSimplex.decoderSuccess (NeZero.pos m) V lam -
        WeakSimplex.decoderSuccess (NeZero.pos m) X lam := by
  have h := ball_decoder_centroid_energy_of_unit hm hlam.le hunit X V hX hV
  have hnn := mul_nonneg hcs (sq_nonneg ‖∑ i, X i‖)
  nlinarith

/-- The same statement at the density-maximum Bayes-value boundary, already
identified with the measurable ML decoder's operational success. -/
theorem ball_bayes_unused_energy_of_unit {d refdim : ℕ}
    (hm : 2 ≤ m) {lam cs : ℝ} (hlam : 0 < lam) (hcs : 0 ≤ cs)
    (hunit : UnitDecoderCentroidBound m lam cs)
    (X : Config m d) (V : Config m refdim)
    (hX : BallConfig X) (hV : gram V = simplexGram m) :
    cs * (∑ i, (1-‖X i‖^2)) ≤
      WeakSimplex.bayesValue (NeZero.pos m) V lam -
        WeakSimplex.bayesValue (NeZero.pos m) X lam := by
  have h := ball_decoder_unused_energy_of_unit hm hlam hcs hunit X V hX hV
  simpa only [WeakSimplex.mlDecoder_success_eq_bayesValue] using h

#print axioms ball_decoder_centroid_energy_of_unit
#print axioms ball_decoder_unused_energy_of_unit
#print axioms ball_bayes_unused_energy_of_unit
end SimplexFull.Geometry
