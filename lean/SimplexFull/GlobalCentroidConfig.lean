import SimplexFull.GlobalCentroidOrthant
import SimplexFull.GlobalGaussianNormalization
noncomputable section
open WeakSimplex Set
open scoped BigOperators
namespace SimplexFull.GlobalCentroid

theorem qform_gram_one {m d : Nat} (X : Geometry.Config m d) :
    qform (Geometry.gram X) (allOnesVector m) = ‖∑ i, X i‖^2 := by
  rw [qform, inner_one_eq_sum]
  simp only [matrixMul_one_apply, Geometry.gram_apply]
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  exact Finset.sum_comm

theorem centroidExcess_normalized_gram {m d : Nat} [NeZero m]
    (X : Geometry.Config m d) :
    centroidExcess (GlobalTail.normalizedCovariance (Geometry.gram X)) =
      alpha m * ‖∑ i, X i‖^2 := by
  have hm : (m:Real) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hq : ∀ (A B : Matrix (Fin m) (Fin m) Real) (x : Coord m),
      qform (A+B) x = qform A x+qform B x := by
    intros A B x
    simp [qform, matrixMul, inner_add_right]
  unfold centroidExcess GlobalTail.normalizedCovariance
  rw [hq, qform_smul_matrix, qform_smul_matrix, qform_gram_one]
  change _ + (m:Real)⁻¹*qform (allOnesMatrix m) (allOnesVector m)-(m:Real)=_
  rw [qform_allOnes]
  simp only [allOnesVector_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  <;> ring

/-- Manuscript Lemma 4, with its exact tau/M0 coefficient, for every unit configuration. -/
theorem centroid_penalty {m d : Nat} (hm : 2≤m)
    (X : Geometry.Config m d) (hX : Geometry.UnitConfig X)
    {c : Real} (hc : c ∈ Icc (0:Real) 1) :
    eta m*‖∑ i, X i‖^2 ≤
      thresholdDeficit (GlobalTail.normalizedCovariance (Geometry.gram X)) c := by
  letI : NeZero m := ⟨by omega⟩
  have hG : IsCorrelation (Geometry.gram X) :=
    ⟨Geometry.gram_posSemidef X, Geometry.gram_diagonal_unit X hX⟩
  have hh := centroid_matrix_penalty hm
    (GlobalTail.normalizedCovariance_isWeakSimplexCov hm (Geometry.gram X) hG) hc
  rw [centroidExcess_normalized_gram] at hh
  have heq : eta m/alpha m*(alpha m*‖∑ i, X i‖^2)=eta m*‖∑ i, X i‖^2 := by
    field_simp [ne_of_gt (alpha_pos hm)]
  rwa [heq] at hh

#print axioms centroid_penalty
end SimplexFull.GlobalCentroid
