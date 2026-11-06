import SimplexFull.GlobalCentroidPotential
import SimplexFull.GlobalScalarTaylor
noncomputable section
open WeakSimplex Set
open scoped BigOperators
namespace SimplexFull.GlobalCentroid
open GlobalScalar

theorem centroid_shift_bound {m : Nat} (hm : 2≤m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R) (i : Fin m) :
    |tau m*rowDisplacement R i| ≤ h 0/2 := by
  rw [abs_mul, abs_of_pos (tau_pos hm)]
  exact (mul_le_mul_of_nonneg_left (abs_rowDisplacement_le hm hR i) (tau_pos hm).le).trans
    (tau_shift_le hm)

theorem trialCoordinate_pos {m : Nat} (hm : 2≤m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R)
    {c : Real} (hc : c ∈ Icc (0:Real) 1) (i : Fin m) :
    0 < trialCoordinate R c (tau m) i := by
  have hz := (abs_le.mp (centroid_shift_bound hm hR i)).1
  have hh := strictMono_h.monotone hc.1
  have hp := h_pos 0
  change 0 < h c+tau m*rowDisplacement R i
  linarith

theorem sum_trial_Psi_lower {m : Nat} (hm : 2≤m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R)
    {c : Real} (hc : c ∈ Icc (0:Real) 1) :
    (m:Real)*psiPull c+(q c*tau m)*centroidExcess R-
      (M0*(tau m)^2/2)*(∑ i, (rowDisplacement R i)^2) ≤
      ∑ i, Psi (trialCoordinate R c (tau m) i) := by
  calc
    _ = ∑ i, (psiPull c+(q c*tau m)*rowDisplacement R i-
        (M0*(tau m)^2/2)*(rowDisplacement R i)^2) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, sum_rowDisplacement]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have ht := centroid_scalar_taylor hc (centroid_shift_bound hm hR i)
      rw [Psi_h] at ht
      calc
        _ = psiPull c+q c*(tau m*rowDisplacement R i)-M0*(tau m*rowDisplacement R i)^2/2 := by ring
        _ ≤ _ := ht

#print axioms sum_trial_Psi_lower

theorem centroid_gain_coefficient {m : Nat} (hm : 2≤m) {c : Real}
    (hc : c ∈ Icc (0:Real) 1) :
    q 1*tau m/2 ≤ q c*tau m-(tau m)^2*(1+M0*((m:Real)-1))/2 := by
  have ht := tau_pos hm
  have hq := mul_le_mul_of_nonneg_right (strictAnti_q.antitone hc.2) ht.le
  have hb := mul_le_mul_of_nonneg_left (tau_curvature_le hm) ht.le
  nlinarith

theorem adaptive_value_centroid_gain {m : Nat} (hm : 2≤m)
    {R : Matrix (Fin m) (Fin m) Real} {c : Real} (hR : IsWeakSimplexCov R)
    (hc : c ∈ Icc (0:Real) 1) (w : AdaptiveWitnesses R c) :
    (m:Real)*Real.log (Phi c)+(q 1*tau m/2)*centroidExcess R ≤ adaptiveValue w := by
  have hsum := sum_trial_Psi_lower hm hR hc
  have htrial := adaptive_value_ge_centroid_trial (show 0<m by omega) hR w (tau m)
    (trialCoordinate_pos hm hR hc)
  have hM := M0_pos
  have hsq := mul_le_mul_of_nonneg_left (sum_rowDisplacement_sq_le hm hR)
    (show 0≤M0*(tau m)^2/2 by positivity)
  have hgain := mul_le_mul_of_nonneg_right (centroid_gain_coefficient hm hc)
    (centroidExcess_nonneg (show 0<m by omega) hR)
  dsimp [psiPull] at hsum
  nlinarith

#print axioms adaptive_value_centroid_gain
end SimplexFull.GlobalCentroid
