import SimplexFull.GlobalGaussianNormalization
import SimplexFull.GlobalCentroidConfig
import SimplexFull.GlobalProcrustesBound
import SimplexFull.GlobalRankBound
import Mathlib.Tactic

noncomputable section
open WeakSimplex
open scoped BigOperators
namespace SimplexFull.GlobalTail
open GlobalCentroid
variable {m : ℕ} [NeZero m]

theorem normalizedCovariance_sub_one (hm : 2 ≤ m) (G : Matrix (Fin m) (Fin m) ℝ) :
    normalizedCovariance G - 1 = Geometry.alpha m • (G-Geometry.simplexGram m) := by
  have ha := Geometry.alpha_ne_zero_of_gt_one m (by omega)
  rw [smul_sub, Geometry.simplexGram, smul_smul, mul_inv_cancel₀ ha, one_smul]
  unfold normalizedCovariance Geometry.centering
  abel

theorem frobSq_normalizedCovariance (hm : 2 ≤ m) (G : Matrix (Fin m) (Fin m) ℝ) :
    Geometry.frobSq (normalizedCovariance G-1) =
      (Geometry.alpha m)^2 * Geometry.frobSq (G-Geometry.simplexGram m) := by
  rw [normalizedCovariance_sub_one hm, Geometry.global_frobSq_smul]

theorem qform_one_eq_entrySum (G : Matrix (Fin m) (Fin m) ℝ) :
    qform G (allOnesVector m) = Geometry.entrySum G := by
  rw [qform, inner_one_eq_sum]
  simp only [GlobalCentroid.matrixMul_one_apply, Geometry.entrySum]

theorem centroidExcess_normalizedCovariance (G : Matrix (Fin m) (Fin m) ℝ) :
    GlobalCentroid.centroidExcess (normalizedCovariance G) =
      Geometry.alpha m * Geometry.entrySum G := by
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hadd : ∀ (A B : Matrix (Fin m) (Fin m) ℝ) (x : Coord m),
      qform (A+B) x = qform A x + qform B x := by
    intros A B x
    simp [qform, matrixMul, inner_add_right]
  unfold GlobalCentroid.centroidExcess normalizedCovariance
  rw [hadd, qform_smul_matrix, qform_smul_matrix, qform_one_eq_entrySum]
  change _ + (m:ℝ)⁻¹ * qform (allOnesMatrix m) (allOnesVector m)-(m:ℝ)=_
  rw [qform_allOnes]
  simp only [allOnesVector_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  <;> ring

theorem centroid_entrySum_penalty (hm : 2 ≤ m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G)
    {c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) :
    GlobalCentroid.eta m * Geometry.entrySum G ≤
      GlobalCentroid.thresholdDeficit (normalizedCovariance G) c := by
  have hh := GlobalCentroid.centroid_matrix_penalty hm
    (normalizedCovariance_isWeakSimplexCov hm G hG) hc
  rw [centroidExcess_normalizedCovariance] at hh
  have he : GlobalCentroid.eta m / Geometry.alpha m *
      (Geometry.alpha m * Geometry.entrySum G) =
      GlobalCentroid.eta m * Geometry.entrySum G := by
    field_simp [Geometry.alpha_ne_zero_of_gt_one m (by omega)]
  exact he ▸ hh

#print axioms frobSq_normalizedCovariance
#print axioms centroid_entrySum_penalty
end SimplexFull.GlobalTail
