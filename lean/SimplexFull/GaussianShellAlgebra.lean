import SimplexFull.GaussianHessian
import SimplexFull.ShapeHessian
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
open SimplexFull.Covariance
variable {m : ℕ} [NeZero m]
lemma centered_shell_square (D : shellSpace m) : centered ((D : ShapeMatrix m)*(D : ShapeMatrix m)) := by
  obtain ⟨_,hPD,hDP,_⟩ := shell_facts D
  apply shell_centered (NeZero.ne m)
  · rw [← Matrix.mul_assoc, hPD]
  · rw [Matrix.mul_assoc, hDP]
lemma trace_shell_square (D : shellSpace m) :
    Matrix.trace ((D : ShapeMatrix m)*(D : ShapeMatrix m)) = shellN D-2*shellR D/(m:ℝ) := by
  obtain ⟨hS,hPD,hDP,htr⟩ := shell_facts D
  rw [trace_mul_self_eq_frobSq hS, frobSq_centered_tracefree (NeZero.ne m) (shell_centered (NeZero.ne m) hPD hDP) htr]
  unfold shellN shellR shellB
  ring
lemma fderiv_extendedLoss_shell_acceleration (hm : 2 ≤ m) {mu : ℝ} (hmu : 0 < mu) (D : shellSpace m) :
    fderiv ℝ (extendedLoss (m:=m) mu) 1 (uncompress ((D : ShapeMatrix m)*(D : ShapeMatrix m))) =
      -(m:ℝ)*gaussianC m mu/2*(shellN D-2*shellR D/(m:ℝ)) := by
  rw [fderiv_extendedLoss_one_coefficient hm hmu (uncompress_zeroDiagonal _),
    halfEntrySum_uncompress_of_centered (centered_shell_square D), trace_shell_square D]
  ring
lemma shell_hessian_coefficient_algebra (A B C : ℝ) (D : shellSpace m) :
    4*(A/2*shellN D-(C-B)*shellR D)+
      2*(-(m:ℝ)*C/2*(shellN D-2*shellR D/(m:ℝ))) = 2*shellQuadratic m A B C D := by
  unfold shellQuadratic
  ring
#print axioms fderiv_extendedLoss_shell_acceleration
end SimplexFull.Geometry
