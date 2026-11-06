import SimplexFull.ShellObjective
import SimplexFull.GaussianSymmetry
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
namespace SimplexFull.Geometry
lemma shell_vertical_stationary {m : ℕ} (hm : 2 ≤ m) (tau : ℝ)
    (loss : ShapeMatrix m → ℝ)
    (hinv : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m,
      loss (A.submatrix σ σ) = loss A)
    (hloss : DifferentiableAt ℝ loss (shellCovariance m tau 0)) (H : shellSpace m) :
    (fderiv ℝ (fun p : ℝ × shellSpace m => loss (shellCovarianceOnSpace m p.1 p.2))
      (tau,0)) (0,H) = 0 := by
  let F : ℝ × shellSpace m → ℝ := fun p => loss (shellCovarianceOnSpace m p.1 p.2)
  let g : ShapeMatrix m → ℝ := fun D => loss (shellCovariance m tau D)
  have hg : DifferentiableAt ℝ g 0 :=
    hloss.comp 0 (Symmetry.differentiable_shellCovariance tau).differentiableAt
  have hF : DifferentiableAt ℝ F (tau,0) :=
    hloss.comp (tau,0) ((contDiff_shellCovarianceOnSpace m).differentiable (by simp)).differentiableAt
  have hM : HasDerivAt (fun t : ℝ => t • (H : ShapeMatrix m)) (H : ShapeMatrix m) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const (H : ShapeMatrix m)
  have hP : HasDerivAt (fun t : ℝ => (tau,t • H)) (0,H) 0 := by
    simpa using (hasDerivAt_const (0:ℝ) tau).prodMk ((hasDerivAt_id (0:ℝ)).smul_const H)
  have h1 : HasDerivAt (fun t : ℝ => g (t • (H : ShapeMatrix m))) 0 0 := by
    have h := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hM (by simp)
    rw [Symmetry.loss_fderiv_shellCovariance_vanishes hm tau loss hinv hloss H] at h
    exact h
  have h2 : HasDerivAt (fun t : ℝ => F (tau,t • H))
      ((fderiv ℝ F (tau,0)) (0,H)) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hP (by simp)
  exact h2.unique h1
#print axioms shell_vertical_stationary
lemma extendedLoss_submatrix_perm {m : ℕ} [NeZero m] (mu : ℝ) (R : ShapeMatrix m)
    (sigma : Equiv.Perm (Fin m)) : extendedLoss mu (R.submatrix sigma sigma) = extendedLoss mu R := by
  simp only [extendedLoss, Covariance.rhoExpectation_submatrix_perm]
theorem exists_shellLoss_stationary {m : ℕ} [NeZero m] (hm : 2 ≤ m) (mu : ℝ) :
    ∃ eps > 0, ∀ tau : ℝ, |tau| < eps → ∀ H : shellSpace m,
      (fderiv ℝ (shellLoss (m:=m) mu) (tau,0)) (0,H) = 0 := by
  have ht : ContinuousAt (fun tau : ℝ => shellCovariance m tau 0) 0 :=
    ((contDiff_shellCovariance m).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousAt
  have ht' : Filter.Tendsto (fun tau : ℝ => shellCovariance m tau 0) (𝓝 0) (𝓝 1) := by
    simpa only [ContinuousAt, shellCovariance_zero] using ht
  have he : ∀ᶠ tau : ℝ in 𝓝 0,
      ContDiffAt ℝ 2 (extendedLoss (m:=m) mu) (shellCovariance m tau 0) :=
    ht'.eventually ((contDiffAt_extendedLoss_one (m:=m) mu).eventually (by norm_num))
  obtain ⟨eps,heps,hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨eps,heps,?_⟩
  intro tau htau H
  have hd := (hb (by simpa only [dist_zero_right, Real.norm_eq_abs] using htau)).differentiableAt (by norm_num)
  exact shell_vertical_stationary hm tau (extendedLoss (m:=m) mu)
    (fun sigma R => extendedLoss_submatrix_perm mu R sigma) hd H
#print axioms exists_shellLoss_stationary
end SimplexFull.Geometry