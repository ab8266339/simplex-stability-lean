import SimplexFull.DensityInverse

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix ContinuousLinearMap Filter
open scoped BigOperators Matrix.Norms.L2Operator Real Topology
namespace SimplexFull.Covariance
variable {m : ℕ}

theorem hasDerivAt_inverse_covLine_at_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) (-A) 0 := by
  simpa [matrix_inv_one] using hasDerivAt_inv_covLine A (t := 0) (by simp)

theorem hasDerivAt_deriv_inverse_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) t)
      ((2 : ℝ) • (A * A)) 0 := by
  let B : ℝ → Matrix (Fin m) (Fin m) ℝ := fun t => (1 + t • A)⁻¹
  let g : ℝ → Matrix (Fin m) (Fin m) ℝ := fun t => -(B t * A * B t)
  have hB : HasDerivAt B (-A) 0 := hasDerivAt_inverse_covLine_at_zero A
  have hg : HasDerivAt g ((2 : ℝ) • (A * A)) 0 := by
    have hh := ((hB.mul_const A).mul hB).neg
    simpa [g, B, matrix_inv_one, two_smul, Pi.mul_def, Pi.neg_def] using hh
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0 := by
    exact ((contDiff_det_line A).continuous.tendsto 0).eventually_ne (by simp)
  have he : deriv B =ᶠ[𝓝 (0 : ℝ)] g := hn.mono fun t ht => (hasDerivAt_inv_covLine A ht).deriv
  exact hg.congr_of_eventuallyEq he

theorem iteratedDeriv_two_inverse_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    iteratedDeriv 2 (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) 0 =
      ((2 : ℝ) • (A * A)) := by
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using
    (hasDerivAt_deriv_inverse_covLine_zero A).deriv

set_option pp.fullNames true
#print axioms hasDerivAt_inverse_covLine_at_zero
#print axioms hasDerivAt_deriv_inverse_covLine_zero
#print axioms iteratedDeriv_two_inverse_covLine_zero
end SimplexFull.Covariance
