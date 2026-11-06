import SimplexFull.DensityJacobi
import SimplexFull.GaussianDifferentiation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix ContinuousLinearMap Filter
open scoped BigOperators Matrix.Norms.L2Operator Real Topology
namespace SimplexFull.Covariance
variable {m : ℕ}

lemma ds_prefactor_derivative_algebra (z tr : ℝ) (hz : 0 < z) :
    -((z*tr)/(2*Real.sqrt z))/(Real.sqrt z)^2 =
      -(Real.sqrt z)⁻¹*tr/2 := by
  have hs : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr hz).ne'
  have hsq : (Real.sqrt z)^2 = z := Real.sq_sqrt hz.le
  field_simp [hs]
  rw [hsq]
  ring

theorem ds_hasDerivAt_rhoPrefactor_covLine (A : Matrix (Fin m) (Fin m) ℝ) {t : ℝ}
    (ht : 0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det) :
    HasDerivAt (fun s : ℝ => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A))
      (-rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) *
        Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A) / 2) t := by
  let c : ℝ := (2*Real.pi)^m
  have hc : 0 < c := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  have hd := (ds_hasDerivAt_det_covLine A ht.ne').const_mul c
  have hp : 0 < c * ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det := mul_pos hc ht
  have hh := (hd.sqrt hp.ne').inv ((Real.sqrt_pos.mpr hp).ne')
  have he : -((c * (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det *
      Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A))) /
      (2 * Real.sqrt (c * ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det))) /
      (Real.sqrt (c * ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det))^2 =
      -rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) *
        Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A) / 2 := by
    rw [← mul_assoc]
    exact ds_prefactor_derivative_algebra _ _ hp
  exact (hh.congr_deriv he).congr_of_eventuallyEq (Eventually.of_forall fun s => rfl)

theorem ds_hasDerivAt_deriv_rhoPrefactor_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)) t)
      (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
        ((A*A).trace/2 + A.trace^2/4)) 0 := by
  let P : ℝ → ℝ := fun t => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)
  let g : ℝ → ℝ := fun t => -P t *
    Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A) / 2
  have hp := hasDerivAt_rhoPrefactor_covLine_zero A
  have ht := ds_hasDerivAt_trace_inverse_mul_zero A
  have hh := (hp.neg.mul ht).div_const 2
  have hg : HasDerivAt g
      (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
        ((A*A).trace/2 + A.trace^2/4)) 0 := by
    have hc : (-(-rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2) * A.trace +
        -rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * -(A*A).trace) / 2 =
        rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
          ((A*A).trace/2 + A.trace^2/4) := by ring
    simpa only [zero_smul, add_zero, matrix_inv_one, Matrix.one_mul, Pi.neg_apply,
      hc, g, P, Pi.mul_def, Pi.neg_def] using hh
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det :=
    ((contDiff_det_line A).continuous.tendsto 0).eventually (eventually_gt_nhds (by simp))
  have he : deriv P =ᶠ[𝓝 (0 : ℝ)] g :=
    hn.mono fun t ht => (ds_hasDerivAt_rhoPrefactor_covLine A ht).deriv
  exact hg.congr_of_eventuallyEq he

theorem ds_iteratedDeriv_two_rhoPrefactor_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    iteratedDeriv 2 (fun t : ℝ => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)) 0 =
      rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
        ((A*A).trace/2 + A.trace^2/4) := by
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using
    (ds_hasDerivAt_deriv_rhoPrefactor_covLine_zero A).deriv

set_option pp.fullNames true
#print axioms ds_hasDerivAt_rhoPrefactor_covLine
#print axioms ds_hasDerivAt_deriv_rhoPrefactor_covLine_zero
#print axioms ds_iteratedDeriv_two_rhoPrefactor_covLine_zero
end SimplexFull.Covariance
