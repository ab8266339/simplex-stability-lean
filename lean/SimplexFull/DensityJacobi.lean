import SimplexFull.DensityInverseSecond

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix ContinuousLinearMap Filter
open scoped BigOperators Matrix.Norms.L2Operator Real Polynomial Topology
namespace SimplexFull.Covariance
variable {m : ℕ}

lemma ds_det_covLine_add (A : Matrix (Fin m) (Fin m) ℝ) (t u : ℝ)
    (ht : ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) + (t + u) • A).det =
      ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det *
        ((1 : Matrix (Fin m) (Fin m) ℝ) +
          u • (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A)).det := by
  have hm : ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) *
      (1 + u • (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A)) =
      (1 : Matrix (Fin m) (Fin m) ℝ) + (t + u) • A := by
    rw [mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht),
      Matrix.one_mul, add_assoc, ← add_smul]
  rw [← hm, Matrix.det_mul]

theorem ds_hasDerivAt_det_covLine (A : Matrix (Fin m) (Fin m) ℝ) {t : ℝ}
    (ht : ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0) :
    HasDerivAt (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A).det)
      (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det *
        Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A)) t := by
  have hf : (fun u : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + (t + u) • A).det) =
      fun u => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det *
        ((1 : Matrix (Fin m) (Fin m) ℝ) +
          u • (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A)).det := by
    funext u
    exact ds_det_covLine_add A t u ht
  have hh := (hasDerivAt_det_covLine_zero
    (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A)).const_mul
    (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det)
  rw [← hf] at hh
  rw [← sub_self t] at hh
  have hc := hh.comp_sub_const t t
  simpa using hc

def ds_traceCLM : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin m) ℝ ℝ).toContinuousLinearMap

theorem ds_hasDerivAt_trace_inverse_mul_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ =>
      Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A))
      (-(A*A).trace) 0 := by
  have hh := ds_traceCLM.hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_inverse_covLine_at_zero A).mul_const A)
  simpa [ds_traceCLM, Matrix.traceLinearMap, neg_mul, Function.comp_def] using hh

theorem ds_hasDerivAt_deriv_det_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A).det) t)
      (A.trace^2 - (A*A).trace) 0 := by
  let D : ℝ → ℝ := fun t => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det
  let g : ℝ → ℝ := fun t => D t *
    Matrix.trace (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A)
  have hh := (hasDerivAt_det_covLine_zero A).mul (ds_hasDerivAt_trace_inverse_mul_zero A)
  have hg : HasDerivAt g (A.trace^2 - (A*A).trace) 0 := by
    simpa [g, D, matrix_inv_one, pow_two, sub_eq_add_neg, Pi.mul_def] using hh
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0 :=
    ((contDiff_det_line A).continuous.tendsto 0).eventually_ne (by simp)
  have he : deriv D =ᶠ[𝓝 (0 : ℝ)] g :=
    hn.mono fun t ht => (ds_hasDerivAt_det_covLine A ht).deriv
  exact hg.congr_of_eventuallyEq he

theorem ds_iteratedDeriv_two_det_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    iteratedDeriv 2 (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det) 0 =
      A.trace^2 - (A*A).trace := by
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using
    (ds_hasDerivAt_deriv_det_covLine_zero A).deriv

set_option pp.fullNames true
#print axioms ds_hasDerivAt_det_covLine
#print axioms ds_hasDerivAt_deriv_det_covLine_zero
#print axioms ds_iteratedDeriv_two_det_covLine_zero
end SimplexFull.Covariance
