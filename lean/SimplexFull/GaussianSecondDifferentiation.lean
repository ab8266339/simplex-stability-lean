import SimplexFull.PrecisionCompositionSecond
import SimplexFull.DensityPrefactorSecond
import SimplexFull.SecondChain
import SimplexFull.GramCoordinates

noncomputable section
open MeasureTheory Matrix Filter ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology
set_option maxHeartbeats 800000
namespace SimplexFull.Covariance
variable {m : ℕ} [NeZero m]
local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedSpace

omit [NeZero m] in
lemma second_product_zero_left {f g : ℝ → ℝ} {f2 g1 g2 : ℝ}
    (hf1 : HasDerivAt f 0 0) (hg1 : HasDerivAt g g1 0)
    (hf2 : HasDerivAt (deriv f) f2 0) (hg2 : HasDerivAt (deriv g) g2 0)
    (hfn : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ f t)
    (hgn : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ g t) :
    HasDerivAt (deriv (fun t => f t*g t)) (f2*g 0+f 0*g2) 0 := by
  have he : deriv (fun t => f t*g t) =ᶠ[𝓝 (0:ℝ)] fun t => deriv f t*g t+f t*deriv g t := by
    filter_upwards [hfn,hgn] with t ht hu
    exact deriv_mul ht hu
  have hh := (hf2.mul hg1).add (hf1.mul hg2)
  have hd : deriv f 0=0 := hf1.deriv
  have hv : HasDerivAt (fun t => deriv f t*g t+f t*deriv g t) (f2*g 0+f 0*g2) 0 := by
    convert hh using 1 <;> first | rfl | simp [hd]
  exact hv.congr_of_eventuallyEq he

lemma precision_prefactor_one_ne_zero : rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  apply ne_of_gt
  unfold rhoPrefactor
  simp only [Matrix.det_one, mul_one]
  positivity

lemma integrable_precision_second_poly (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x => precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x*
      ((quad A x)^2/4-quad (A*A) x)) := by
  have hh := ((integrable_exp_max_rho_one_mul_quad_sq lam A).div_const 4).sub
    (integrable_exp_max_rho_one_mul_quad lam (A*A))
  have hs := hh.const_mul (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹
  convert hs using 1
  ext x
  simp only [Pi.sub_apply]
  rw [← rhoPrefactor_mul_precisionKernel_one]
  have hk := precision_prefactor_one_ne_zero (m := m)
  field_simp
lemma precision_second_product_integral (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ)*(A*A).trace/2)*precisionIntegral (m := m) lam 1+
      rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ)*
        (∫ x, precisionKernel lam 1 x*((quad A x)^2/4-quad (A*A) x)) =
      2*(∫ x, Real.exp (lam*maxCoord x)*secondDensityCoeff A x) := by
  have hi := integrable_precisionKernel (m := m) lam (M := 1) (by simp)
  have hj := integrable_precision_second_poly lam A
  unfold precisionIntegral
  rw [← integral_const_mul, ← integral_const_mul]
  rw [← integral_add (hi.const_mul _) (hj.const_mul _), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    _ = (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ)*precisionKernel lam 1 x)*
        ((A*A).trace/2+(quad A x)^2/4-quad (A*A) x) := by ring
    _ = (Real.exp (lam*maxCoord x)*rho 1 x)*
        ((A*A).trace/2+(quad A x)^2/4-quad (A*A) x) := by
      rw [rhoPrefactor_mul_precisionKernel_one]
    _ = _ := by unfold secondDensityCoeff; ring

theorem hasDerivAt_deriv_rhoExpectation_covLine_zero_trace
    (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (htr : A.trace=0) :
    HasDerivAt (deriv (fun t : ℝ => rhoExpectation lam (1+t • A)))
      (2*(∫ x, Real.exp (lam*maxCoord x)*secondDensityCoeff A x)) 0 := by
  let line : ℝ → Matrix (Fin m) (Fin m) ℝ := fun t => 1+t • A
  let c : ℝ → ℝ := fun t => rhoPrefactor (line t)
  let psi : ℝ → ℝ := fun t => precisionIntegral lam (line t)⁻¹
  have hl0 : line 0=1 := by simp [line]
  have hl : ContDiff ℝ 2 line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hcC : ContDiffAt ℝ 2 c 0 := by
    have hh : ContDiffAt ℝ 2 (rhoPrefactor : Matrix (Fin m) (Fin m) ℝ → ℝ) (line 0) := by
      rw [hl0]
      exact contDiffAt_rhoPrefactor_one.of_le (by simp)
    simpa only [c, Function.comp_def] using hh.comp 0 hl.contDiffAt
  have hpC : ContDiffAt ℝ 2 psi 0 := by
    have hJ : ContDiffAt ℝ 2 (precisionIntegral (m := m) lam) (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ := by
      simpa only [matrix_inv_one] using contDiffAt_precisionIntegral_one (m := m) lam
    have hJR : ContDiffAt ℝ 2 (fun R : Matrix (Fin m) (Fin m) ℝ => precisionIntegral lam R⁻¹) (line 0) := by
      rw [hl0]
      exact hJ.comp 1 (contDiffAt_matrixInverse_one.of_le (by simp))
    simpa only [psi, Function.comp_def] using hJR.comp 0 hl.contDiffAt
  have hcn : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ c t := by
    filter_upwards [hcC.eventually (by norm_num)] with t ht
    exact ht.differentiableAt (by norm_num)
  have hpn : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ psi t := by
    filter_upwards [hpC.eventually (by norm_num)] with t ht
    exact ht.differentiableAt (by norm_num)
  have hc1 : HasDerivAt c 0 0 := by
    simpa [c,line,htr] using hasDerivAt_rhoPrefactor_covLine_zero A
  have hc2 : HasDerivAt (deriv c)
      (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ)*(A*A).trace/2) 0 := by
    simpa [c,line,htr,mul_div_assoc] using ds_hasDerivAt_deriv_rhoPrefactor_covLine_zero A
  have hp1 : HasDerivAt psi ((fderiv ℝ (precisionIntegral (m := m) lam) 1) (-A)) 0 :=
    hasDerivAt_precisionIntegral_inv_covLine_zero lam A
  have hp2 : HasDerivAt (deriv psi)
      (∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x*((quad A x)^2/4-quad (A*A) x)) 0 :=
    hasDerivAt_deriv_precisionComp_zero lam A
  have hh := second_product_zero_left hc1 hp1 hc2 hp2 hcn hpn
  have he : (fun t : ℝ => rhoExpectation lam (1+t • A)) = fun t => c t*psi t := by
    ext t
    exact rhoExpectation_eq_precision lam (line t)
  rw [he]
  refine hh.congr_deriv ?_
  simp only [c,psi,hl0]
  rw [matrix_inv_one]
  exact precision_second_product_integral lam A

theorem second_fderiv_rhoExpectation_one_trace_zero
    (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (htr : A.trace=0) :
    (fderiv ℝ (fderiv ℝ (rhoExpectation (m := m) lam)) 1 A) A =
      2*(∫ x, Real.exp (lam*maxCoord x)*secondDensityCoeff A x) := by
  have hc := SimplexFull.Geometry.secondDeriv_line (v := A) (contDiffAt_rhoExpectation_one (m := m) lam)
  exact hc.symm.trans (hasDerivAt_deriv_rhoExpectation_covLine_zero_trace lam A htr).deriv

#print axioms second_fderiv_rhoExpectation_one_trace_zero

theorem second_fderiv_rhoExpectation_one_zeroDiagonal
    (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (hZ : SimplexFull.Geometry.zeroDiagonal A) :
    (fderiv ℝ (fderiv ℝ (rhoExpectation (m := m) lam)) 1 A) A =
      2*(∫ x, Real.exp (lam*maxCoord x)*secondDensityCoeff A x) := by
  apply second_fderiv_rhoExpectation_one_trace_zero lam A
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_eq_zero fun i _ => SimplexFull.Geometry.zeroDiagonal_apply hZ i

#print axioms second_fderiv_rhoExpectation_one_zeroDiagonal
end SimplexFull.Covariance