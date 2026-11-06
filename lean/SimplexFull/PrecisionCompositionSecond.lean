import SimplexFull.PrecisionGaussian
import SimplexFull.GaussianDifferentiation
import SimplexFull.GaussianPolynomial
import SimplexFull.DensityInverseSecond
import SimplexFull.SecondChain

/-!
# Second covariance derivative of the tilted Gaussian integral

The precision-integral Hessian is the integral of `precisionD2`. At the identity,
the second derivative of `J` along `t ↦ (I + t A)⁻¹` is the integral of the
quadratic precision kernel.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Matrix Filter ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology

namespace SimplexFull.Covariance

variable {m : ℕ}

local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup
    (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ
    (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

variable [NeZero m]

omit [NeZero m] in
lemma norm_sub_one_le_of_mem_precisionBall {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Metric.ball 1 (1 / 2)) : ‖M - 1‖ ≤ 1 / 2 :=
  (show ‖M - 1‖ < 1 / 2 by simpa only [Metric.mem_ball, dist_eq_norm] using hM).le

lemma integrable_precisionD2_of_close (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M - 1‖ ≤ 1 / 2) : Integrable (precisionD2 (m := m) lam M) := by
  refine (integrable_precisionBound (m := m) 4 lam).mono'
    ((continuous_precisionD2 lam M).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  simpa [precisionBound] using precisionD2_bound lam hM x

lemma precisionD2_apply (lam : ℝ) (M A B : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    (precisionD2 lam M x A) B =
      precisionKernel lam M x * quad A x * quad B x / 4 := by
  simp only [precisionD2, precisionLinear, smulRight_apply, _root_.smul_apply, smul_eq_mul,
    quadCLM_apply]
  ring

/-- Second Fréchet derivative of the precision integral, evaluated on a pair of directions. -/
theorem second_fderiv_precisionIntegral_apply (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Metric.ball 1 (1 / 2)) (A B : Matrix (Fin m) (Fin m) ℝ) :
    ((fderiv ℝ (fderiv ℝ (precisionIntegral (m := m) lam)) M) A) B =
      ∫ x, precisionKernel lam M x * quad A x * quad B x / 4 := by
  have hD2 : Integrable (precisionD2 (m := m) lam M) :=
    integrable_precisionD2_of_close lam (norm_sub_one_le_of_mem_precisionBall hM)
  rw [second_fderiv_precisionIntegral lam hM]
  rw [ContinuousLinearMap.integral_apply hD2 A]
  have hD2A : Integrable (fun x => precisionD2 lam M x A) := hD2.apply_continuousLinearMap A
  rw [ContinuousLinearMap.integral_apply hD2A B]
  exact integral_congr_ae (ae_of_all _ fun x => precisionD2_apply lam M A B x)

/-- On the precision ball the derivative of `J` is itself `C¹`, with derivative `∫ precisionD2`. -/
theorem hasFDerivAt_fderiv_precisionIntegral (lam : ℝ) {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Metric.ball 1 (1 / 2)) :
    HasFDerivAt (fderiv ℝ (precisionIntegral (m := m) lam))
      (∫ x, precisionD2 (m := m) lam M x) M := by
  have hC2 : ContDiffAt ℝ 2 (precisionIntegral (m := m) lam) M :=
    (contDiffOn_precisionIntegral lam).contDiffAt (Metric.isOpen_ball.mem_nhds hM)
  have hC1 : ContDiffAt ℝ 1 (fderiv ℝ (precisionIntegral (m := m) lam)) M := by
    simpa using hC2.fderiv_right (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hd : DifferentiableAt ℝ (fderiv ℝ (precisionIntegral (m := m) lam)) M :=
    hC1.differentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)
  rw [← second_fderiv_precisionIntegral lam hM]
  exact hd.hasFDerivAt

omit [NeZero m] in
lemma quad_neg (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    quad (-A) x = -quad A x := by
  rw [show -A = (-1 : ℝ) • A by simp, quad_smul]
  ring

lemma fderiv_precisionIntegral_one_apply (lam : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    (fderiv ℝ (precisionIntegral (m := m) lam) (1 : Matrix (Fin m) (Fin m) ℝ)) B =
      ∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * ((-1 / 2) * quad B x) := by
  rw [fderiv_precisionIntegral lam (one_mem_precisionBall (m := m)),
    ContinuousLinearMap.integral_apply (integrable_precisionD1_one lam) B]
  exact integral_congr_ae (ae_of_all _ fun x => precisionD1_one_apply lam B x)

lemma hasDerivAt_deriv_precisionComp_zero (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (deriv (fun t : ℝ =>
        precisionIntegral lam (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)))
      (∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x *
        ((quad A x) ^ 2 / 4 - quad (A * A) x)) 0 := by
  let M : ℝ → Matrix (Fin m) (Fin m) ℝ := fun t => (1 + t • A)⁻¹
  let J : Matrix (Fin m) (Fin m) ℝ → ℝ := precisionIntegral (m := m) lam
  let ψ : ℝ → ℝ := fun t => J (M t)
  let L : ℝ → Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ := fun t => fderiv ℝ J (M t)
  let v : ℝ → Matrix (Fin m) (Fin m) ℝ := deriv M
  have hball := one_mem_precisionBall (m := m)
  have hM0 : HasDerivAt M (-A) 0 := hasDerivAt_inverse_covLine_at_zero A
  have hv0 : HasDerivAt v ((2 : ℝ) • (A * A)) 0 := by
    have hfun : (fun t : ℝ => deriv
        (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) t) = v := by
      funext t
      rfl
    rw [← hfun]
    exact hasDerivAt_deriv_inverse_covLine_zero A
  have hL : HasDerivAt L
      (((∫ x, precisionD2 lam (1 : Matrix (Fin m) (Fin m) ℝ) x) (-A))) 0 := by
    have hF := hasFDerivAt_fderiv_precisionIntegral lam hball
    have hcomp := hF.comp_hasDerivAt_of_eq 0 hM0 (by simp [M])
    have hfun : fderiv ℝ (precisionIntegral (m := m) lam) ∘ M = L := by
      funext t
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have happ : HasDerivAt (fun t => L t (v t))
      ((((∫ x, precisionD2 lam (1 : Matrix (Fin m) (Fin m) ℝ) x) (-A)) (v 0)) +
        (L 0) ((2 : ℝ) • (A * A))) 0 := hL.clm_apply hv0
  have hv0val : v 0 = -A := by
    have hv : v 0 = deriv M 0 := rfl
    rw [hv]
    exact hM0.deriv
  have hL0 : L 0 = fderiv ℝ J (1 : Matrix (Fin m) (Fin m) ℝ) := by
    simp only [L]
    rw [show M 0 = 1 by simp [M]]
  have hsq : ((∫ x, precisionD2 lam (1 : Matrix (Fin m) (Fin m) ℝ) x) (-A)) (-A) =
      ∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x) ^ 2 / 4 := by
    have happly := second_fderiv_precisionIntegral_apply lam hball (-A) (-A)
    rw [second_fderiv_precisionIntegral lam hball] at happly
    rw [happly]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    simp only [quad_neg]
    ring
  have hlin : (fderiv ℝ J (1 : Matrix (Fin m) (Fin m) ℝ)) ((2 : ℝ) • (A * A)) =
      ∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (-quad (A * A) x) := by
    rw [fderiv_precisionIntegral_one_apply]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [quad_smul]
    ring
  have hval :
      (((∫ x, precisionD2 lam (1 : Matrix (Fin m) (Fin m) ℝ) x) (-A)) (v 0)) +
        (L 0) ((2 : ℝ) • (A * A)) =
      ∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x *
        ((quad A x) ^ 2 / 4 - quad (A * A) x) := by
    rw [hv0val, hL0, hsq, hlin, ← integral_add]
    · refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      ring
    · have hD2 := integrable_precisionD2_of_close lam
        (by simp : ‖(1 : Matrix (Fin m) (Fin m) ℝ) - 1‖ ≤ 1 / 2)
      have happ2 := (hD2.apply_continuousLinearMap (-A)).apply_continuousLinearMap (-A)
      convert happ2 using 1
      ext x
      have h := precisionD2_apply lam (1 : Matrix (Fin m) (Fin m) ℝ) (-A) (-A) x
      simp only [quad_neg] at h
      rw [h]
      ring
    · have hD1 := (integrable_precisionD1_one lam).apply_continuousLinearMap ((2 : ℝ) • (A * A))
      convert hD1 using 1
      ext x
      rw [precisionD1_one_apply, quad_smul]
      ring
  rw [hval] at happ
  have hdet : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0 :=
    ((contDiff_det_line A).continuous.tendsto 0).eventually_ne (by simp)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), M t ∈ Metric.ball 1 (1 / 2) := by
    have h0 : M 0 = 1 := by simp [M]
    have htend := hM0.continuousAt.tendsto
    rw [h0] at htend
    exact htend.eventually (Metric.isOpen_ball.mem_nhds hball)
  have hchain : deriv (fun t : ℝ =>
        precisionIntegral lam (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => L t (v t) := by
    filter_upwards [hdet, hmem] with t ht htb
    have hinv := hasDerivAt_inv_covLine A ht
    have hJ : HasFDerivAt J (fderiv ℝ J (M t)) (M t) :=
      (((contDiffOn_precisionIntegral lam).contDiffAt
        (Metric.isOpen_ball.mem_nhds htb)).differentiableAt
        (by simp : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
    have hcomp := hJ.comp_hasDerivAt t hinv
    have hd := hcomp.deriv
    have hcomp_fun :
        J ∘ (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) = ψ := by
      funext s
      rfl
    rw [hcomp_fun] at hd
    rw [← hinv.deriv] at hd
    have hv : v t = deriv (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) t := rfl
    have hLt : L t = fderiv ℝ J (M t) := rfl
    rw [← hv, ← hLt] at hd
    have hψ : ψ = fun s : ℝ =>
        precisionIntegral lam (((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) := by
      funext s
      rfl
    rw [hψ] at hd
    exact hd
  exact happ.congr_of_eventuallyEq hchain


#print axioms hasDerivAt_deriv_precisionComp_zero
end SimplexFull.Covariance