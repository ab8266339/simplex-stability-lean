import SimplexFull.GaussianSmooth
import SimplexFull.PrecisionGaussian
import SimplexFull.DensityDerivatives
import SimplexFull.GaussianPolynomial

/-!
# Covariance derivatives of the tilted Gaussian integral

`rhoExpectation lam` at the identity, differentiated in a matrix direction `A`.
The factorization `F(R) = rhoPrefactor R * precisionIntegral lam R⁻¹` reduces the
first derivative to the product rule along the line `t ↦ I + t A`.
-/

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

/-- `(I + t A)⁻¹` has derivative `-A` at `t = 0`. -/
lemma hasDerivAt_inv_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) (-A) 0 := by
  have hline : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) A 0 :=
    hasDerivAt_covLine A 0
  have hinv : HasFDerivAt Ring.inverse
      (-mulLeftRight ℝ (Matrix (Fin m) (Fin m) ℝ)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹))
      (1 : Matrix (Fin m) (Fin m) ℝ) :=
    hasFDerivAt_ringInverse (1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)
  have hcomp := hinv.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hderiv :
      (-mulLeftRight ℝ (Matrix (Fin m) (Fin m) ℝ)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹)) A = -A := by
    simp [mulLeftRight_apply, Units.val_one, inv_one, one_mul, mul_one]
  have hfun : (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) =
      Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A := by
    ext t
    simp [Matrix.nonsing_inv_eq_ringInverse]
  have hcomp' :
      HasDerivAt (Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) (-A) 0 := by
    simpa [hderiv] using hcomp
  rw [hfun]
  exact hcomp'

/-- Logarithmic derivative of the Gaussian prefactor along `t ↦ I + t A` at `t = 0`. -/
lemma hasDerivAt_rhoPrefactor_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A))
      (-rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2) 0 := by
  have hk : 0 < (2 * Real.pi) ^ m := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  have hd := hasDerivAt_det_covLine_zero A
  have hu := hd.const_mul ((2 * Real.pi) ^ m)
  have hu0 : (2 * Real.pi) ^ m *
      ((1 : Matrix (Fin m) (Fin m) ℝ) + (0 : ℝ) • A).det ≠ 0 := by
    simp [Matrix.det_one, hk.ne']
  have hs := hu.sqrt hu0
  have hs0 : Real.sqrt ((2 * Real.pi) ^ m *
      ((1 : Matrix (Fin m) (Fin m) ℝ) + (0 : ℝ) • A).det) ≠ 0 := by
    refine (Real.sqrt_pos.2 ?_).ne'
    simp [Matrix.det_one, hk]
  have ha := hs.inv hs0
  refine (ha.congr_of_eventuallyEq ?_).congr_deriv ?_
  · apply Eventually.of_forall
    intro t
    simp [rhoPrefactor]
  · simp only [Matrix.det_one, zero_smul, add_zero, mul_one, rhoPrefactor]
    have hs2 : Real.sqrt ((2 * Real.pi) ^ m) ^ 2 = (2 * Real.pi) ^ m := Real.sq_sqrt hk.le
    have hne : Real.sqrt ((2 * Real.pi) ^ m) ≠ 0 := (Real.sqrt_pos.2 hk).ne'
    field_simp [hne]
    rw [hs2]
    ring

lemma one_mem_precisionBall : (1 : Matrix (Fin m) (Fin m) ℝ) ∈ Metric.ball 1 (1 / 2) := by
  simp [Metric.mem_ball]

variable [NeZero m]

lemma integrable_precisionD1_one (lam : ℝ) :
    Integrable (precisionD1 (m := m) lam (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  refine (integrable_precisionBound (m := m) 2 lam).mono'
    ((continuous_precisionD1 lam (1 : Matrix (Fin m) (Fin m) ℝ)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  have hM : ‖(1 : Matrix (Fin m) (Fin m) ℝ) - 1‖ ≤ (1 : ℝ) / 2 := by simp
  simpa [precisionBound] using precisionD1_bound lam hM x

lemma precisionD1_one_apply (lam : ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    precisionD1 lam (1 : Matrix (Fin m) (Fin m) ℝ) x B =
      precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * ((-1 / 2) * quad B x) := by
  simp only [precisionD1, precisionLinear, _root_.smul_apply, smul_eq_mul, quadCLM_apply]

lemma precisionD1_one_apply_neg (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    precisionD1 lam (1 : Matrix (Fin m) (Fin m) ℝ) x (-A) =
      precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x / 2) := by
  rw [precisionD1_one_apply]
  have hquad : quad (-A) x = -quad A x := by
    rw [show -A = (-1 : ℝ) • A by simp, quad_smul]
    ring
  rw [hquad]
  ring

lemma integral_precisionD1_one_neg (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (∫ x, precisionD1 lam (1 : Matrix (Fin m) (Fin m) ℝ) x) (-A) =
      ∫ x, precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x / 2) := by
  rw [ContinuousLinearMap.integral_apply (integrable_precisionD1_one lam)]
  exact integral_congr_ae (ae_of_all _ fun x => precisionD1_one_apply_neg lam A x)

lemma rhoPrefactor_mul_precisionKernel_one (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
        precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x =
      Real.exp (lam * maxCoord x) * rho (1 : Matrix (Fin m) (Fin m) ℝ) x := by
  unfold precisionKernel
  rw [rho_one]
  have hlin : precisionLinear x (1 : Matrix (Fin m) (Fin m) ℝ) = -‖x‖ ^ 2 / 2 := by
    simp only [precisionLinear, _root_.smul_apply, smul_eq_mul, quadCLM_apply, quad_one]
    ring
  rw [hlin]
  have hc : rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) =
      (Real.sqrt ((2 * Real.pi) ^ m))⁻¹ := by
    simp [rhoPrefactor, Matrix.det_one]
  rw [hc]
  exact mul_left_comm _ _ _

lemma hasDerivAt_precisionIntegral_inv_covLine_zero (lam : ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ =>
        precisionIntegral lam (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹))
      ((fderiv ℝ (precisionIntegral (m := m) lam) (1 : Matrix (Fin m) (Fin m) ℝ)) (-A)) 0 := by
  have hJ : HasFDerivAt (precisionIntegral (m := m) lam)
      (fderiv ℝ (precisionIntegral (m := m) lam) (1 : Matrix (Fin m) (Fin m) ℝ))
      (1 : Matrix (Fin m) (Fin m) ℝ) :=
    ((contDiffAt_precisionIntegral_one (m := m) lam).differentiableAt
      (by simp : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hM := hasDerivAt_inv_covLine_zero A
  exact hJ.comp_hasDerivAt_of_eq 0 hM (by simp [zero_smul, add_zero])

/-- Derivative of `t ↦ rhoExpectation lam (I + t A)` at `t = 0`. -/
theorem hasDerivAt_rhoExpectation_covLine_zero (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => rhoExpectation lam ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A))
      (∫ x, Real.exp (lam * maxCoord x) * rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
        (quad A x - A.trace) / 2) 0 := by
  have hc := hasDerivAt_rhoPrefactor_covLine_zero A
  have hJ := hasDerivAt_precisionIntegral_inv_covLine_zero lam A
  have hprod := hc.mul hJ
  have hfun : (fun t : ℝ => rhoExpectation lam ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)) =
      fun t : ℝ => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) *
        precisionIntegral lam (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) := by
    ext t
    exact rhoExpectation_eq_precision lam _
  rw [hfun]
  refine hprod.congr_deriv ?_
  have hball := one_mem_precisionBall (m := m)
  rw [fderiv_precisionIntegral lam hball, integral_precisionD1_one_neg lam A]
  simp only [zero_smul, add_zero, matrix_inv_one]
  have hK : Integrable (precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ)) :=
    integrable_precisionKernel lam (by simp : ‖(1 : Matrix (Fin m) (Fin m) ℝ) - 1‖ ≤ 1 / 2)
  have hD1A : Integrable (fun x => precisionD1 lam (1 : Matrix (Fin m) (Fin m) ℝ) x (-A)) :=
    (integrable_precisionD1_one lam).apply_continuousLinearMap (-A)
  have hquad : Integrable (fun x =>
      precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x / 2)) := by
    convert hD1A using 1
    ext x
    exact (precisionD1_one_apply_neg lam A x).symm
  have hpref : Integrable (fun x =>
      (-rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2) *
        precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x) :=
    hK.const_mul (-rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2)
  have hscaled : Integrable (fun x =>
      rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
        (precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x / 2))) :=
    hquad.const_mul (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ))
  unfold precisionIntegral
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hpref hscaled]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hwk := rhoPrefactor_mul_precisionKernel_one lam x
  calc
    (-rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2) *
          precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x +
        rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
          (precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x / 2))
      = rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
          precisionKernel lam (1 : Matrix (Fin m) (Fin m) ℝ) x * ((quad A x - A.trace) / 2) := by
        ring
    _ = Real.exp (lam * maxCoord x) * rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
          ((quad A x - A.trace) / 2) := by rw [hwk]
    _ = Real.exp (lam * maxCoord x) * rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
          (quad A x - A.trace) / 2 := by ring

/-- Fréchet derivative of `rhoExpectation lam` at the identity covariance. -/
theorem fderiv_rhoExpectation_one (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (fderiv ℝ (rhoExpectation (m := m) lam) (1 : Matrix (Fin m) (Fin m) ℝ)) A =
      ∫ x, Real.exp (lam * maxCoord x) * rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
        (quad A x - A.trace) / 2 := by
  have hF : HasFDerivAt (rhoExpectation (m := m) lam)
      (fderiv ℝ (rhoExpectation (m := m) lam) (1 : Matrix (Fin m) (Fin m) ℝ))
      (1 : Matrix (Fin m) (Fin m) ℝ) :=
    ((contDiffAt_rhoExpectation_one (m := m) lam).differentiableAt
      (by simp : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) A 0 :=
    hasDerivAt_covLine A 0
  have hcomp := hF.comp_hasDerivAt_of_eq 0 hline (by simp [zero_smul, add_zero])
  have hdir := hasDerivAt_rhoExpectation_covLine_zero lam A
  exact hcomp.deriv.symm.trans hdir.deriv

#print axioms hasDerivAt_rhoExpectation_covLine_zero
#print axioms fderiv_rhoExpectation_one

end SimplexFull.Covariance
