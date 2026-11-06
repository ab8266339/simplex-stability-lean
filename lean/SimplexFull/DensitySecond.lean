import SimplexFull.DensityPrefactorSecond

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix ContinuousLinearMap Filter
open scoped BigOperators Matrix.Norms.L2Operator Real Polynomial Topology
namespace SimplexFull.Covariance
variable {m : ℕ}

lemma ds_hasDerivAt_quad_inv_covLine (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) {t : ℝ}
    (ht : ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0) :
    HasDerivAt (fun s : ℝ => quad (((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) x)
      (-quad ((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
        (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) x) t := by
  have hB := hasDerivAt_inv_covLine A ht
  have hcomp :=
    ((quadLinearMap x).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hB
  have hquad : quad (-((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
      (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹))) x =
      -quad ((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
        (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) x := by
    rw [show -((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
      (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) =
        (-1 : ℝ) • ((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
          (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) by simp,
      quad_smul, neg_one_mul]
  have h := by
    simpa [quadLinearMap, LinearMap.coe_toContinuousLinearMap, hquad] using hcomp
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp [Function.comp_apply]

theorem ds_hasDerivAt_deriv_quad_inv_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
        quad (((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) x) t)
      (2 * quad (A * A) x) 0 := by
  let B : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹
  have h2 : HasDerivAt (fun t => deriv B t) ((2 : ℝ) • (A * A)) 0 := by
    simpa [B] using hasDerivAt_deriv_inverse_covLine_zero A
  have hg : HasDerivAt (fun t => quad (deriv B t) x) (2 * quad (A * A) x) 0 := by
    have hcomp :=
      ((quadLinearMap x).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 h2
    have hquad : quad ((2 : ℝ) • (A * A)) x = 2 * quad (A * A) x := quad_smul _ _ _
    have h := by
      simpa [quadLinearMap, LinearMap.coe_toContinuousLinearMap, hquad] using hcomp
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [Function.comp_apply]
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0 :=
    ((contDiff_det_line A).continuous.tendsto 0).eventually_ne (by simp)
  have he : (fun t => deriv (fun s => quad (B s) x) t) =ᶠ[𝓝 (0 : ℝ)]
      fun t => quad (deriv B t) x := by
    refine hn.mono fun t ht => ?_
    have hB := hasDerivAt_inv_covLine A ht
    have hdB : deriv B t = -(B t * A * B t) := by simpa [B] using hB.deriv
    have hdQ := (ds_hasDerivAt_quad_inv_covLine A x ht).deriv
    have hQ : -quad (B t * A * B t) x = quad (deriv B t) x := by
      rw [hdB, show -(B t * A * B t) = (-1 : ℝ) • (B t * A * B t) by simp, quad_smul, neg_one_mul]
    simpa [B, hQ] using hdQ
  simpa [B] using hg.congr_of_eventuallyEq he

lemma ds_hasDerivAt_expNegQuad_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => Real.exp
        (-quad (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) x / 2))
      (Real.exp (-‖x‖ ^ 2 / 2) * (quad A x / 2)) 0 := by
  have hq := hasDerivAt_quad_inv_covLine_zero A x
  refine ((hq.neg.div_const (2 : ℝ)).exp).congr_deriv ?_
  simp only [matrix_inv_one, zero_smul, add_zero, quad_one, neg_neg, Pi.neg_apply]

theorem ds_hasDerivAt_deriv_expNegQuad_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => Real.exp
        (-quad (((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹) x / 2)) t)
      (Real.exp (-‖x‖ ^ 2 / 2) * ((quad A x) ^ 2 / 4 - quad (A * A) x)) 0 := by
  let q : ℝ → ℝ := fun t => quad (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) x
  let e : ℝ → ℝ := fun t => Real.exp (-q t / 2)
  have hv : HasDerivAt (fun t => -(deriv q t) / 2) (-quad (A * A) x) 0 := by
    refine ((ds_hasDerivAt_deriv_quad_inv_covLine_zero A x).neg.div_const (2 : ℝ)).congr_deriv ?_
    ring
  have he1 : HasDerivAt e (Real.exp (-‖x‖ ^ 2 / 2) * (quad A x / 2)) 0 := by
    simpa [e, q] using ds_hasDerivAt_expNegQuad_covLine_zero A x
  have hprod := he1.mul hv
  have hg : HasDerivAt (fun t => e t * (-(deriv q t) / 2))
      (Real.exp (-‖x‖ ^ 2 / 2) * ((quad A x) ^ 2 / 4 - quad (A * A) x)) 0 := by
    refine hprod.congr_deriv ?_
    have hdq : deriv q 0 = -quad A x := by
      simpa [q] using (hasDerivAt_quad_inv_covLine_zero A x).deriv
    have he0 : e 0 = Real.exp (-‖x‖ ^ 2 / 2) := by
      simp [e, q, matrix_inv_one, zero_smul, add_zero, quad_one]
    rw [hdq, he0]
    ring
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0 :=
    ((contDiff_det_line A).continuous.tendsto 0).eventually_ne (by simp)
  have heq : (fun t => deriv e t) =ᶠ[𝓝 (0 : ℝ)] fun t => e t * (-(deriv q t) / 2) := by
    refine hn.mono fun t ht => ?_
    have hq := ds_hasDerivAt_quad_inv_covLine A x ht
    have hexp := (hq.neg.div_const (2 : ℝ)).exp
    have hdq : deriv q t =
        -quad ((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
          (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) x := by
      simpa [q] using hq.deriv
    have hde : deriv e t = e t *
        (quad ((((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) * A *
          (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) x / 2) := by
      simpa [e, q, neg_neg] using hexp.deriv
    change deriv e t = e t * (-deriv q t / 2)
    rw [hde, hdq]
    ring
  simpa [e, q] using hg.congr_of_eventuallyEq heq

theorem hasDerivAt_deriv_rho_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
        rho ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A) x) t)
      (rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
        ((quad A x - A.trace) ^ 2 / 4 + (A * A).trace / 2 - quad (A * A) x)) 0 := by
  let c : ℝ → ℝ := fun t => rhoPrefactor ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)
  let q : ℝ → ℝ := fun t => quad (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) x
  let e : ℝ → ℝ := fun t => Real.exp (-q t / 2)
  have hc1 : HasDerivAt c (-rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2) 0 := by
    simpa [c] using hasDerivAt_rhoPrefactor_covLine_zero A
  have hc2 : HasDerivAt (fun t => deriv c t)
      (rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) *
        ((A * A).trace / 2 + A.trace ^ 2 / 4)) 0 := by
    simpa [c] using ds_hasDerivAt_deriv_rhoPrefactor_covLine_zero A
  have he1 : HasDerivAt e (Real.exp (-‖x‖ ^ 2 / 2) * (quad A x / 2)) 0 := by
    simpa [e, q] using ds_hasDerivAt_expNegQuad_covLine_zero A x
  have he2 : HasDerivAt (fun t => deriv e t)
      (Real.exp (-‖x‖ ^ 2 / 2) * ((quad A x) ^ 2 / 4 - quad (A * A) x)) 0 := by
    simpa [e, q] using ds_hasDerivAt_deriv_expNegQuad_covLine_zero A x
  have hsum := (hc2.mul he1).add (hc1.mul he2)
  have hg : HasDerivAt (fun t => deriv c t * e t + c t * deriv e t)
      (rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
        ((quad A x - A.trace) ^ 2 / 4 + (A * A).trace / 2 - quad (A * A) x)) 0 := by
    refine hsum.congr_deriv ?_
    have hdc : deriv c 0 = -rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * A.trace / 2 :=
      hc1.deriv
    have hde : deriv e 0 = Real.exp (-‖x‖ ^ 2 / 2) * (quad A x / 2) := he1.deriv
    have he0 : e 0 = Real.exp (-‖x‖ ^ 2 / 2) := by
      simp [e, q, matrix_inv_one, zero_smul, add_zero, quad_one]
    have hc0 : c 0 = rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) := by
      simp [c, rhoPrefactor, Matrix.det_one, zero_smul, add_zero, mul_one]
    have hrho : rho (1 : Matrix (Fin m) (Fin m) ℝ) x =
        rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ) * Real.exp (-‖x‖ ^ 2 / 2) := by
      simp [rho, rhoPrefactor, Matrix.det_one, matrix_inv_one, quad_one, mul_one]
    rw [hdc, hde, he0, hc0, hrho]
    ring
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det :=
    ((contDiff_det_line A).continuous.tendsto 0).eventually (eventually_gt_nhds (by simp))
  have heq : (fun t => deriv (fun s => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A) x) t)
      =ᶠ[𝓝 (0 : ℝ)] fun t => deriv c t * e t + c t * deriv e t := by
    refine hn.mono fun t ht => ?_
    have hc := ds_hasDerivAt_rhoPrefactor_covLine A ht
    have hq := ds_hasDerivAt_quad_inv_covLine A x ht.ne'
    have hexp := (hq.neg.div_const (2 : ℝ)).exp
    have hmul := hc.mul hexp
    have h := hmul.deriv
    rw [← hc.deriv, ← hexp.deriv] at h
    simpa [c, e, q, rho, rhoPrefactor, Pi.mul_def, Pi.neg_def] using h
  exact hg.congr_of_eventuallyEq heq

theorem iteratedDeriv_two_rho_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    iteratedDeriv 2 (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) 0 =
      rho (1 : Matrix (Fin m) (Fin m) ℝ) x *
        ((quad A x - A.trace) ^ 2 / 4 + (A * A).trace / 2 - quad (A * A) x) := by
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using
    (hasDerivAt_deriv_rho_covLine_zero A x).deriv

theorem iteratedDeriv_two_rho_covLine_zero_of_trace_eq_zero [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) (hA : A.trace = 0) :
    iteratedDeriv 2 (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) 0 =
      2 * secondDensityCoeff A x := by
  rw [iteratedDeriv_two_rho_covLine_zero, secondDensityCoeff, hA]
  ring

set_option pp.fullNames true in
#print axioms hasDerivAt_deriv_rho_covLine_zero
#print axioms iteratedDeriv_two_rho_covLine_zero
#print axioms iteratedDeriv_two_rho_covLine_zero_of_trace_eq_zero

end SimplexFull.Covariance
