import SimplexFull.GaussianHessian
import SimplexFull.TaylorDefinitions
import SimplexFull.GaussianShift
import SimplexFull.SignalSmooth

/-!
First-order coefficient of simplex decoding success along the normal covariance
`R(τ) = κ(τ)² I + (1 - κ(τ)²) J`, with `κ = chartKappa`.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace SimplexFull.Geometry

variable {m : ℕ} [NeZero m]

/-- `R(τ) = κ(τ)² I + (1 - κ(τ)²) J`. -/
def normalR (m : ℕ) (tau : ℝ) : ShapeMatrix m :=
  (chartKappa m tau) ^ 2 • (1 : ShapeMatrix m) +
    (1 - (chartKappa m tau) ^ 2) • onesMatrix m

/-- Velocity `R'(0) = (J - I) / m`. -/
def normalVelocity (m : ℕ) : ShapeMatrix m :=
  (1 / (m : ℝ)) • (onesMatrix m - 1)

lemma chartKappa_zero (m : ℕ) : chartKappa m 0 = 1 := by
  simp [chartKappa]

lemma normalR_zero (m : ℕ) : normalR m 0 = 1 := by
  simp [normalR, chartKappa_zero]

lemma hasDerivAt_chartKappa (m : ℕ) (tau : ℝ) :
    HasDerivAt (chartKappa m) (-(1 / (2 * (m : ℝ)))) tau := by
  unfold chartKappa
  have hdiv : HasDerivAt (fun t : ℝ => t / (2 * (m : ℝ))) (1 / (2 * (m : ℝ))) tau := by
    simpa [div_eq_mul_inv, one_div] using
      (hasDerivAt_id tau).mul_const ((2 * (m : ℝ))⁻¹)
  exact ((hasDerivAt_const tau (1 : ℝ)).sub hdiv).congr_deriv (by ring)

lemma hasDerivAt_chartKappa_sq_zero :
    HasDerivAt (fun tau : ℝ => (chartKappa m tau) ^ 2) (-(1 / (m : ℝ))) 0 := by
  have hmul := (hasDerivAt_chartKappa m 0).mul (hasDerivAt_chartKappa m 0)
  have hfun : (fun tau : ℝ => chartKappa m tau * chartKappa m tau) =
      fun tau : ℝ => (chartKappa m tau) ^ 2 := by
    funext tau
    ring
  rw [← hfun]
  exact hmul.congr_deriv (by rw [chartKappa_zero]; ring)

lemma hasDerivAt_normalR_zero :
    HasDerivAt (normalR m) (normalVelocity m) 0 := by
  have hu := hasDerivAt_chartKappa_sq_zero (m := m)
  have hI := hu.smul_const (1 : ShapeMatrix m)
  have hsub : HasDerivAt (fun tau : ℝ => 1 - (chartKappa m tau) ^ 2) (1 / (m : ℝ)) 0 := by
    exact ((hasDerivAt_const 0 (1 : ℝ)).sub hu).congr_deriv (by ring)
  have hJ := hsub.smul_const (onesMatrix m)
  exact (hI.add hJ).congr_deriv <| by
    ext i j
    simp [normalVelocity, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

lemma zeroDiagonal_normalVelocity :
    zeroDiagonal (normalVelocity m) := by
  intro i
  simp [normalVelocity, Matrix.smul_apply, Matrix.sub_apply, onesMatrix, smul_eq_mul]

lemma entrySum_onesMatrix_sub_one :
    entrySum (onesMatrix m - (1 : ShapeMatrix m)) = (m : ℝ) * ((m : ℝ) - 1) := by
  unfold entrySum
  simp only [Matrix.sub_apply, onesMatrix, Matrix.one_apply]
  have hrow : ∀ i : Fin m, ∑ j : Fin m, ((1 : ℝ) - if i = j then 1 else 0) = (m : ℝ) - 1 := by
    intro i
    rw [Finset.sum_sub_distrib, sum_const_fin]
    have hdiag : ∑ j : Fin m, (if i = j then (1 : ℝ) else 0) = 1 := by
      simp only [eq_comm]
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    rw [hdiag]
    ring
  simp only [hrow, sum_const_fin]

lemma entrySum_smul (c : ℝ) (A : ShapeMatrix m) :
    entrySum (c • A) = c * entrySum A := by
  unfold entrySum
  simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma halfEntrySum_normalVelocity :
    halfEntrySum (normalVelocity m) = ((m : ℝ) - 1) / 2 := by
  rw [halfEntrySum, normalVelocity, entrySum_smul, entrySum_onesMatrix_sub_one]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  field_simp [hm]

open SimplexFull.Covariance

theorem hasDerivAt_extendedLoss_normalR (hm : 2 ≤ m) {mu : ℝ} (hmu : 0 < mu) :
    HasDerivAt (fun tau : ℝ => extendedLoss mu (normalR m tau))
      (gaussianC m mu * ((m : ℝ) - 1) / 2) 0 := by
  have hdiff : DifferentiableAt ℝ (extendedLoss (m := m) mu) (normalR m 0) := by
    rw [normalR_zero]
    exact (contDiffAt_extendedLoss_one mu).differentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0)
  refine (hdiff.hasFDerivAt.comp_hasDerivAt 0 hasDerivAt_normalR_zero).congr_deriv ?_
  rw [normalR_zero, fderiv_extendedLoss_one_coefficient hm hmu zeroDiagonal_normalVelocity,
    halfEntrySum_normalVelocity]
  ring

#print axioms hasDerivAt_extendedLoss_normalR



lemma simplexSuccess_eq_decoding_one (hm : 1 < m) (lam : ℝ) :
    simplexSuccess m lam = SimplexFull.decodingSuccess (1:ShapeMatrix m) (muFromSNR m lam) := by
  have hh := SimplexFull.decodingSuccess_independenceCov (simplexGram m)
    SimplexFull.simplexGram_posSemidef (muFromSNR m lam)
  have hmat : alpha m • simplexGram m+(m:ℝ)⁻¹ • onesMatrix m = (1:ShapeMatrix m) := by
    rw [simplexGram, smul_smul, mul_inv_cancel₀ (alpha_ne_zero_of_gt_one m hm),
      one_smul, centering, sub_add_cancel]
  rw [hmat, muFromSNR_mul_sqrt hm lam] at hh
  exact hh.symm

lemma extendedLoss_normalR_eq_deficit (hm : 1 < m) (lam tau : ℝ)
    (ht : 0 ≤ tau) (hu : tau < 2*(m:ℝ)) :
    extendedLoss (muFromSNR m lam) (normalR m tau) =
      simplexSuccess m lam-simplexSuccess m (lam*chartKappa m tau) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hd : 0 < 2*(m:ℝ) := by positivity
  have hk : 0 < chartKappa m tau := by
    unfold chartKappa
    have hh := (div_lt_one hd).mpr hu
    linarith
  have hk1 : chartKappa m tau ≤ 1 := by
    unfold chartKappa
    exact sub_le_self _ (div_nonneg ht hd.le)
  have hs : 0 ≤ 1-(chartKappa m tau)^2 := by nlinarith
  have hR : (normalR m tau).PosDef :=
    (Matrix.PosDef.one.smul (sq_pos_of_pos hk)).add_posSemidef
      (SimplexFull.posSemidef_onesMatrix.smul hs)
  rw [extendedLoss_eq_decodingDeficit _ _ hR]
  rw [simplexSuccess_eq_decoding_one hm lam, simplexSuccess_eq_decoding_one hm (lam*chartKappa m tau)]
  unfold normalR
  rw [SimplexFull.decodingSuccess_normalScale _ Matrix.PosDef.one.posSemidef hk.le hk1]
  congr 2
  unfold muFromSNR
  ring
#print axioms extendedLoss_normalR_eq_deficit

lemma hasDerivAt_simplex_normal_deficit (hm : 3 ≤ m) (lam : ℝ) :
    HasDerivAt (fun tau : ℝ => simplexSuccess m lam-
      simplexSuccess m (lam*chartKappa m tau))
      (lam*deriv (simplexSuccess m) lam/(2*(m:ℝ))) 0 := by
  have hd : DifferentiableAt ℝ (simplexSuccess m) lam :=
    SimplexFull.differentiableAt_simplexSuccess hm lam
  have hk : HasDerivAt (fun tau : ℝ => lam*chartKappa m tau)
      (-lam/(2*(m:ℝ))) 0 := by
    convert (hasDerivAt_chartKappa m 0).const_mul lam using 1 <;> first | rfl | ring
  have hp : HasDerivAt (simplexSuccess m) (deriv (simplexSuccess m) lam)
      (lam*chartKappa m 0) := by simpa [chartKappa_zero] using hd.hasDerivAt
  have hc := (hasDerivAt_const 0 (simplexSuccess m lam)).sub (hp.comp 0 hk)
  exact hc.congr_deriv (by ring)

open Filter Set Topology in
/-- The quadratic coefficient in the exact normal minimum equals the actual
normal curvature. The conversion mu=lambda/sqrt(alpha) contributes no extra factor. -/
theorem simplex_quadratic_coefficient_eq_normal_curvature (hm : 3 ≤ m)
    {lam : ℝ} (hlam : 0 < lam) :
    lam*deriv (simplexSuccess m) lam/(2*(m:ℝ)) =
      ((m:ℝ)-1)/2*gaussianC m (muFromSNR m lam) := by
  have hm1 : 1 < m := by omega
  have hmu := muFromSNR_pos hm1 hlam
  have hL := hasDerivAt_extendedLoss_normalR (by omega : 2 ≤ m) hmu
  have hD := hasDerivAt_simplex_normal_deficit hm lam
  have hpos : (0:ℝ) < 2*(m:ℝ) := by positivity
  have heq : (fun tau : ℝ => extendedLoss (muFromSNR m lam) (normalR m tau))
      =ᶠ[𝓝[Ici 0] 0] (fun tau => simplexSuccess m lam-simplexSuccess m (lam*chartKappa m tau)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds] with tau ht hu
    exact extendedLoss_normalR_eq_deficit hm1 lam tau ht hu
  have hh := hD.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq (by simp : (0:ℝ) ∈ Ici (0:ℝ))
  have h1 := hh.derivWithin (uniqueDiffWithinAt_Ici 0)
  have h2 := hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  rw [h2] at h1
  linarith
#print axioms simplex_quadratic_coefficient_eq_normal_curvature
end SimplexFull.Geometry