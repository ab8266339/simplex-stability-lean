import SimplexFull.GlobalScalarCurvature
import Mathlib.Analysis.Convex.Deriv
noncomputable section
open Set
namespace SimplexFull.GlobalScalar

def regularizedPsi (y : Real) : Real := Psi y + M0 * y^2 / 2

theorem hasDerivAt_regularizedPsi {y : Real} (hy : 0 < y) :
    HasDerivAt regularizedPsi (deriv Psi y + M0*y) y := by
  unfold regularizedPsi
  refine ((hasDerivAt_Psi hy).add
    ((((hasDerivAt_id y).pow 2).const_mul M0).div_const 2)).congr_deriv ?_
  rw [(hasDerivAt_Psi hy).deriv]
  try dsimp only [id]
  ring

theorem hasDerivAt_regularizedPsi_slope {y : Real} (hy : 0 < y) :
    HasDerivAt (fun x => deriv Psi x + M0*x) (M0 - psiCurvature y) y := by
  refine ((hasDerivAt_deriv_Psi hy).add ((hasDerivAt_id y).const_mul M0)).congr_deriv ?_
  try dsimp only [id]
  ring

theorem convexOn_regularizedPsi : ConvexOn Real curvatureInterval regularizedPsi := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => deriv Psi x + M0*x)
    (f'' := fun x => M0 - psiCurvature x) (convex_Icc _ _)
  · intro x hx
    exact (hasDerivAt_regularizedPsi (curvatureInterval_pos hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_regularizedPsi (curvatureInterval_pos (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_regularizedPsi_slope (curvatureInterval_pos (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact sub_nonneg.mpr (psiCurvature_le_M0 (interior_subset hx))

/-- Actual second-order lower bound with the manuscript's fixed M0. -/
theorem Psi_taylor_lower {x y : Real} (hx : x ∈ curvatureInterval)
    (hy : y ∈ curvatureInterval) :
    Psi x + q (hInv x)*(y-x) - M0*(y-x)^2/2 ≤ Psi y := by
  have hd := hasDerivAt_regularizedPsi (curvatureInterval_pos hx)
  have hdx := (hasDerivAt_Psi (curvatureInterval_pos hx)).deriv
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hs := convexOn_regularizedPsi.le_slope_of_hasDerivAt hx hy hlt hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    rw [hdx] at hm
    dsimp [regularizedPsi] at hm
    nlinarith
  · subst y
    simp
  · have hs := convexOn_regularizedPsi.slope_le_of_hasDerivAt hy hx hgt hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    rw [hdx] at hm
    dsimp [regularizedPsi] at hm
    nlinarith

#print axioms Psi_taylor_lower

/-- The exact scalar Taylor estimate used in the centroid proof, with no free smoothness bound. -/
theorem centroid_scalar_taylor {c z : Real} (hc : c ∈ Icc (0 : Real) 1)
    (hz : |z| ≤ h 0 / 2) :
    Psi (h c) + q c*z - M0*z^2/2 ≤ Psi (h c+z) := by
  have hc0 : h 0 ≤ h c := strictMono_h.monotone hc.1
  have hc1 : h c ≤ h 1 := strictMono_h.monotone hc.2
  have h01 : h 0 ≤ h 1 := strictMono_h.monotone (by norm_num)
  have hp0 := h_pos 0
  have hp1 := h_pos 1
  have hx : h c ∈ curvatureInterval := by
    constructor <;> linarith
  have hy : h c+z ∈ curvatureInterval := by
    have hzl := (abs_le.mp hz).1
    have hzu := (abs_le.mp hz).2
    constructor <;> linarith
  simpa only [hInv_h, add_sub_cancel_left] using Psi_taylor_lower hx hy

#print axioms centroid_scalar_taylor
end SimplexFull.GlobalScalar
