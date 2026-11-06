import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
import SimplexFull.Mills
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set
namespace SimplexFull.GlobalScalar

/-- The manuscript's Psi composed with the actual Gaussian H. -/
def psiPull (s : Real) : Real := Real.log (Phi s) + q s ^ 2 / 2

theorem hasDerivAt_psiPull (s : Real) :
    HasDerivAt psiPull (q s * sigma s) s := by
  unfold psiPull
  refine (((hasDerivAt_Phi s).log (ne_of_gt (Phi_pos s))).add
    (((hasDerivAt_q s).pow 2).div_const 2)).congr_deriv ?_
  dsimp [sigma, q]
  ring

theorem deriv_psiPull (s : Real) : deriv psiPull s = q s * sigma s :=
  (hasDerivAt_psiPull s).deriv

theorem strictMono_psiPull : StrictMono psiPull := by
  apply strictMono_of_deriv_pos
  intro s
  rw [deriv_psiPull]
  exact mul_pos (q_pos s) (sigma_pos s)

theorem continuous_psiPull : Continuous psiPull := by
  have hd : Differentiable Real psiPull := fun s => (hasDerivAt_psiPull s).differentiableAt
  exact hd.continuous

/-- A direct left-tail bound from the strictly positive conditional variance. -/
theorem h_lt_inv_neg {s : Real} (hs : s < 0) : h s < 1 / (-s) := by
  apply (lt_div_iff₀ (neg_pos.mpr hs)).2
  have hv := sigma_pos s
  have he : q s = h s - s := by simp [h]
  dsimp [sigma] at hv
  rw [he] at hv
  nlinarith [sq_nonneg (h s)]

#print axioms hasDerivAt_psiPull
#print axioms strictMono_psiPull
#print axioms h_lt_inv_neg

/-- H has exactly the positive real numbers as its range. -/
theorem exists_h_eq {y : Real} (hy : 0 < y) : ∃ s : Real, h s = y := by
  have hl : h (-(y⁻¹)) < y := by
    have hb := h_lt_inv_neg (neg_neg_of_pos (inv_pos.mpr hy))
    simpa using hb
  have hr : y < h y := by
    dsimp [h]
    linarith [q_pos y]
  exact intermediate_value_univ (-(y⁻¹)) y continuous_h ⟨hl.le, hr.le⟩

#print axioms exists_h_eq

/-- The actual inverse of H on the positive half-line. -/
def hInv : Real → Real := Function.invFun h

theorem h_hInv {y : Real} (hy : 0 < y) : h (hInv y) = y :=
  Function.invFun_eq (exists_h_eq hy)

theorem hInv_h (s : Real) : hInv (h s) = s :=
  Function.leftInverse_invFun strictMono_h.injective s

theorem strictMonoOn_hInv : StrictMonoOn hInv (Ioi (0 : Real)) := by
  intro x hx y hy hxy
  apply strictMono_h.lt_iff_lt.mp
  simpa only [h_hInv hx, h_hInv hy] using hxy

theorem image_hInv_Ioi : hInv '' Ioi (0 : Real) = univ := by
  apply Set.eq_univ_of_forall
  intro s
  exact ⟨h s, h_pos s, hInv_h s⟩

theorem continuousAt_hInv {y : Real} (hy : 0 < y) : ContinuousAt hInv y := by
  apply strictMonoOn_hInv.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hy)
  rw [image_hInv_Ioi]
  exact Filter.univ_mem

theorem hasDerivAt_hInv {y : Real} (hy : 0 < y) :
    HasDerivAt hInv (sigma (hInv y))⁻¹ y := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_hInv hy)
    (hasDerivAt_h (hInv y)) (ne_of_gt (sigma_pos (hInv y)))
  filter_upwards [Ioi_mem_nhds hy] with t ht using h_hInv ht

/-- The paper's actual scalar Psi; its intended domain is y>0. -/
def Psi (y : Real) : Real := psiPull (hInv y)

theorem Psi_h (s : Real) : Psi (h s) = psiPull s := by simp [Psi, hInv_h]

theorem hasDerivAt_Psi {y : Real} (hy : 0 < y) :
    HasDerivAt Psi (q (hInv y)) y := by
  unfold Psi
  refine ((hasDerivAt_psiPull (hInv y)).comp y (hasDerivAt_hInv hy)).congr_deriv ?_
  field_simp [ne_of_gt (sigma_pos (hInv y))]

#print axioms hasDerivAt_hInv
#print axioms hasDerivAt_Psi
end SimplexFull.GlobalScalar
