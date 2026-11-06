import SimplexFull.GaussianBase
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Filter
namespace SimplexFull

theorem q_pos (c : ℝ) : 0 < q c := by
  unfold q
  exact div_pos (phi_pos c) (Phi_pos c)

theorem hasDerivAt_q (c : ℝ) : HasDerivAt q (-(q c * h c)) c := by
  have hΦ : Phi c ≠ 0 := (Phi_pos c).ne'
  have hderiv := (hasDerivAt_phi c).fun_div (hasDerivAt_Phi c) hΦ
  refine (hderiv.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  simp only [q, h]
  field_simp [hΦ]
  ring

theorem deriv_q (c : ℝ) : deriv q c = -(q c * h c) :=
  (hasDerivAt_q c).deriv

theorem differentiableAt_q (c : ℝ) : DifferentiableAt ℝ q c :=
  (hasDerivAt_q c).differentiableAt

theorem differentiable_q : Differentiable ℝ q := fun c => differentiableAt_q c

theorem continuous_q : Continuous q :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_q c).continuousAt

theorem hasDerivAt_h (c : ℝ) : HasDerivAt h (sigma c) c := by
  have hadd := (hasDerivAt_id' c).add (hasDerivAt_q c)
  refine (hadd.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · unfold sigma
    ring
  · unfold h
    rfl

theorem deriv_h (c : ℝ) : deriv h c = sigma c :=
  (hasDerivAt_h c).deriv

theorem differentiableAt_h (c : ℝ) : DifferentiableAt ℝ h c :=
  (hasDerivAt_h c).differentiableAt

theorem differentiable_h : Differentiable ℝ h := fun c => differentiableAt_h c

theorem continuous_h : Continuous h :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_h c).continuousAt

/-- At a zero of `h`, the identity `h' = sigma = 1 - q h` collapses to `h' = 1`. -/
theorem deriv_h_eq_one_of_h_eq_zero {c : ℝ} (hh : h c = 0) : deriv h c = 1 := by
  rw [deriv_h, sigma, hh, mul_zero, sub_zero]

theorem hasDerivAt_sigma (c : ℝ) : HasDerivAt sigma (q c * F c) c := by
  have hprod := (hasDerivAt_q c).mul (hasDerivAt_h c)
  have hsub := (hasDerivAt_const c (1 : ℝ)).sub hprod
  refine (hsub.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · unfold F
    ring
  · unfold sigma
    rfl

theorem deriv_sigma (c : ℝ) : deriv sigma c = q c * F c :=
  (hasDerivAt_sigma c).deriv

theorem differentiableAt_sigma (c : ℝ) : DifferentiableAt ℝ sigma c :=
  (hasDerivAt_sigma c).differentiableAt

theorem differentiable_sigma : Differentiable ℝ sigma := fun c => differentiableAt_sigma c

theorem continuous_sigma : Continuous sigma :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_sigma c).continuousAt

/-- At a zero of `sigma`, `sigma' = q F = q (h ^ 2 - sigma)` collapses to `q h ^ 2`. -/
theorem deriv_sigma_eq_q_mul_h_sq_of_sigma_eq_zero {c : ℝ} (hs : sigma c = 0) :
    deriv sigma c = q c * h c ^ 2 := by
  rw [deriv_sigma, F, hs, sub_zero]

theorem hasDerivAt_F (c : ℝ) : HasDerivAt F (2 * h c * sigma c - q c * F c) c := by
  have hsub := ((hasDerivAt_h c).pow 2).sub (hasDerivAt_sigma c)
  refine (hsub.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · ring
  · unfold F
    rfl

theorem deriv_F (c : ℝ) : deriv F c = 2 * h c * sigma c - q c * F c :=
  (hasDerivAt_F c).deriv

theorem differentiableAt_F (c : ℝ) : DifferentiableAt ℝ F c :=
  (hasDerivAt_F c).differentiableAt

theorem differentiable_F : Differentiable ℝ F := fun c => differentiableAt_F c

theorem continuous_F : Continuous F :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_F c).continuousAt

theorem deriv_F_eq_two_h_sigma_of_F_eq_zero {c : ℝ} (hF : F c = 0) :
    deriv F c = 2 * h c * sigma c := by
  rw [deriv_F, hF, mul_zero, sub_zero]

theorem hasDerivAt_D (c : ℝ) : HasDerivAt D
    (q c * F c * (1 + 2 * sigma c + h c ^ 2) - 2 * h c * sigma c * (1 - sigma c)) c := by
  have hσ := hasDerivAt_sigma c
  have h1σ := (hasDerivAt_const c (1 : ℝ)).sub hσ
  have hh2 := (hasDerivAt_h c).pow 2
  have hD := (hσ.add (hσ.pow 2)).sub (h1σ.mul hh2)
  refine (hD.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · simp only [Pi.pow_apply, Pi.sub_apply]
    dsimp
    ring
  · unfold D
    rfl

theorem deriv_D (c : ℝ) : deriv D c =
    q c * F c * (1 + 2 * sigma c + h c ^ 2) - 2 * h c * sigma c * (1 - sigma c) :=
  (hasDerivAt_D c).deriv

theorem differentiableAt_D (c : ℝ) : DifferentiableAt ℝ D c :=
  (hasDerivAt_D c).differentiableAt

theorem differentiable_D : Differentiable ℝ D := fun c => differentiableAt_D c

theorem continuous_D : Continuous D :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_D c).continuousAt

end SimplexFull
