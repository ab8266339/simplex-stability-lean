import SimplexFull.GaussianBase
import SimplexFull.Scalar
import SimplexFull.Abstract
import SimplexFull.MillsPrep
import SimplexFull.MillsBounds
import SimplexFull.MillsAlgebra
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace SimplexFull

def millsRatio (t : ℝ) : ℝ := Phi (-t) / phi t

theorem millsRatio_pos (t : ℝ) : 0 < millsRatio t := div_pos (Phi_pos (-t)) (phi_pos t)

theorem mills_h_identity (t : ℝ) :
    millsRatio t * h (-t) = 1-t*millsRatio t := by
  unfold millsRatio h q
  rw [phi_neg_basic]
  field_simp [(phi_pos t).ne', (Phi_pos (-t)).ne']
  <;> ring

theorem mills_sigma_identity {t : ℝ} (ht : 0 < t) :
    (millsRatio t)^2 * sigma (-t) =
      (1/t^2)*(t*millsRatio t)^2+t*millsRatio t-1 := by
  unfold millsRatio sigma h q
  rw [phi_neg_basic]
  field_simp [(phi_pos t).ne', (Phi_pos (-t)).ne', ht.ne']
  <;> ring

theorem mills_F_identity {t : ℝ} (ht : 0 < t) :
    (millsRatio t)^2 * F (-t) =
      (1-1/t^2)*(t*millsRatio t)^2-3*(t*millsRatio t)+2 := by
  unfold millsRatio F sigma h q
  rw [phi_neg_basic]
  field_simp [(phi_pos t).ne', (Phi_pos (-t)).ne', ht.ne']
  <;> ring

theorem mills_D_identity {t : ℝ} (ht : 0 < t) :
    (millsRatio t)^3 / t * D (-t) =
      (t*millsRatio t-1)^2+3*(1/t^2)*(t*millsRatio t)*(t*millsRatio t-1)+
        2*(1/t^2)^2*(t*millsRatio t)^3 := by
  unfold millsRatio D sigma h q
  rw [phi_neg_basic]
  field_simp [(phi_pos t).ne', (Phi_pos (-t)).ne', ht.ne']
  <;> ring

theorem mills_tail_pos_of_bounds {t : ℝ} (ht : 100000 ≤ t)
    (hl : millsPoly5 (1/t^2) ≤ t*millsRatio t)
    (hr : t*millsRatio t ≤ millsPoly4 (1/t^2)) :
    0 < h (-t) ∧ 0 < sigma (-t) ∧ 0 < F (-t) ∧ 0 < D (-t) := by
  have ht0 : 0 < t := by linarith
  have hu : 0 < 1/t^2 := by positivity
  have hsmall : 1/t^2 ≤ 1/10000000000 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 10000000000)
    nlinarith [sq_nonneg (t-100000)]
  have hm := millsRatio_pos t
  have hhprod : 0 < millsRatio t*h (-t) := by
    rw [mills_h_identity]
    exact mills_interval_h_pos hu hsmall hr
  have hsprod : 0 < (millsRatio t)^2*sigma (-t) := by
    rw [mills_sigma_identity ht0]
    exact mills_interval_sigma_pos hu hsmall hl
  have hFprod : 0 < (millsRatio t)^2*F (-t) := by
    rw [mills_F_identity ht0]
    exact mills_interval_F_pos hu hsmall hl hr
  have hDprod : 0 < (millsRatio t)^3/t*D (-t) := by
    rw [mills_D_identity ht0]
    exact mills_interval_D_pos hu hsmall hl hr
  exact ⟨(mul_pos_iff_of_pos_left hm).mp hhprod,
    (mul_pos_iff_of_pos_left (pow_pos hm 2)).mp hsprod,
    (mul_pos_iff_of_pos_left (pow_pos hm 2)).mp hFprod,
    (mul_pos_iff_of_pos_left (div_pos (pow_pos hm 3) ht0)).mp hDprod⟩

private theorem positive_from_concrete_tail
    (tail : ∀ c : ℝ, c ≤ -100000 →
      0 < h c ∧ 0 < sigma c ∧ 0 < F c ∧ 0 < D c) :
    ∀ c : ℝ, 0 < h c ∧ 0 < sigma c ∧ sigma c < 1 ∧ 0 < F c ∧ 0 < D c := by
  have hh : ∀ c, 0 < h c := WeakSimplexPilot.no_downcross h differentiable_h (-100000)
    (fun c hc => (tail c hc).1) (by
      intro c hz
      rw [deriv_h_eq_one_of_h_eq_zero hz]
      norm_num)
  have hs : ∀ c, 0 < sigma c := WeakSimplexPilot.no_downcross sigma differentiable_sigma (-100000)
    (fun c hc => (tail c hc).2.1) (by
      intro c hz
      rw [deriv_sigma_eq_q_mul_h_sq_of_sigma_eq_zero hz]
      exact mul_pos (q_pos c) (pow_pos (hh c) 2))
  have hs1 : ∀ c, sigma c < 1 := by
    intro c
    have hp := mul_pos (q_pos c) (hh c)
    unfold sigma
    linarith
  have hF : ∀ c, 0 < F c := WeakSimplexPilot.no_downcross F differentiable_F (-100000)
    (fun c hc => (tail c hc).2.2.1) (by
      intro c hz
      rw [deriv_F_eq_two_h_sigma_of_F_eq_zero hz]
      exact mul_pos (mul_pos (by norm_num) (hh c)) (hs c))
  have hD : ∀ c, 0 < D c := WeakSimplexPilot.no_downcross D differentiable_D (-100000)
    (fun c hc => (tail c hc).2.2.2) (by
      intro c hz
      have hconstraint : sigma c + sigma c ^ 2 - (1-sigma c)*(h c)^2 = 0 := by
        simpa [D] using hz
      obtain ⟨he, hp⟩ := WeakSimplexPilot.proof_T1 (h c) (sigma c) (hh c) (hs c) (hs1 c) hconstraint
      have hq : q c = (1-sigma c)/h c := by
        apply (eq_div_iff (hh c).ne').2
        unfold sigma
        ring
      have hid : deriv D c = 4*(sigma c)^3/(h c*(1-sigma c)) := by
        calc
          deriv D c = (1+2*sigma c+(h c)^2)*
              ((1-sigma c)*((h c)^2-sigma c)/h c)-
              2*h c*(1-sigma c)*sigma c := by
                rw [deriv_D, hq]
                unfold F
                ring
          _ = 4*(sigma c)^3/(h c*(1-sigma c)) := he
      rw [hid]
      exact hp)
  exact fun c => ⟨hh c, hs c, hs1 c, hF c, hD c⟩


theorem mills_scaled_bounds {t : ℝ} (ht : 0 < t) :
    millsPoly5 (1/t^2) ≤ t*millsRatio t ∧ t*millsRatio t ≤ millsPoly4 (1/t^2) := by
  obtain ⟨hl, hr⟩ := mills_ratio_bounds ht
  have he4 : t*millsP4 t = millsPoly4 (1/t^2) := by
    unfold millsP4 millsPoly4
    field_simp [ht.ne']
    <;> ring
  have he5 : t*millsP5 t = millsPoly5 (1/t^2) := by
    unfold millsP5 millsP4 millsPoly5 millsPoly4
    field_simp [ht.ne']
    <;> ring
  constructor
  · rw [← he5]
    exact mul_le_mul_of_nonneg_left hl ht.le
  · rw [← he4]
    exact mul_le_mul_of_nonneg_left hr ht.le

theorem scalar_left_tail_positive {c : ℝ} (hc : c ≤ -100000) :
    0 < h c ∧ 0 < sigma c ∧ 0 < F c ∧ 0 < D c := by
  have ht : 100000 ≤ -c := by linarith
  obtain ⟨hl, hr⟩ := mills_scaled_bounds (by linarith : 0 < -c)
  simpa only [neg_neg] using mills_tail_pos_of_bounds ht hl hr

theorem scalar_positive (c : ℝ) :
    0 < h c ∧ 0 < sigma c ∧ sigma c < 1 ∧ 0 < F c ∧ 0 < D c :=
  positive_from_concrete_tail (fun _ hc => scalar_left_tail_positive hc) c

theorem h_pos (c : ℝ) : 0 < h c := (scalar_positive c).1
theorem sigma_pos (c : ℝ) : 0 < sigma c := (scalar_positive c).2.1
theorem sigma_lt_one (c : ℝ) : sigma c < 1 := (scalar_positive c).2.2.1
theorem F_pos (c : ℝ) : 0 < F c := (scalar_positive c).2.2.2.1
theorem D_pos (c : ℝ) : 0 < D c := (scalar_positive c).2.2.2.2

#print axioms scalar_positive
#print axioms h_pos
#print axioms sigma_pos
#print axioms F_pos
#print axioms D_pos
theorem strictMono_h : StrictMono h := by
  apply strictMono_of_deriv_pos
  intro c
  rw [deriv_h]
  exact sigma_pos c

theorem strictAnti_q : StrictAnti q := by
  apply strictAnti_of_deriv_neg
  intro c
  rw [deriv_q]
  exact neg_neg_of_pos (mul_pos (q_pos c) (h_pos c))

theorem strictMono_sigma : StrictMono sigma := by
  apply strictMono_of_deriv_pos
  intro c
  rw [deriv_sigma]
  exact mul_pos (q_pos c) (F_pos c)

theorem h_le_abs_add (c : ℝ) : h c ≤ |c| + h 0 := by
  by_cases hc : c ≤ 0
  · have hh := strictMono_h.monotone hc
    linarith [abs_nonneg c]
  · have hc0 : 0 ≤ c := le_of_not_ge hc
    have hq := strictAnti_q.antitone hc0
    simp only [h, zero_add, abs_of_nonneg hc0]
    linarith

theorem abs_h_le_abs_add (c : ℝ) : |h c| ≤ |c| + h 0 := by
  rw [abs_of_pos (h_pos c)]
  exact h_le_abs_add c

theorem hasDerivAt_hsq_div_sigma (c : ℝ) :
    HasDerivAt (fun x => h x^2/sigma x) (h c*D c/(sigma c)^2) c := by
  have hd := ((hasDerivAt_h c).pow 2).fun_div (hasDerivAt_sigma c) (sigma_pos c).ne'
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  simp only [Pi.pow_apply]
  unfold F D sigma
  ring

theorem strictMono_hsq_div_sigma : StrictMono (fun c => h c^2/sigma c) := by
  apply strictMono_of_deriv_pos
  intro c
  rw [(hasDerivAt_hsq_div_sigma c).deriv]
  exact div_pos (mul_pos (h_pos c) (D_pos c)) (pow_pos (sigma_pos c) 2)

#print axioms strictMono_sigma
#print axioms strictMono_hsq_div_sigma
#print axioms h_le_abs_add
theorem mills_remainder_bound {t : ℝ} (ht : 0 < t) :
    |millsRatio t-millsP4 t| ≤ 945/t^11 := by
  obtain ⟨hl, hr⟩ := mills_ratio_bounds ht
  change millsP4 t-945/t^11 ≤ millsRatio t at hl
  change millsRatio t ≤ millsP4 t at hr
  rw [abs_of_nonpos (sub_nonpos.mpr hr)]
  linarith

#print axioms mills_remainder_bound
theorem strictMono_hsq : StrictMono (fun c : ℝ => h c^2) := by
  intro x y hxy
  nlinarith [strictMono_h hxy, h_pos x, h_pos y]

theorem continuous_hsq_div_sigma : Continuous (fun c : ℝ => h c^2/sigma c) :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_hsq_div_sigma c).continuousAt

#print axioms strictMono_hsq
end SimplexFull