import SimplexFull.GlobalScalarRange
noncomputable section
namespace SimplexFull.GlobalScalar

theorem q_lt_sqrt_neg_two_log_Phi (s : Real) :
    q s < Real.sqrt (-2 * Real.log (Phi s)) := by
  have hp := psiPull_neg s
  dsimp [psiPull] at hp
  have hsq : q s^2 < -2 * Real.log (Phi s) := by linarith
  have hnn : 0 ≤ -2 * Real.log (Phi s) := (sq_nonneg (q s)).trans hsq.le
  have hr := Real.sq_sqrt hnn
  have hn := Real.sqrt_nonneg (-2 * Real.log (Phi s))
  nlinarith [q_pos s]

theorem threshold_plus_radius_pos (s : Real) :
    0 < s + Real.sqrt (-2 * Real.log (Phi s)) := by
  have hp := h_pos s
  have hq := q_lt_sqrt_neg_two_log_Phi s
  dsimp [h] at hp
  linarith

/-- Positivity of the exact B0 expression, before any adaptive-witness assumption. -/
theorem threshold_envelope_pos {m alpha u v : Real} (hm : 0 < m) (huv : u ≤ v) :
    0 < v + Real.sqrt (-2 * (m * Real.log (Phi u)) / m) +
      Real.sqrt (-2 * alpha * (m * Real.log (Phi u))) := by
  have he : -2 * (m * Real.log (Phi u)) / m = -2 * Real.log (Phi u) := by
    field_simp [ne_of_gt hm]
  rw [he]
  have hp := threshold_plus_radius_pos u
  have hn := Real.sqrt_nonneg (-2 * alpha * (m * Real.log (Phi u)))
  linarith

/-- The adaptive scalar log-mass bound implies the exact derivative cap A0. -/
theorem q_le_deriv_Psi_psiInv {L s : Real} (hL : L < 0)
    (hbound : L ≤ psiPull s) : q s ≤ deriv Psi (psiInv L) := by
  have hb : psiInv L ≤ h s := (psiInv_le_iff hL (h_pos s)).mpr (by rwa [Psi_h])
  have hd := strictAntiOn_deriv_Psi.antitoneOn (psiInv_pos L) (h_pos s) hb
  rwa [deriv_Psi_h] at hd

#print axioms threshold_envelope_pos
#print axioms q_le_deriv_Psi_psiInv
end SimplexFull.GlobalScalar
