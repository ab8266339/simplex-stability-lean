import SimplexFull.GlobalScalarCurvature
import SimplexFull.GlobalFoundationBridge
import Mathlib.Analysis.Convex.Deriv
noncomputable section
open Set Filter
open scoped Topology
namespace SimplexFull.GlobalScalar

theorem psiPull_eq_localLogMass : psiPull = WeakSimplex.localLogMass := by
  funext s
  exact (GlobalFoundation.localLogMass_eq_pullback s).symm

theorem psiPull_neg (s : Real) : psiPull s < 0 := by
  rw [psiPull_eq_localLogMass]
  exact WeakSimplex.localLogMass_neg s

theorem psiPull_tendsto_atTop : Tendsto psiPull atTop (nhds 0) := by
  rw [psiPull_eq_localLogMass]
  exact WeakSimplex.localLogMass_tendsto_atTop

theorem psiPull_tendsto_atBot : Tendsto psiPull atBot atBot := by
  rw [psiPull_eq_localLogMass]
  exact WeakSimplex.localLogMass_tendsto_atBot

theorem Psi_neg (y : Real) : Psi y < 0 := psiPull_neg (hInv y)

theorem exists_psiPull_eq {L : Real} (hL : L < 0) : ∃ s : Real, psiPull s = L := by
  obtain ⟨s0,hs0⟩ := (psiPull_tendsto_atBot.eventually (eventually_le_atBot L)).exists
  obtain ⟨s1,hs1⟩ := (psiPull_tendsto_atTop.eventually (eventually_gt_nhds hL)).exists
  exact intermediate_value_univ s0 s1 continuous_psiPull ⟨hs0,hs1.le⟩

theorem exists_Psi_eq {L : Real} (hL : L < 0) : ∃ y > 0, Psi y = L := by
  obtain ⟨s,hs⟩ := exists_psiPull_eq hL
  exact ⟨h s,h_pos s,by rwa [Psi_h]⟩

/-- The paper's Psi inverse, on negative target values. -/
def psiInv (L : Real) : Real := h (Function.invFun psiPull L)

theorem psiInv_pos (L : Real) : 0 < psiInv L := h_pos _

theorem Psi_psiInv {L : Real} (hL : L < 0) : Psi (psiInv L) = L := by
  rw [psiInv, Psi_h]
  exact Function.invFun_eq (exists_psiPull_eq hL)

theorem psiInv_Psi {y : Real} (hy : 0 < y) : psiInv (Psi y) = y := by
  apply strictMonoOn_Psi.injOn (psiInv_pos (Psi y)) hy
  exact Psi_psiInv (Psi_neg y)

#print axioms exists_Psi_eq
#print axioms Psi_psiInv

theorem continuousOn_Psi : ContinuousOn Psi (Ioi (0 : Real)) :=
  fun y hy => (hasDerivAt_Psi hy).continuousAt.continuousWithinAt

theorem strictConcaveOn_Psi : StrictConcaveOn Real (Ioi (0 : Real)) Psi := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) continuousOn_Psi
  simpa only [isOpen_Ioi.interior_eq] using strictAntiOn_deriv_Psi

theorem psiInv_le_iff {L y : Real} (hL : L < 0) (hy : 0 < y) :
    psiInv L ≤ y ↔ L ≤ Psi y := by
  constructor
  · intro hh
    have hb := strictMonoOn_Psi.monotoneOn (psiInv_pos L) hy hh
    rwa [Psi_psiInv hL] at hb
  · intro hh
    by_contra hn
    have hb := strictMonoOn_Psi hy (psiInv_pos L) (lt_of_not_ge hn)
    rw [Psi_psiInv hL] at hb
    exact not_lt_of_ge hh hb

theorem deriv_Psi_pos {y : Real} (hy : 0 < y) : 0 < deriv Psi y := by
  rw [(hasDerivAt_Psi hy).deriv]
  exact q_pos _

theorem deriv_Psi_h (s : Real) : deriv Psi (h s) = q s := by
  rw [(hasDerivAt_Psi (h_pos s)).deriv, hInv_h]

#print axioms strictConcaveOn_Psi
#print axioms psiInv_le_iff
end SimplexFull.GlobalScalar
