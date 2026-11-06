import SimplexFull.GlobalScalarPsi
noncomputable section
open Set
namespace SimplexFull.GlobalScalar

/-- The positive negative second derivative of the paper's actual Psi. -/
def psiCurvature (y : Real) : Real := q (hInv y) * y / sigma (hInv y)

theorem psiCurvature_pos {y : Real} (hy : 0 < y) : 0 < psiCurvature y :=
  div_pos (mul_pos (q_pos _) hy) (sigma_pos _)

theorem continuousAt_psiCurvature {y : Real} (hy : 0 < y) :
    ContinuousAt psiCurvature y := by
  unfold psiCurvature
  exact ((continuous_q.continuousAt.comp (continuousAt_hInv hy)).mul continuousAt_id).div
    (continuous_sigma.continuousAt.comp (continuousAt_hInv hy)) (ne_of_gt (sigma_pos _))

theorem hasDerivAt_deriv_Psi {y : Real} (hy : 0 < y) :
    HasDerivAt (deriv Psi) (-psiCurvature y) y := by
  have hd : HasDerivAt (fun t => q (hInv t)) (-psiCurvature y) y := by
    refine ((hasDerivAt_q (hInv y)).comp y (hasDerivAt_hInv hy)).congr_deriv ?_
    rw [h_hInv hy]
    dsimp [psiCurvature]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact (hasDerivAt_Psi ht).deriv

theorem deriv2_Psi {y : Real} (hy : 0 < y) :
    deriv (deriv Psi) y = -psiCurvature y := (hasDerivAt_deriv_Psi hy).deriv

theorem strictMonoOn_Psi : StrictMonoOn Psi (Ioi (0 : Real)) := by
  intro x hx y hy hxy
  exact strictMono_psiPull (strictMonoOn_hInv hx hy hxy)

theorem strictAntiOn_deriv_Psi : StrictAntiOn (deriv Psi) (Ioi (0 : Real)) := by
  intro x hx y hy hxy
  rw [(hasDerivAt_Psi hx).deriv, (hasDerivAt_Psi hy).deriv]
  exact strictAnti_q (strictMonoOn_hInv hx hy hxy)

#print axioms hasDerivAt_deriv_Psi
#print axioms strictAntiOn_deriv_Psi

/-- The fixed compact interval from the manuscript's centroid constant. -/
def curvatureInterval : Set Real := Icc (h 0 / 2) (3 * h 1 / 2)

theorem curvatureInterval_nonempty : curvatureInterval.Nonempty := by
  apply Set.nonempty_Icc.mpr
  have hs := strictMono_h (show (0 : Real) < 1 by norm_num)
  linarith [h_pos 0]

theorem curvatureInterval_pos {y : Real} (hy : y ∈ curvatureInterval) : 0 < y := by
  have h0 := h_pos 0
  have hl : h 0 / 2 ≤ y := hy.1
  linarith

theorem continuousOn_psiCurvature_interval : ContinuousOn psiCurvature curvatureInterval :=
  fun y hy => (continuousAt_psiCurvature (curvatureInterval_pos hy)).continuousWithinAt

theorem exists_maxPsiCurvature :
    ∃ y ∈ curvatureInterval, IsMaxOn psiCurvature curvatureInterval y :=
  isCompact_Icc.exists_isMaxOn curvatureInterval_nonempty continuousOn_psiCurvature_interval

/-- The actual maximum defining M0 in the paper. -/
def M0 : Real := psiCurvature (Classical.choose exists_maxPsiCurvature)

theorem M0_pos : 0 < M0 := by
  apply psiCurvature_pos
  exact curvatureInterval_pos (Classical.choose_spec exists_maxPsiCurvature).1

theorem psiCurvature_le_M0 {y : Real} (hy : y ∈ curvatureInterval) :
    psiCurvature y ≤ M0 :=
  (Classical.choose_spec exists_maxPsiCurvature).2 hy

theorem M0_attained : ∃ y ∈ curvatureInterval, M0 = psiCurvature y :=
  ⟨Classical.choose exists_maxPsiCurvature, (Classical.choose_spec exists_maxPsiCurvature).1, rfl⟩

#print axioms M0_pos
#print axioms psiCurvature_le_M0
end SimplexFull.GlobalScalar
