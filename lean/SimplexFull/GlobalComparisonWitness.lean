import SimplexFull.GlobalComparisonDefs
noncomputable section
open MeasureTheory ProbabilityTheory WeakSimplex
open scoped BigOperators InnerProductSpace
namespace SimplexFull.GlobalComparison

theorem witnessValue_eq {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) :
    witnessValue w = (∑ i, Real.log (normalCDF (w.s i))) +
      (inner ℝ w.a w.a - inner ℝ w.a (matrixMul R w.a))/2 := by
  rw [witnessValue, SimplexUniqueness.Witness.inner_self_eq]
  have he : (∑ i, GlobalScalar.psiPull (w.s i)) =
      (∑ i, Real.log (normalCDF (w.s i))) + (∑ i, w.a i^2)/2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [w.a_eq_r]
    rfl
  rw [he]
  dsimp [qform]
  ring

theorem witnessValue_lower {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : logFloor m c ≤ witnessValue w := by
  rw [witnessValue_eq]
  exact w.value_bound

theorem logFloor_mono {m : ℕ} {u c : ℝ} (huc : u ≤ c) :
    logFloor m u ≤ logFloor m c := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  exact Real.log_le_log (Phi_pos u) (SimplexUniqueness.Witness.normalCDF_mono huc)

theorem witness_local_bound {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c u : ℝ}
    (hR : R.PosSemidef) (w : AdaptiveWitnesses R c) (huc : u ≤ c) (i : Fin m) :
    logFloor m u ≤ GlobalScalar.psiPull (w.s i) :=
  (logFloor_mono huc).trans (SimplexUniqueness.Witness.localLogMass_ge hR w i)

theorem witness_a_le {m : ℕ} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) ℝ} {c u : ℝ}
    (hR : R.PosSemidef) (w : AdaptiveWitnesses R c) (huc : u ≤ c) (i : Fin m) :
    w.a i ≤ capA m u := by
  rw [w.a_eq_r]
  exact GlobalScalar.q_le_deriv_Psi_psiInv (logFloor_neg hm u)
    (witness_local_bound hR w huc i)

theorem witness_beta_le {m : ℕ} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) ℝ} {c u : ℝ}
    (hR : R.PosSemidef) (w : AdaptiveWitnesses R c) (huc : u ≤ c) (i : Fin m) :
    beta m u ≤ h (w.s i) := by
  apply (GlobalScalar.psiInv_le_iff (logFloor_neg hm u) (h_pos _)).mpr
  rw [GlobalScalar.Psi_h]
  exact witness_local_bound hR w huc i

theorem witness_qform_le {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c u : ℝ}
    (w : AdaptiveWitnesses R c) (huc : u ≤ c) :
    qform R w.a ≤ -2 * logFloor m u := by
  have hv := (logFloor_mono huc).trans (witnessValue_lower w)
  have hs : (∑ i, GlobalScalar.psiPull (w.s i)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => (GlobalScalar.psiPull_neg _).le
  dsimp [witnessValue] at hv
  linarith

theorem witness_threshold_eq {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) :
    h (w.s i) = c + matrixMul R w.a i := by
  have hc := congrArg (fun x : Coord m => x i) w.compatibility
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hc
  have ha : w.a i = q (w.s i) := w.a_eq_r i
  have ho : allOnesVector m i = 1 := rfl
  rw [ho] at hc
  dsimp [h]
  linarith

theorem paper_sqrt_envelope {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : L ≤ 0) :
    Real.sqrt (-2*L) ≤ Real.sqrt (-2*L/m) +
      Real.sqrt (-2*(((m : ℝ)-1)/m)*L) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0<m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 0 ≤ -2*L/m := div_nonneg (by linarith) hm0.le
  have h2 : 0 ≤ -2*(((m : ℝ)-1)/m)*L := by
    exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (div_nonneg (sub_nonneg.mpr hm1) hm0.le)) hL
  have he : -2*L = -2*L/m + (-2*(((m : ℝ)-1)/m)*L) := by
    field_simp; ring
  have hs := Real.sq_sqrt (show 0 ≤ -2*L by linarith)
  have hs1 := Real.sq_sqrt h1
  have hs2 := Real.sq_sqrt h2
  nlinarith [Real.sqrt_nonneg (-2*L), Real.sqrt_nonneg (-2*L/m),
    Real.sqrt_nonneg (-2*(((m : ℝ)-1)/m)*L),
    mul_nonneg (Real.sqrt_nonneg (-2*L/m))
      (Real.sqrt_nonneg (-2*(((m : ℝ)-1)/m)*L))]

theorem witness_threshold_le {m : ℕ} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) ℝ} {c u v : ℝ}
    (hR : IsCorrelation R) (w : AdaptiveWitnesses R c)
    (huc : u ≤ c) (hcv : c ≤ v) (i : Fin m) :
    h (w.s i) ≤ capB m u v := by
  have hc := GlobalCentroid.qform_cauchy hR.1 (GlobalCentroid.coordBasis i) w.a
  rw [GlobalCentroid.inner_coordBasis, GlobalCentroid.qform_coordBasis, hR.2 i,
    one_mul] at hc
  have hq := witness_qform_le w huc
  have hL := logFloor_neg hm u
  have hs := Real.sq_sqrt (show 0 ≤ -2*logFloor m u by linarith)
  have hr : matrixMul R w.a i ≤ Real.sqrt (-2*logFloor m u) := by
    nlinarith [Real.sqrt_nonneg (-2*logFloor m u)]
  have he := paper_sqrt_envelope (m:=m) (by omega) hL.le
  rw [witness_threshold_eq]
  dsimp [capB]
  linarith

#print axioms witness_a_le
#print axioms witness_beta_le
#print axioms witness_threshold_le
end SimplexFull.GlobalComparison
