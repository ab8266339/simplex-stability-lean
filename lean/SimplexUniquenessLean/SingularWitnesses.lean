import WeakSimplexConjectureLean
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Adaptive witnesses for singular covariance

Mulgund's `exists_adaptiveWitnesses` constructs the adaptive tilt data for positive-definite
`R`. This module extends it to every admissible covariance, singular included, by a compactness
argument: witnesses for the regularizations `(1 - ε) R + ε I` stay in a bounded set, because
`localLogMass < 0` and `localLogMass → -∞` at `-∞` bound each coordinate from below through the
value bound, and the compatibility equation then bounds it from above. A convergent subsequence
yields witnesses for `R`, since compatibility and the value bound are closed conditions.
-/

namespace SimplexUniqueness

open MeasureTheory Set WeakSimplex ProbabilityTheory Filter
open scoped ENNReal Matrix BigOperators InnerProductSpace Topology

namespace Witness

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Orthant/Singular.lean, MIT
/-- The regularization `(1 - ε) R + ε I`. -/
noncomputable def regCov {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 - ε) • R + ε • 1

theorem centeredIdentity_posSemidef {m : ℕ} (hm : 0 < m) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) -
      (1 / (m : ℝ)) • allOnesMatrix m).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub Matrix.isHermitian_one ?_
    apply Matrix.IsHermitian.smul
    · ext i j
      simp [allOnesMatrix]
    · simp
  · intro x
    have hrewrite :
        star x ⬝ᵥ (((1 : Matrix (Fin m) (Fin m) ℝ) -
          (1 / (m : ℝ)) • allOnesMatrix m).mulVec x) =
          (∑ i, x i ^ 2) - (1 / (m : ℝ)) * (∑ i, x i) ^ 2 := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply]
      calc
        (∑ i, x i * ∑ j,
          ((if i = j then 1 else 0) - (1 / (m : ℝ)) * 1) * x j) =
            ∑ i, x i * (x i - (1 / (m : ℝ)) * ∑ j, x j) := by
              apply Finset.sum_congr rfl
              intro i _
              congr 1
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
              simp only [mul_one]
              rw [show (∑ j, (if i = j then 1 else 0) * x j) = x i by simp]
              rw [← Finset.mul_sum]
        _ = (∑ i, x i ^ 2) - (1 / (m : ℝ)) * (∑ i, x i) ^ 2 := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              congr 1
              · simp only [pow_two]
              · rw [← Finset.sum_mul]
                ring
    rw [hrewrite]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hcs : (∑ i, x i) ^ 2 ≤ (m : ℝ) * ∑ i, x i ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
    have hdiv : (∑ i, x i) ^ 2 / (m : ℝ) ≤ ∑ i, x i ^ 2 :=
      (div_le_iff₀ hmR).2 (by simpa [mul_comm] using hcs)
    rw [sub_nonneg]
    simpa [div_eq_inv_mul, mul_comm] using hdiv


theorem regCov_posDef
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (regCov R ε).PosDef := by
  have hleft : ((1 - ε) • R).PosSemidef := hR.1.1.smul (by linarith)
  have hright : (ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hε0
  exact Matrix.PosDef.posSemidef_add hleft hright

theorem regCov_isWeakSimplexCov
    {m : ℕ} (hm : 0 < m) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    IsWeakSimplexCov (regCov R ε) := by
  have hpd := regCov_posDef R hR hε0 hε1
  refine ⟨⟨hpd.posSemidef, ?_⟩, ?_⟩
  · intro i
    simp [regCov, hR.1.2 i]
  · have hrewrite :
        regCov R ε - (1 / (m : ℝ)) • allOnesMatrix m =
          (1 - ε) • (R - (1 / (m : ℝ)) • allOnesMatrix m) +
            ε • ((1 : Matrix (Fin m) (Fin m) ℝ) -
              (1 / (m : ℝ)) • allOnesMatrix m) := by
        ext i j
        simp [regCov]
        ring
    rw [hrewrite]
    exact (hR.2.smul (by linarith)).add
      ((centeredIdentity_posSemidef hm).smul hε0.le)

theorem normalPDF_le_one (x : ℝ) : normalPDF x ≤ 1 := by
  unfold normalPDF gaussianPDFReal
  have h1 : (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [Real.one_le_sqrt]
    simp only [NNReal.coe_one, mul_one]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have : 0 ≤ x ^ 2 / 2 := by positivity
    rw [neg_div]; linarith
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

theorem normalCDF_mono {a b : ℝ} (h : a ≤ b) : normalCDF a ≤ normalCDF b := by
  unfold normalCDF
  exact setIntegral_mono_set (integrable_gaussianPDFReal 0 1).integrableOn
    (ae_of_all _ fun y ↦ (normalPDF_pos y).le) (Iic_subset_Iic.2 h).eventuallyLE

theorem continuous_normalCDF : Continuous normalCDF := by
  rw [continuous_iff_continuousAt]
  exact fun s ↦ (hasDerivAt_normalCDF s).continuousAt

theorem continuous_r : Continuous r := by
  have : r = fun s ↦ H s - s := by
    ext s; simp [H]
  rw [this]
  exact continuous_H.sub continuous_id

/-- `r` is bounded above on every ray `[N, ∞)`. -/
theorem r_bddAbove (N : ℝ) : ∃ A : ℝ, ∀ t, N ≤ t → r t ≤ A := by
  refine ⟨1 / normalCDF N, fun t ht ↦ ?_⟩
  unfold r
  have hN := normalCDF_pos N
  calc normalPDF t / normalCDF t ≤ normalPDF t / normalCDF N :=
        div_le_div_of_nonneg_left (normalPDF_pos t).le hN (normalCDF_mono ht)
    _ ≤ 1 / normalCDF N := div_le_div_of_nonneg_right (normalPDF_le_one t) hN.le


theorem matrixMul_regCov {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (x : Coord m) :
    matrixMul (regCov R ε) x = (1 - ε) • matrixMul R x + ε • x := by
  simp [regCov, matrixMul, map_add, map_smul]

theorem continuous_matrixMul {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (matrixMul R : Coord m → Coord m) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) R).continuous

theorem continuous_coordinateMap_r {m : ℕ} :
    Continuous (coordinateMap r : Coord m → Coord m) := by
  unfold coordinateMap Coord.ofFun
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m ↦ ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_r.comp (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i)

theorem inner_self_eq {m : ℕ} (a : Coord m) : ⟪a, a⟫_ℝ = ∑ i, a i ^ 2 := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
  simp

/-- Each coordinate of an adaptive witness for a PSD matrix has local log-mass at least
`m log Φ(c)`. -/
theorem localLogMass_ge {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosSemidef) {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) :
    (m : ℝ) * Real.log (normalCDF c) ≤ localLogMass (w.s i) := by
  have hq : 0 ≤ ⟪w.a, matrixMul R w.a⟫_ℝ := by
    change 0 ≤ qform R w.a
    rw [qform_eq_dotProduct]
    simpa using hR.dotProduct_mulVec_nonneg (Coord.toFun w.a)
  have hvb := w.value_bound
  rw [inner_self_eq] at hvb
  have hsum : (m : ℝ) * Real.log (normalCDF c) ≤ ∑ j, localLogMass (w.s j) := by
    have : ∑ j, localLogMass (w.s j) =
        ∑ j, Real.log (normalCDF (w.s j)) + (∑ j, w.a j ^ 2) / 2 := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [w.a_eq_r]; rfl
    linarith
  refine hsum.trans ?_
  have hneg : ∀ j ∈ Finset.univ.erase i, localLogMass (w.s j) ≤ 0 :=
    fun j _ ↦ (localLogMass_neg _).le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  linarith [Finset.sum_nonpos hneg]

/-- Norm bound on the tilt vector: `a_i ≤ A` forces `‖a‖ ≤ m A`. -/
theorem norm_le_of_coord_le {m : ℕ} (a : Coord m) (A : ℝ) (hA : 0 ≤ A)
    (h0 : ∀ i, 0 ≤ a i) (h : ∀ i, a i ≤ A) : ‖a‖ ≤ m * A := by
  have h2 : ‖a‖ ^ 2 ≤ (m * A) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hi : ∀ i, ‖a i‖ ^ 2 ≤ A ^ 2 := fun i ↦ by
      rw [Real.norm_eq_abs, sq_abs]
      exact pow_le_pow_left₀ (h0 i) (h i) 2
    calc ∑ i, ‖a i‖ ^ 2 ≤ ∑ _i : Fin m, A ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
      _ = m * A ^ 2 := by simp
      _ ≤ (m * A) ^ 2 := by
        have hm1 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ m := by exact_mod_cast h
            nlinarith
        nlinarith [sq_nonneg A]
  exact le_of_sq_le_sq h2 (by positivity)

theorem tendsto_regMul {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) {ε : ℕ → ℝ} {a : ℕ → Coord m}
    {a₀ : Coord m} (hε : Tendsto ε atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun n ↦ (1 - ε n) • matrixMul R (a n) + ε n • a n) atTop
      (𝓝 (matrixMul R a₀)) := by
  have h1 : Tendsto (fun n ↦ 1 - ε n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hε
  have h2 : Tendsto (fun n ↦ matrixMul R (a n)) atTop (𝓝 (matrixMul R a₀)) :=
    ((continuous_matrixMul R).tendsto a₀).comp ha
  have h3 := (h1.smul h2).add (hε.smul ha)
  simpa using h3

end Witness

/-- Adaptive witnesses exist for every admissible covariance, singular included. -/
theorem exists_adaptiveWitnesses_of_isWeakSimplexCov
    {m : ℕ} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsWeakSimplexCov R)
    (c : ℝ) :
    Nonempty (AdaptiveWitnesses R c) := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε0 : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n ↦ by
    simp only [ε]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : ∀ n, Nonempty (AdaptiveWitnesses (Witness.regCov R (ε n)) c) := fun n ↦
    exists_adaptiveWitnesses hm _ (Witness.regCov_posDef R hR (hε0 n) (hε1 n))
      (Witness.regCov_isWeakSimplexCov hm R hR (hε0 n) (hε1 n)).2 c
  let w : ∀ n, AdaptiveWitnesses (Witness.regCov R (ε n)) c := fun n ↦ (hw n).some
  have hpsd : ∀ n, (Witness.regCov R (ε n)).PosSemidef := fun n ↦
    (Witness.regCov_posDef R hR (hε0 n) (hε1 n)).posSemidef
  -- lower bound on every coordinate
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ t ≤ N, localLogMass t < (m : ℝ) * Real.log (normalCDF c) :=
    eventually_atBot.1 (localLogMass_tendsto_atBot.eventually (eventually_lt_atBot _))
  have hsN : ∀ n i, N < (w n).s i := fun n i ↦ by
    by_contra hcon
    have := hN _ (not_lt.1 hcon)
    linarith [Witness.localLogMass_ge (hpsd n) (w n) i]
  obtain ⟨A, hA⟩ := Witness.r_bddAbove N
  have hA0 : 0 ≤ A := (r_pos N).le.trans (hA N le_rfl)
  have hnorm_a : ∀ n, ‖(w n).a‖ ≤ m * A := fun n ↦
    Witness.norm_le_of_coord_le _ A hA0 (fun i ↦ ((w n).a_pos i).le) fun i ↦ by
      rw [(w n).a_eq_r]; exact hA _ (hsN n i).le
  set K : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) R‖ with hK
  have hs_eq : ∀ n, (w n).s = c • allOnesVector m - (w n).a +
      ((1 - ε n) • matrixMul R (w n).a + ε n • (w n).a) := fun n ↦ by
    have := (w n).compatibility
    rw [Witness.matrixMul_regCov] at this
    rw [← this]; abel
  set B : ℝ := |c| * ‖allOnesVector m‖ + (K + 2) * (m * A) with hB
  have hnorm_s : ∀ n, ‖(w n).s‖ ≤ B := fun n ↦ by
    have hMa : ‖matrixMul R (w n).a‖ ≤ K * ‖(w n).a‖ :=
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).le_opNorm _
    have hK0 : 0 ≤ K := norm_nonneg _
    have ha := hnorm_a n
    have ha0 := norm_nonneg (w n).a
    have h1 : ‖(1 - ε n) • matrixMul R (w n).a‖ ≤ K * ‖(w n).a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hε1 n])]
      nlinarith [hε0 n, norm_nonneg (matrixMul R (w n).a)]
    have h2 : ‖ε n • (w n).a‖ ≤ ‖(w n).a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hε0 n).le]
      nlinarith [hε1 n]
    rw [hs_eq n]
    calc ‖c • allOnesVector m - (w n).a +
          ((1 - ε n) • matrixMul R (w n).a + ε n • (w n).a)‖
        ≤ ‖c • allOnesVector m‖ + ‖(w n).a‖ + (‖(1 - ε n) • matrixMul R (w n).a‖ +
            ‖ε n • (w n).a‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _)) (norm_add_le _ _))
      _ ≤ |c| * ‖allOnesVector m‖ + ‖(w n).a‖ + (K * ‖(w n).a‖ + ‖(w n).a‖) := by
          rw [norm_smul, Real.norm_eq_abs]; linarith
      _ ≤ B := by rw [hB]; nlinarith
  obtain ⟨s, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Coord m) B).tendsto_subseq
    (x := fun n ↦ (w n).s) fun n ↦ mem_closedBall_zero_iff.2 (hnorm_s n)
  have hεφ : Tendsto (fun n ↦ ε (φ n)) atTop (𝓝 0) := hεt.comp hφ.tendsto_atTop
  have halim : Tendsto (fun n ↦ (w (φ n)).a) atTop (𝓝 (coordinateMap r s)) := by
    have : ∀ n, (w (φ n)).a = coordinateMap r (w (φ n)).s := fun n ↦ by
      ext i; simp [coordinateMap, (w (φ n)).a_eq_r]
    simp_rw [this]
    exact (Witness.continuous_coordinateMap_r.tendsto s).comp hlim
  have hMlim := Witness.tendsto_regMul R hεφ halim
  refine ⟨{
    s := s
    a := coordinateMap r s
    a_eq_r := fun i ↦ rfl
    a_pos := fun i ↦ r_pos _
    compatibility := ?_
    value_bound := ?_ }⟩
  · have hc : Tendsto (fun n ↦ (w (φ n)).s + (w (φ n)).a -
        ((1 - ε (φ n)) • matrixMul R (w (φ n)).a + ε (φ n) • (w (φ n)).a)) atTop
        (𝓝 (s + coordinateMap r s - matrixMul R (coordinateMap r s))) :=
      (hlim.add halim).sub hMlim
    have hconst : ∀ n, (w (φ n)).s + (w (φ n)).a -
        ((1 - ε (φ n)) • matrixMul R (w (φ n)).a + ε (φ n) • (w (φ n)).a) =
        c • allOnesVector m := fun n ↦ by
      have := (w (φ n)).compatibility
      rwa [Witness.matrixMul_regCov] at this
    simp_rw [hconst] at hc
    have := tendsto_nhds_unique tendsto_const_nhds hc
    exact this.symm
  · have hv : Tendsto (fun n ↦ (∑ i, Real.log (normalCDF ((w (φ n)).s i))) +
        (⟪(w (φ n)).a, (w (φ n)).a⟫_ℝ -
          ⟪(w (φ n)).a, (1 - ε (φ n)) • matrixMul R (w (φ n)).a + ε (φ n) • (w (φ n)).a⟫_ℝ)
          / 2) atTop
        (𝓝 ((∑ i, Real.log (normalCDF (s i))) +
          (⟪coordinateMap r s, coordinateMap r s⟫_ℝ -
            ⟪coordinateMap r s, matrixMul R (coordinateMap r s)⟫_ℝ) / 2)) := by
      have hlog : Continuous (fun x : Coord m ↦ ∑ i, Real.log (normalCDF (x i))) :=
        continuous_finsetSum _ fun i _ ↦
          (Witness.continuous_normalCDF.comp
            (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i)).log
            fun x ↦ (normalCDF_pos _).ne'
      exact (hlog.tendsto s |>.comp hlim).add
        (((halim.inner halim).sub (halim.inner hMlim)).div_const 2)
    refine ge_of_tendsto hv (Eventually.of_forall fun n ↦ ?_)
    have := (w (φ n)).value_bound
    rwa [Witness.matrixMul_regCov] at this
  
end SimplexUniqueness
