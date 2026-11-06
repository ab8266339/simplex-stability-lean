import SimplexFull.GeometryBase
import SimplexFull.GramCoordinates
import SimplexFull.Shell
import SimplexFull.ProcrustesFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Quantitative square-root shell enclosure.

`D = T - chartKappa m tau • centering m` is the deviation of a centered
positive semidefinite square root from the chart ray. The Frobenius bound is
the finite sum `frobSq`, not an operator norm. The covariance identity is the
normalization needed to instantiate a Gaussian loss; it is derived from the
unit diagonal and `uncompress_compression_of_symm_zeroDiagonal`.
-/

set_option maxHeartbeats 800000

noncomputable section

open Finset Matrix
open scoped Matrix RealInnerProductSpace

namespace SimplexFull.Geometry

private lemma trace_centering (m : ℕ) (hm : m ≠ 0) :
    Matrix.trace (centering m) = (m : ℝ) - 1 := by
  rw [trace_eq_sum_diag]
  simp_rw [centering_apply_diag]
  rw [sum_const_fin, mul_sub, mul_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm)]

private lemma trace_gram_mul_onesMatrix {m d : ℕ} (X : Config m d) :
    Matrix.trace (gram X * onesMatrix m) = ‖∑ i, X i‖ ^ 2 := by
  rw [trace_eq_sum_diag]
  have hentry : ∀ i, (gram X * onesMatrix m) i i =
      inner ℝ (X i) (∑ j, X j) := by
    intro i
    rw [Matrix.mul_apply]
    simp_rw [onesMatrix, mul_one, gram_apply]
    exact (inner_sum Finset.univ (fun j => X j) (X i)).symm
  simp_rw [hentry]
  rw [← sum_inner Finset.univ (fun i => X i) (∑ j, X j), real_inner_self_eq_norm_sq]

private lemma trace_compressed_gram {m d : ℕ} (hm : m ≠ 0) (X : Config m d) :
    Matrix.trace (centering m * gram X * centering m) =
      Matrix.trace (gram X) - (m : ℝ)⁻¹ * ‖∑ i, X i‖ ^ 2 := by
  have hstep1 : Matrix.trace (centering m * gram X * centering m) =
      Matrix.trace ((gram X * centering m) * centering m) := by
    rw [Matrix.mul_assoc]
    exact Matrix.trace_mul_comm (centering m) (gram X * centering m)
  have hstep2 : (gram X * centering m) * centering m = gram X * centering m := by
    rw [Matrix.mul_assoc, centering_mul_self hm]
  rw [hstep1, hstep2]
  have hGP : gram X * centering m =
      gram X - (m : ℝ)⁻¹ • (gram X * onesMatrix m) := by
    rw [centering, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  rw [hGP, Matrix.trace_sub, Matrix.trace_smul, trace_gram_mul_onesMatrix, smul_eq_mul]

private lemma trace_gram_of_unit {m d : ℕ} (X : Config m d) (hX : UnitConfig X) :
    Matrix.trace (gram X) = (m : ℝ) := by
  rw [trace_eq_sum_diag]
  simp_rw [gram_diagonal_unit X hX]
  rw [sum_const_fin, mul_one]

private lemma alpha_mul_cast (m : ℕ) (hm : m ≠ 0) :
    alpha m * (m : ℝ) = (m : ℝ) - 1 := by
  unfold alpha
  exact div_mul_cancel₀ ((m : ℝ) - 1) (Nat.cast_ne_zero.mpr hm)

/-- `trace(T*T) ≤ m - 1`, from `trace(P G P) = trace G - m⁻¹ ‖∑ X i‖²`
and the squared centroid being nonnegative. -/
theorem trace_sqrt_sq_le {m d : ℕ} (hm : 3 ≤ m) (X : Config m d)
    (hX : UnitConfig X) (T : Matrix (Fin m) (Fin m) ℝ)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m)) :
    Matrix.trace (T * T) ≤ (m : ℝ) - 1 := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  have hαpos : 0 ≤ alpha m := by
    unfold alpha
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt hm1))
      (Nat.cast_nonneg m)
  have hnn : 0 ≤ (m : ℝ)⁻¹ * ‖∑ i, X i‖ ^ 2 :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) (sq_nonneg _)
  have hle : Matrix.trace (centering m * gram X * centering m) ≤
      Matrix.trace (gram X) := by
    rw [trace_compressed_gram hm0 X]
    exact sub_le_self _ hnn
  rw [hTsq, Matrix.trace_smul, smul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_left hle hαpos
  rw [trace_gram_of_unit X hX, alpha_mul_cast m hm0] at hmul
  exact hmul

private lemma unitConfig_of_simplexGram {m d : ℕ} (hm : 1 < m) (V : Config m d)
    (hVgram : gram V = simplexGram m) : UnitConfig V := by
  intro i
  have hii : inner ℝ (V i) (V i) = 1 := by
    rw [← gram_apply, hVgram, simplexGram_diagonal m hm i]
  rw [norm_eq_sqrt_real_inner, hii, Real.sqrt_one]

/-- The chart coefficient read off `procrustesSq_sqrt`. -/
theorem trace_sqrt_eq_chartKappa {m d : ℕ} (hm : 3 ≤ m) (X V : Config m d)
    (hX : UnitConfig X) (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (hK : IsUnit (T + (1 - centering m)))
    (tau : ℝ) (hτ : procrustesSq X V = tau) :
    Matrix.trace T = ((m : ℝ) - 1) * chartKappa m tau := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  have hα : alpha m ≠ 0 := alpha_ne_zero_of_gt_one m hm1
  have hV : UnitConfig V := unitConfig_of_simplexGram hm1 V hVgram
  have hdist := procrustesSq_sqrt hm X V hX hV hVgram T hT hPT hTP hTsq hK
  rw [hτ] at hdist
  have hlin : 2 / alpha m * Matrix.trace T = 2 * (m : ℝ) - tau := by
    linarith
  have htr : Matrix.trace T = alpha m / 2 * (2 * (m : ℝ) - tau) := by
    have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
    have hmul := congrArg (fun z : ℝ => alpha m / 2 * z) hlin
    have hcoef : alpha m / 2 * (2 / alpha m) = 1 := by
      field_simp [hα, h2]
    rw [← mul_assoc, hcoef, one_mul] at hmul
    exact hmul
  rw [htr]
  unfold chartKappa alpha
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  field_simp [hmR, two_ne_zero]

theorem procrustesTau_bounds {m d : ℕ} (hm : 3 ≤ m) (X V : Config m d)
    (hX : UnitConfig X) (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (hK : IsUnit (T + (1 - centering m)))
    (tau : ℝ) (hτ : procrustesSq X V = tau) :
    0 ≤ tau ∧ tau ≤ 2 * (m : ℝ) := by
  have h0 : 0 ≤ tau := by
    rw [← hτ]
    exact procrustesSq_nonneg X V
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hV : UnitConfig V := unitConfig_of_simplexGram hm1 V hVgram
  have hdist := procrustesSq_sqrt hm X V hX hV hVgram T hT hPT hTP hTsq hK
  rw [hτ] at hdist
  have htr0 : 0 ≤ Matrix.trace T := hT.trace_nonneg
  have hαpos : 0 < alpha m := by
    unfold alpha
    exact div_pos (sub_pos.mpr (by exact_mod_cast hm1))
      (by exact_mod_cast (lt_trans (Nat.succ_pos 0) hm1))
  have hprod : 0 ≤ 2 / alpha m * Matrix.trace T :=
    mul_nonneg (div_nonneg zero_le_two (le_of_lt hαpos)) htr0
  have h2 : tau ≤ 2 * (m : ℝ) := by
    linarith
  exact ⟨h0, h2⟩

private lemma chartFactor_le_tau {m : ℕ} (hm : 3 ≤ m) {tau : ℝ} (h0 : 0 ≤ tau) :
    ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) ≤ tau := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hMpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_trans (Nat.succ_pos 0) hm1)
  have hM1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_lt hm1
  set x : ℝ := tau / (2 * (m : ℝ))
  have hκ : chartKappa m tau = 1 - x := by
    unfold chartKappa
    rfl
  have hsq : 1 - chartKappa m tau ^ 2 = x * (2 - x) := by
    rw [hκ]
    ring
  have h2M : 2 * (m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hmR
  have hx2 : 2 - x = (4 * (m : ℝ) - tau) / (2 * (m : ℝ)) := by
    have hmul : (2 - x) * (2 * (m : ℝ)) = 4 * (m : ℝ) - tau := by
      rw [show x = tau / (2 * (m : ℝ)) from rfl]
      field_simp [h2M]
      ring
    exact (eq_div_iff h2M).2 hmul
  have hprod : x * (2 - x) =
      tau * (4 * (m : ℝ) - tau) / (4 * (m : ℝ) ^ 2) := by
    rw [show x = tau / (2 * (m : ℝ)) from rfl, hx2, div_mul_div_comm]
    rw [show (2 * (m : ℝ)) * (2 * (m : ℝ)) = 4 * (m : ℝ) ^ 2 by ring]
  have h4 : 4 * (m : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hmR)
  have hdiff : tau - ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) =
      tau * (4 * (m : ℝ) + ((m : ℝ) - 1) * tau) / (4 * (m : ℝ) ^ 2) := by
    rw [hsq, hprod]
    field_simp [h4]
    ring
  have hnum : 0 ≤ tau * (4 * (m : ℝ) + ((m : ℝ) - 1) * tau) := by
    refine mul_nonneg h0 ?_
    exact add_nonneg (mul_nonneg (by norm_num) (le_of_lt hMpos))
      (mul_nonneg (sub_nonneg.mpr hM1) h0)
  have hden : 0 ≤ 4 * (m : ℝ) ^ 2 :=
    le_of_lt (mul_pos (by norm_num) (pow_pos hMpos 2))
  have hfrac : 0 ≤ tau - ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) := by
    rw [hdiff]
    exact div_nonneg hnum hden
  exact sub_nonneg.mp hfrac

private lemma chartFactor_nonneg {m : ℕ} (hm : 3 ≤ m) {tau : ℝ}
    (h0 : 0 ≤ tau) (h2 : tau ≤ 2 * (m : ℝ)) :
    0 ≤ ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hden : 0 < 2 * (m : ℝ) :=
    mul_pos two_pos (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hκ0 : 0 ≤ chartKappa m tau := by
    unfold chartKappa
    have hdiv : tau / (2 * (m : ℝ)) ≤ 1 := by
      rw [div_le_one hden]
      exact h2
    linarith
  have hκ1 : chartKappa m tau ≤ 1 := by
    unfold chartKappa
    have hdiv : 0 ≤ tau / (2 * (m : ℝ)) := div_nonneg h0 (le_of_lt hden)
    linarith
  have hfac : 0 ≤ 1 - chartKappa m tau ^ 2 := by
    have hdiff : 1 - chartKappa m tau ^ 2 =
        (1 - chartKappa m tau) * (1 + chartKappa m tau) := by
      ring
    rw [hdiff]
    exact mul_nonneg (by linarith) (by linarith)
  have hm1' : 0 ≤ (m : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt hm1)
  exact mul_nonneg hm1' hfac

private lemma deviation_sq {m : ℕ} (hm : m ≠ 0)
    (T : Matrix (Fin m) (Fin m) ℝ) (κ : ℝ)
    (hPT : centering m * T = T) (hTP : T * centering m = T) :
    (T - κ • centering m) * (T - κ • centering m) =
      T * T - (2 * κ) • T + (κ ^ 2) • centering m := by
  have hTPκ : T * (κ • centering m) = κ • T := by
    rw [Matrix.mul_smul, hTP]
  have hPTκ : (κ • centering m) * T = κ • T := by
    rw [Matrix.smul_mul, hPT]
  have hPPκ : (κ • centering m) * (κ • centering m) = (κ ^ 2) • centering m := by
    rw [Matrix.smul_mul, Matrix.mul_smul, centering_mul_self hm, smul_smul, ← pow_two]
  have hstep : (T * T - κ • T) - (κ • T - (κ ^ 2) • centering m) =
      T * T - κ • T - κ • T + (κ ^ 2) • centering m := by
    calc
      (T * T - κ • T) - (κ • T - (κ ^ 2) • centering m)
          = (T * T - κ • T) + ((κ ^ 2) • centering m - κ • T) := by
            rw [sub_eq_add_neg, neg_sub]
      _ = (T * T - κ • T) + (κ ^ 2) • centering m - κ • T := by
            rw [← add_sub_assoc]
      _ = T * T - κ • T - κ • T + (κ ^ 2) • centering m := by
            rw [add_sub_right_comm]
  calc
    (T - κ • centering m) * (T - κ • centering m)
        = T * (T - κ • centering m) -
            (κ • centering m) * (T - κ • centering m) := by
          rw [sub_mul]
    _ = (T * T - T * (κ • centering m)) -
          ((κ • centering m) * T - (κ • centering m) * (κ • centering m)) := by
          rw [mul_sub, mul_sub]
    _ = (T * T - κ • T) - (κ • T - (κ ^ 2) • centering m) := by
          rw [hTPκ, hPTκ, hPPκ]
    _ = T * T - κ • T - κ • T + (κ ^ 2) • centering m := hstep
    _ = T * T - (2 * κ) • T + (κ ^ 2) • centering m := by
          rw [sub_sub, ← add_smul, ← two_mul]

private lemma frobSq_eq_trace_mul_of_isSymm {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    frobSq A = Matrix.trace (A * A) := by
  rw [frobSq, trace_eq_sum_diag]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hA.apply i j]
  ring

theorem shellDeviation_mem_shellSpace {m d : ℕ} (hm : 3 ≤ m) (X V : Config m d)
    (hX : UnitConfig X) (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (hK : IsUnit (T + (1 - centering m)))
    (tau : ℝ) (hτ : procrustesSq X V = tau) :
    T - chartKappa m tau • centering m ∈ shellSpace m := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  set κ : ℝ := chartKappa m tau
  set D : Matrix (Fin m) (Fin m) ℝ := T - κ • centering m
  have hTsym : T.IsSymm := (isHermitian_iff_isSymm).1 hT.isHermitian
  have hPsym : (centering m).transpose = centering m := by
    ext i j
    simp [Matrix.transpose_apply, centering_apply, eq_comm]
  have hDsym : D.IsSymm := by
    unfold Matrix.IsSymm
    dsimp only [D]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hTsym.eq, hPsym]
  have hPD : centering m * D = D := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hPT, centering_mul_self hm0]
  have hDP : D * centering m = D := by
    rw [Matrix.sub_mul, Matrix.smul_mul, hTP, centering_mul_self hm0]
  have htr : Matrix.trace D = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul,
      trace_sqrt_eq_chartKappa hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ,
      trace_centering m hm0, smul_eq_mul]
    ring
  have hcarrier : D.transpose = D ∧ centering m * D = D ∧
      D * centering m = D ∧ Matrix.trace D = 0 :=
    ⟨hDsym, hPD, hDP, htr⟩
  simpa [shellSpace, Set.mem_setOf] using hcarrier

theorem frobSq_shellDeviation {m d : ℕ} (hm : 3 ≤ m) (X V : Config m d)
    (hX : UnitConfig X) (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (hK : IsUnit (T + (1 - centering m)))
    (tau : ℝ) (hτ : procrustesSq X V = tau) :
    frobSq (T - chartKappa m tau • centering m) =
        Matrix.trace (T * T) - chartKappa m tau ^ 2 * ((m : ℝ) - 1) ∧
      frobSq (T - chartKappa m tau • centering m) ≤
        ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) ∧
      ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) ≤ tau ∧
      frobSq (T - chartKappa m tau • centering m) ≤ tau ∧
      0 ≤ ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  have htau := procrustesTau_bounds hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ
  set κ : ℝ := chartKappa m tau
  set D : Matrix (Fin m) (Fin m) ℝ := T - κ • centering m
  have hTsym : T.IsSymm := (isHermitian_iff_isSymm).1 hT.isHermitian
  have hPsym : (centering m).transpose = centering m := by
    ext i j
    simp [Matrix.transpose_apply, centering_apply, eq_comm]
  have hDsym : D.IsSymm := by
    unfold Matrix.IsSymm
    dsimp only [D]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hTsym.eq, hPsym]
  have hsq := deviation_sq hm0 T κ hPT hTP
  have htrace : Matrix.trace (D * D) =
      Matrix.trace (T * T) - κ ^ 2 * ((m : ℝ) - 1) := by
    rw [hsq, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul,
      trace_sqrt_eq_chartKappa hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ,
      trace_centering m hm0]
    ring
  have hid : frobSq D = Matrix.trace (T * T) - κ ^ 2 * ((m : ℝ) - 1) := by
    rw [frobSq_eq_trace_mul_of_isSymm hDsym, htrace]
  have hle1 : frobSq D ≤ ((m : ℝ) - 1) * (1 - κ ^ 2) := by
    rw [hid]
    have hsub : Matrix.trace (T * T) - κ ^ 2 * ((m : ℝ) - 1) ≤
        ((m : ℝ) - 1) - κ ^ 2 * ((m : ℝ) - 1) :=
      sub_le_sub_right (trace_sqrt_sq_le hm X hX T hTsq) _
    have hfac : ((m : ℝ) - 1) - κ ^ 2 * ((m : ℝ) - 1) =
        ((m : ℝ) - 1) * (1 - κ ^ 2) := by
      ring
    linarith
  have hle2 : ((m : ℝ) - 1) * (1 - κ ^ 2) ≤ tau :=
    chartFactor_le_tau hm htau.1
  have hle : frobSq D ≤ tau := le_trans hle1 hle2
  have hnn : 0 ≤ ((m : ℝ) - 1) * (1 - κ ^ 2) :=
    chartFactor_nonneg hm htau.1 htau.2
  exact ⟨hid, hle1, hle2, hle, hnn⟩

private lemma gram_sub_one_isSymm {m d : ℕ} (X : Config m d) :
    (gram X - 1).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [Matrix.sub_apply, Matrix.sub_apply, gram_apply, gram_apply, real_inner_comm]
  simp [Matrix.one_apply, eq_comm]

private lemma gram_sub_one_zeroDiagonal {m d : ℕ} (X : Config m d)
    (hX : UnitConfig X) : zeroDiagonal (gram X - 1) := by
  intro i
  rw [Matrix.sub_apply, gram_diagonal_unit X hX i, Matrix.one_apply_eq, sub_self]

private lemma uncompress_add {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    uncompress (A + B) = uncompress A + uncompress B := by
  ext i j
  simp only [uncompress, Matrix.add_apply]
  ring

private lemma uncompress_smul {m : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    uncompress (c • A) = c • uncompress A := by
  ext i j
  simp only [uncompress, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma uncompress_centering (m : ℕ) :
    uncompress (centering m) = 1 - onesMatrix m := by
  ext i j
  by_cases hij : i = j
  · subst hij
    show centering m i i - (centering m i i + centering m i i) / 2 =
      (1 : Matrix (Fin m) (Fin m) ℝ) i i - onesMatrix m i i
    rw [centering_apply_diag, Matrix.one_apply_eq]
    simp only [onesMatrix]
    ring
  · show centering m i j - (centering m i i + centering m j j) / 2 =
      (1 : Matrix (Fin m) (Fin m) ℝ) i j - onesMatrix m i j
    rw [centering_apply, centering_apply_diag, centering_apply_diag, if_neg hij]
    simp only [onesMatrix, Matrix.one_apply, hij, if_false]
    ring

private lemma compression_gram_sub_one {m d : ℕ} (hm : m ≠ 0) (X : Config m d) :
    compression (gram X - 1) =
      centering m * gram X * centering m - centering m := by
  rw [compression]
  have hleft : centering m * (gram X - 1) = centering m * gram X - centering m := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [hleft]
  have hright : (centering m * gram X - centering m) * centering m =
      centering m * gram X * centering m - centering m * centering m := by
    rw [sub_mul]
  rw [hright, centering_mul_self hm]

/-- Shell covariance reconstructs `α • gram X + m⁻¹ • J` from the unit diagonal. -/
theorem shellCovariance_sqrt {m d : ℕ} (hm : 3 ≤ m) (X : Config m d)
    (hX : UnitConfig X) (T : Matrix (Fin m) (Fin m) ℝ)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (tau : ℝ) :
    shellCovariance m tau (T - chartKappa m tau • centering m) =
      (alpha m) • gram X + (m : ℝ)⁻¹ • onesMatrix m := by
  have h2lt : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) h2lt
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  set κ : ℝ := chartKappa m tau
  set D : Matrix (Fin m) (Fin m) ℝ := T - κ • centering m
  have hTD : κ • centering m + D = T := by
    rw [← add_sub_assoc, add_comm, add_sub_cancel_right]
  have hC : squareShellC m tau D =
      (alpha m) • (centering m * gram X * centering m) - centering m := by
    unfold squareShellC
    rw [hTD, hTsq]
  have hsplit : squareShellC m tau D =
      (alpha m) • compression (gram X - 1) + (alpha m - 1) • centering m := by
    rw [hC]
    have hcomp := compression_gram_sub_one hm0 X
    have hre : centering m * gram X * centering m =
        compression (gram X - 1) + centering m := by
      rw [hcomp]
      exact (sub_add_cancel (centering m * gram X * centering m) (centering m)).symm
    rw [hre, smul_add, add_sub_assoc]
    congr 1
    calc
      (alpha m) • centering m - centering m
          = (alpha m) • centering m - (1 : ℝ) • centering m := by
            rw [one_smul]
      _ = (alpha m - 1) • centering m := by
            rw [← sub_smul]
  have hun : uncompress (squareShellC m tau D) =
      (alpha m) • (gram X - 1) + (alpha m - 1) • (1 - onesMatrix m) := by
    rw [hsplit, uncompress_add, uncompress_smul, uncompress_smul,
      uncompress_compression_of_symm_zeroDiagonal (gram_sub_one_isSymm X)
        (gram_sub_one_zeroDiagonal X hX),
      uncompress_centering]
  have hlift : shellLift (squareShellC m tau D) = uncompress (squareShellC m tau D) := rfl
  rw [shellCovariance, hlift, hun]
  have hα1 : alpha m - 1 = - (m : ℝ)⁻¹ := by
    rw [alpha_eq_one_sub_inv m hm0]
    ring
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      onesMatrix, if_true, smul_eq_mul]
    rw [hα1, alpha_eq_one_sub_inv m hm0]
    ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      onesMatrix, if_neg hij, smul_eq_mul]
    rw [hα1]
    ring

theorem shell_enclosure {m d : ℕ} (hm : 3 ≤ m) (X V : Config m d)
    (hX : UnitConfig X) (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (hK : IsUnit (T + (1 - centering m)))
    (tau : ℝ) (hτ : procrustesSq X V = tau) :
    0 ≤ tau ∧ tau ≤ 2 * (m : ℝ) ∧
      Matrix.trace T = ((m : ℝ) - 1) * chartKappa m tau ∧
      Matrix.trace (T * T) ≤ (m : ℝ) - 1 ∧
      T - chartKappa m tau • centering m ∈ shellSpace m ∧
      frobSq (T - chartKappa m tau • centering m) =
        Matrix.trace (T * T) - chartKappa m tau ^ 2 * ((m : ℝ) - 1) ∧
      frobSq (T - chartKappa m tau • centering m) ≤
        ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) ∧
      ((m : ℝ) - 1) * (1 - chartKappa m tau ^ 2) ≤ tau ∧
      frobSq (T - chartKappa m tau • centering m) ≤ tau ∧
      shellCovariance m tau (T - chartKappa m tau • centering m) =
        (alpha m) • gram X + (m : ℝ)⁻¹ • onesMatrix m := by
  have htau := procrustesTau_bounds hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ
  have htr := trace_sqrt_eq_chartKappa hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ
  have hsq := trace_sqrt_sq_le hm X hX T hTsq
  have hmem := shellDeviation_mem_shellSpace hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ
  have hfrob := frobSq_shellDeviation hm X V hX hVgram T hT hPT hTP hTsq hK tau hτ
  have hcov := shellCovariance_sqrt hm X hX T hTsq tau
  exact ⟨htau.1, htau.2, htr, hsq, hmem, hfrob.1, hfrob.2.1, hfrob.2.2.1,
    hfrob.2.2.2.1, hcov⟩

#print axioms trace_sqrt_sq_le
#print axioms trace_sqrt_eq_chartKappa
#print axioms procrustesTau_bounds
#print axioms shellDeviation_mem_shellSpace
#print axioms frobSq_shellDeviation
#print axioms shellCovariance_sqrt
#print axioms shell_enclosure

end SimplexFull.Geometry
