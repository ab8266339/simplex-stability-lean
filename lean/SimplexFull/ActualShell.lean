import SimplexFull.ActualProcrustes
import SimplexFull.CenteredSqrt
import SimplexFull.CovarianceGeometry
import SimplexFull.ShellEnclosure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
Instantiated square-root shell.

`centeredRoot` supplies the matrix `T`. Near a regular simplex, `rootCompletion`
is a unit, so `ShellEnclosure.shell_enclosure` applies with no extra matrix
hypotheses. `frobSq` controls the Euclidean operator norm by Cauchy-Schwarz.
-/

set_option maxHeartbeats 800000

noncomputable section

open Finset Matrix WithLp
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder RealInnerProductSpace

namespace SimplexFull.Geometry

/-- Deviation of the centered square root from the chart ray. -/
def actualDeviation {m d : ℕ} (X : Config m d) (tau : ℝ) : ShapeMatrix m :=
  centeredRoot X - chartKappa m tau • centering m

lemma actual_frobSq_nonneg {m : ℕ} (A : ShapeMatrix m) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma l2_opNorm_le_sqrt_frobSq {m : ℕ} (A : ShapeMatrix m) :
    ‖A‖ ≤ Real.sqrt (frobSq A) := by
  rw [← l2_opNorm_toEuclideanCLM (n := Fin m) (𝕜 := ℝ)]
  refine (toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A).opNorm_le_bound (Real.sqrt_nonneg _) ?_
  intro x
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (actual_frobSq_nonneg A)]
  rw [EuclideanSpace.real_norm_sq_eq]
  have hcoord : ∀ i, (toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A x) i =
      ∑ j, A i j * (ofLp x) j := by
    intro i
    rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  simp_rw [hcoord]
  have hcs : ∀ i, (∑ j, A i j * ofLp x j) ^ 2 ≤
      (∑ j, (A i j) ^ 2) * ∑ j, (ofLp x j) ^ 2 :=
    fun i => sum_mul_sq_le_sq_mul_sq univ (fun j => A i j) (fun j => ofLp x j)
  refine le_trans (Finset.sum_le_sum fun i _ => hcs i) ?_
  rw [← Finset.sum_mul]
  unfold frobSq
  have hx : ∑ j, (ofLp x j) ^ 2 = ‖x‖ ^ 2 :=
    (EuclideanSpace.real_norm_sq_eq x).symm
  rw [hx]

lemma l2_opNorm_sq_le_frobSq {m : ℕ} (A : ShapeMatrix m) :
    ‖A‖ ^ 2 ≤ frobSq A := by
  have h := l2_opNorm_le_sqrt_frobSq A
  have hmul := mul_self_le_mul_self (norm_nonneg _) h
  rw [← pow_two, ← pow_two, Real.sq_sqrt (actual_frobSq_nonneg A)] at hmul
  exact hmul

/-- A small Frobenius sum forces a small Euclidean operator norm. -/
theorem exists_frobSq_opNorm {m : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ∃ eta > 0, ∀ A : ShapeMatrix m, frobSq A < eta → ‖A‖ < eps := by
  refine ⟨eps ^ 2, pow_pos heps 2, ?_⟩
  intro A hA
  have hsqrt : Real.sqrt (frobSq A) < eps := by
    rw [← Real.sqrt_sq heps.le]
    exact Real.sqrt_lt_sqrt (actual_frobSq_nonneg A) hA
  exact lt_of_le_of_lt (l2_opNorm_le_sqrt_frobSq A) hsqrt

theorem exists_actualShell {m d : ℕ} (hm : 3 ≤ m) (V : Config m d)
    (regularV : gram V = simplexGram m) :
    ∃ delta > 0, ∀ (X : Config m d) (tau : ℝ),
      UnitConfig X → procrustesSq X V = tau → tau < delta →
        actualDeviation X tau ∈ shellSpace m ∧
        frobSq (actualDeviation X tau) ≤ tau ∧
        shellCovariance m tau (actualDeviation X tau) = channelCovariance X ∧
        ‖actualDeviation X tau‖ ^ 2 ≤ frobSq (actualDeviation X tau) ∧
        ‖actualDeviation X tau‖ ≤ Real.sqrt tau := by
  have hm1 : 1 < m := by omega
  have hm0 : 1 ≤ m := by omega
  obtain ⟨delta, hdelta, hunit⟩ :=
    exists_procrustes_neighborhood_isUnit V hm1 regularV
  refine ⟨delta, hdelta, ?_⟩
  intro X tau hX hτ hlt
  have hclose : procrustesSq X V < delta := by rwa [hτ]
  obtain ⟨hPT, hTP⟩ := centered_mul_centering (centeredRoot_centered X hm0)
  have hTsq : centeredRoot X * centeredRoot X =
      (alpha m) • (centering m * gram X * centering m) := by
    rw [centeredRoot_mul_self X hm0, centeredGram, compression]
  have hK : IsUnit (centeredRoot X + (1 - centering m)) := by
    simpa [rootCompletion] using hunit X hclose
  have henc := shell_enclosure hm X V hX regularV (centeredRoot X)
    (centeredRoot_posSemidef X) hPT hTP hTsq hK tau hτ
  rcases henc with ⟨_, _, _, _, hmem, _, _, _, hle, hcov⟩
  have hmem' : actualDeviation X tau ∈ shellSpace m := by
    dsimp [actualDeviation]
    exact hmem
  have hle' : frobSq (actualDeviation X tau) ≤ tau := by
    dsimp [actualDeviation]
    exact hle
  have hcov' : shellCovariance m tau (actualDeviation X tau) = channelCovariance X := by
    dsimp [actualDeviation, channelCovariance]
    exact hcov
  have hnorm : ‖actualDeviation X tau‖ ≤ Real.sqrt tau :=
    calc
      ‖actualDeviation X tau‖ ≤ Real.sqrt (frobSq (actualDeviation X tau)) :=
        l2_opNorm_le_sqrt_frobSq _
      _ ≤ Real.sqrt tau := Real.sqrt_le_sqrt hle'
  exact ⟨hmem', hle', hcov', l2_opNorm_sq_le_frobSq _, hnorm⟩

theorem exists_actualShell_opNorm {m d : ℕ} (hm : 3 ≤ m) (V : Config m d)
    (regularV : gram V = simplexGram m) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ (X : Config m d) (tau : ℝ),
      UnitConfig X → procrustesSq X V = tau → tau < delta →
        ‖actualDeviation X tau‖ < eps := by
  obtain ⟨delta0, hdelta0, hpack⟩ := exists_actualShell hm V regularV
  refine ⟨min delta0 (eps ^ 2), (lt_min_iff).mpr ⟨hdelta0, pow_pos heps 2⟩, ?_⟩
  intro X tau hX hτ hlt
  obtain ⟨hlt0, hlte⟩ := (lt_min_iff).mp hlt
  obtain ⟨_, _, _, _, hnorm⟩ := hpack X tau hX hτ hlt0
  have hτ0 : 0 ≤ tau := by
    rw [← hτ]
    exact procrustesSq_nonneg X V
  have hsqrt : Real.sqrt tau < eps := by
    rw [← Real.sqrt_sq heps.le]
    exact Real.sqrt_lt_sqrt hτ0 hlte
  exact lt_of_le_of_lt hnorm hsqrt

private lemma centeredGram_normalConfig {m d : ℕ} (hm : 1 < m) (k t : ℝ)
    (V : Config m d) (z : EuclideanSpace ℝ (Fin d))
    (hVgram : gram V = simplexGram m)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) :
    centeredGram (normalConfig k t V z) = (k ^ 2) • centering m := by
  have hm0 : m ≠ 0 := (Nat.lt_trans Nat.zero_lt_one hm).ne'
  have hα : alpha m ≠ 0 := alpha_ne_zero_of_gt_one m hm
  have hP : centering m * centering m = centering m := centering_idempotent hm0
  have hgram : gram (normalConfig k t V z) =
      k ^ 2 • ((alpha m)⁻¹ • centering m) + t ^ 2 • onesMatrix m := by
    rw [gram_normalConfig k t V z hperp hz, hVgram, simplexGram]
  have hray : k ^ 2 • ((alpha m)⁻¹ • centering m) =
      (k ^ 2 * (alpha m)⁻¹) • centering m := by
    rw [smul_smul]
  have hkill : centering m * (t ^ 2 • onesMatrix m) * centering m = 0 := by
    rw [Matrix.mul_smul, centering_mul_onesMatrix hm0, smul_zero, Matrix.zero_mul]
  have hmain : centering m * ((k ^ 2 * (alpha m)⁻¹) • centering m) * centering m =
      (k ^ 2 * (alpha m)⁻¹) • centering m := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hP, hP]
  rw [centeredGram, compression, hgram, Matrix.mul_add, Matrix.add_mul, hkill, add_zero,
    hray, hmain, smul_smul]
  congr 1
  rw [mul_left_comm, mul_inv_cancel₀ hα, mul_one]

theorem centeredRoot_normalConfig {m d : ℕ} (hm : 1 < m) (k t : ℝ)
    (V : Config m d) (z : EuclideanSpace ℝ (Fin d)) (hk : 0 ≤ k)
    (hVgram : gram V = simplexGram m)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) :
    centeredRoot (normalConfig k t V z) = k • centering m := by
  have hm0 : m ≠ 0 := (Nat.lt_trans Nat.zero_lt_one hm).ne'
  have hsq : (k • centering m) * (k • centering m) = (k ^ 2) • centering m := by
    rw [Matrix.smul_mul, Matrix.mul_smul, centering_idempotent hm0, smul_smul, ← pow_two]
  rw [centeredRoot, centeredGram_normalConfig hm k t V z hVgram hperp hz]
  exact CFC.sqrt_unique hsq ((centering_posSemidef hm0).smul hk).nonneg

theorem actualDeviation_normalConfig {m d : ℕ} (hm : 3 ≤ m) (k t : ℝ)
    (V : Config m d) (z : EuclideanSpace ℝ (Fin d)) (hk : 0 ≤ k)
    (hVgram : gram V = simplexGram m)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1)
    (hkt : k ^ 2 + t ^ 2 = 1) :
    actualDeviation (normalConfig k t V z)
        (procrustesSq (normalConfig k t V z) V) = 0 := by
  have hm1 : 1 < m := by omega
  have hm0 : m ≠ 0 := (Nat.lt_trans Nat.zero_lt_one hm1).ne'
  have hV : UnitConfig V := unitConfig_of_simplexGram V hm1 hVgram
  have hsum : ∑ i, V i = 0 := config_barycenter_of_simplexGram V hm0 hVgram
  have hdist := procrustesSq_normalConfig k t V z hV hsum hperp hz hk hkt
  rw [actualDeviation, hdist, centeredRoot_normalConfig hm1 k t V z hk hVgram hperp hz]
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hden : 2 * (m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hmR
  have hκ : chartKappa m (2 * (m : ℝ) * (1 - k)) = k := by
    unfold chartKappa
    rw [mul_div_cancel_left₀ (1 - k) hden]
    ring
  rw [hκ, sub_self]

#print axioms l2_opNorm_le_sqrt_frobSq
#print axioms l2_opNorm_sq_le_frobSq
#print axioms exists_frobSq_opNorm
#print axioms exists_actualShell
#print axioms exists_actualShell_opNorm
#print axioms centeredRoot_normalConfig
#print axioms actualDeviation_normalConfig

end SimplexFull.Geometry
