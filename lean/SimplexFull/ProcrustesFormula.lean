import SimplexFull.GeometryBase
import SimplexFull.Procrustes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-!
Centered Procrustes square root, without a singular value decomposition.

`recombine X A` is the configuration `j ↦ ∑ i, A i j • X i`.
Its Gram is `Aᵀ * gram X * A`. `configDot` is the configuration pairing and
`weightedGram T` is the Gram-weighted pairing `∑ i j, T i j ⟪X i, Y j⟫`.

`procrustesSq_sqrt` turns concrete matrix hypotheses on a positive semidefinite
`T` — support on the centering projector, `T * T = α • (P * gram X * P)`, and
invertibility of `T + (1 - P)` — into the squared orthogonal distance from `X`
to a unit simplex configuration.
-/

noncomputable section

open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace SimplexFull.Geometry

/-- Recombination `j ↦ ∑ i, A i j • X i`. -/
def recombine {m d : ℕ} (X : Config m d) (A : Matrix (Fin m) (Fin m) ℝ) : Config m d :=
  fun j => synthesis X (fun i => A i j)

@[simp] theorem recombine_apply {m d : ℕ} (X : Config m d)
    (A : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    recombine X A j = ∑ i, A i j • X i := by
  simp [recombine, synthesis_apply]

theorem recombine_add {m d : ℕ} (X : Config m d)
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    recombine X (A + B) = recombine X A + recombine X B := by
  funext j
  simp [recombine_apply, add_smul, sum_add_distrib, Pi.add_apply]

theorem recombine_smul {m d : ℕ} (c : ℝ) (X : Config m d)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    recombine X (c • A) = c • recombine X A := by
  funext j
  simp [recombine_apply, smul_smul, mul_comm c, smul_sum, Pi.smul_apply]

theorem recombine_one {m d : ℕ} (X : Config m d) :
    recombine X (1 : Matrix (Fin m) (Fin m) ℝ) = X := by
  funext j
  simp only [recombine_apply, Matrix.one_apply]
  simp_rw [ite_smul, one_smul, zero_smul]
  have hflip : (∑ i, if i = j then X i else 0) = ∑ i, if j = i then X i else 0 := by
    refine sum_congr rfl fun i _ => ?_
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hflip]
  exact Fintype.sum_ite_eq j X

theorem recombine_mul {m d : ℕ} (X : Config m d)
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    recombine (recombine X A) B = recombine X (A * B) := by
  funext j
  simp only [recombine_apply, smul_sum, smul_smul]
  simp_rw [mul_comm (B _ j) (A _ _)]
  rw [sum_comm]
  simp_rw [← sum_smul, mul_apply]

/-- Gram of a recombined configuration: `gram (X A) = Aᵀ (gram X) A`. -/
theorem gram_recombine {m d : ℕ} (X : Config m d)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    gram (recombine X A) = A.transpose * gram X * A := by
  ext j k
  rw [gram_apply]
  calc
    inner ℝ (recombine X A j) (recombine X A k)
        = inner ℝ (∑ i, A i j • X i) (∑ p, A p k • X p) := by
            simp [recombine_apply]
    _ = ∑ i, ∑ p, A i j * A p k * inner ℝ (X i) (X p) := by
          simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    _ = ∑ p, ∑ i, A i j * inner ℝ (X i) (X p) * A p k := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ => sum_congr rfl fun p _ => ?_
          ring
    _ = ∑ p, (∑ i, A i j * gram X i p) * A p k := by
          simp_rw [← gram_apply, sum_mul]
    _ = (A.transpose * gram X * A) j k := by
          simp [mul_apply, transpose_apply]

/-- Sum of pointwise inner products of two configurations. -/
def configDot {m d : ℕ} (X Y : Config m d) : ℝ :=
  ∑ i, inner ℝ (X i) (Y i)

theorem configDot_comm {m d : ℕ} (X Y : Config m d) :
    configDot X Y = configDot Y X := by
  simp_rw [configDot, real_inner_comm]

theorem configDot_sub_left {m d : ℕ} (X Y Z : Config m d) :
    configDot (X - Y) Z = configDot X Z - configDot Y Z := by
  simp [configDot, Pi.sub_apply, inner_sub_left, sum_sub_distrib]

theorem configDot_sub_right {m d : ℕ} (X Y Z : Config m d) :
    configDot X (Y - Z) = configDot X Y - configDot X Z := by
  simp [configDot, Pi.sub_apply, inner_sub_right, sum_sub_distrib]

theorem configDot_self_eq_trace_gram {m d : ℕ} (X : Config m d) :
    configDot X X = Matrix.trace (gram X) := by
  simp [configDot, Matrix.trace, diag_apply, gram_apply]

/-- Gram-weighted pairing `∑ i j, T i j ⟪X i, Y j⟫`. -/
def weightedGram {m d : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (X Y : Config m d) : ℝ :=
  ∑ i, ∑ j, T i j * inner ℝ (X i) (Y j)

theorem weightedGram_eq_configDot_recombine {m d : ℕ}
    (T : Matrix (Fin m) (Fin m) ℝ) (X Y : Config m d) :
    weightedGram T X Y = configDot (recombine X T) Y := by
  unfold weightedGram configDot
  simp_rw [recombine_apply, sum_inner, real_inner_smul_left]
  rw [sum_comm]

theorem weightedGram_eq_configDot_recombine_transpose {m d : ℕ}
    (T : Matrix (Fin m) (Fin m) ℝ) (X Y : Config m d) :
    weightedGram T X Y = configDot X (recombine Y T.transpose) := by
  unfold weightedGram configDot
  simp_rw [recombine_apply, inner_sum, real_inner_smul_right, transpose_apply]

theorem configDot_eq_weightedGram_one {m d : ℕ} (X Y : Config m d) :
    configDot X Y = weightedGram (1 : Matrix (Fin m) (Fin m) ℝ) X Y := by
  unfold configDot weightedGram
  simp_rw [one_apply, ite_mul, one_mul, zero_mul]
  refine sum_congr rfl fun i _ => ?_
  exact (Fintype.sum_ite_eq i (fun j => inner ℝ (X i) (Y j))).symm

theorem weightedGram_comm_of_isSymm {m d : ℕ}
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsSymm) (X Y : Config m d) :
    weightedGram T X Y = weightedGram T Y X := by
  unfold weightedGram
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  rw [hT.apply j i, ← real_inner_comm (X i) (Y j)]

theorem weightedGram_self_eq_trace {m d : ℕ}
    (T : Matrix (Fin m) (Fin m) ℝ) (X : Config m d) :
    weightedGram T X X = Matrix.trace (T * gram X) := by
  unfold weightedGram
  simp_rw [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, gram_apply]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (X i) (X j)]

theorem weightedGram_sub_sub {m d : ℕ}
    (T : Matrix (Fin m) (Fin m) ℝ) (X Y : Config m d) :
    weightedGram T (X - Y) (X - Y) =
      weightedGram T X X - weightedGram T X Y - weightedGram T Y X +
        weightedGram T Y Y := by
  have hinner : ∀ i j, inner ℝ ((X - Y) i) ((X - Y) j) =
      inner ℝ (X i) (X j) - inner ℝ (X i) (Y j) - inner ℝ (Y i) (X j) +
        inner ℝ (Y i) (Y j) := by
    intro i j
    simp only [Pi.sub_apply]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  unfold weightedGram
  simp_rw [hinner]
  have hdist : ∀ i j,
      T i j * (inner ℝ (X i) (X j) - inner ℝ (X i) (Y j) - inner ℝ (Y i) (X j) +
        inner ℝ (Y i) (Y j)) =
      T i j * inner ℝ (X i) (X j) - T i j * inner ℝ (X i) (Y j) -
        T i j * inner ℝ (Y i) (X j) + T i j * inner ℝ (Y i) (Y j) := by
    intro i j
    ring
  simp_rw [hdist]
  simp only [sum_sub_distrib, sum_add_distrib]

lemma euclidean_inner_eq_sum {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x y = ∑ k, x k * y k := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, star_trivial, mul_comm]

theorem weightedGram_self_nonneg {m d : ℕ}
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef) (Y : Config m d) :
    0 ≤ weightedGram T Y Y := by
  have htriple : weightedGram T Y Y =
      ∑ i, ∑ j, ∑ k : Fin d, T i j * (Y i k) * (Y j k) := by
    unfold weightedGram
    simp_rw [euclidean_inner_eq_sum, Finset.mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    ring
  have hreorder :
      (∑ i, ∑ j, ∑ k : Fin d, T i j * (Y i k) * (Y j k)) =
        ∑ k, ∑ i, ∑ j, T i j * (Y i k) * (Y j k) := by
    have h1 :
        (∑ i, ∑ j, ∑ k : Fin d, T i j * (Y i k) * (Y j k)) =
          ∑ i, ∑ k, ∑ j, T i j * (Y i k) * (Y j k) := by
      refine sum_congr rfl fun i _ => ?_
      exact sum_comm
    rw [h1, sum_comm]
  rw [htriple, hreorder]
  refine sum_nonneg fun k _ => ?_
  have hquad : 0 ≤ dotProduct (fun i => Y i k) (T *ᵥ fun i => Y i k) := by
    simpa [star_trivial] using hT.dotProduct_mulVec_nonneg (fun i => Y i k)
  have hform : ∑ i, ∑ j, T i j * (Y i k) * (Y j k) =
      dotProduct (fun i => Y i k) (Matrix.mulVec T (fun i => Y i k)) := by
    simp_rw [dotProduct, Matrix.mulVec, dotProduct]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hform]
  exact hquad

lemma procrustes_onesMatrix_mul_self (m : ℕ) :
    onesMatrix m * onesMatrix m = (m : ℝ) • onesMatrix m := by
  ext i k
  simp [Matrix.mul_apply, Matrix.smul_apply, onesMatrix, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

lemma centering_apply (m : ℕ) (i j : Fin m) :
    centering m i j = (if i = j then (1 : ℝ) else 0) - (m : ℝ)⁻¹ := by
  simp [centering, onesMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_one]

lemma procrustes_centering_isSymm (m : ℕ) : (centering m).IsSymm := by
  refine IsSymm.ext ?_
  intro i j
  simp [centering_apply, eq_comm]

lemma centering_mul_self {m : ℕ} (hm : m ≠ 0) :
    centering m * centering m = centering m := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [centering]
  set c : ℝ := (m : ℝ)⁻¹
  have hc : c * (m : ℝ) = 1 := inv_mul_cancel₀ hmR
  have hJ : onesMatrix m * onesMatrix m = (m : ℝ) • onesMatrix m := procrustes_onesMatrix_mul_self m
  calc
    (1 - c • onesMatrix m) * (1 - c • onesMatrix m)
        = 1 * (1 - c • onesMatrix m) -
            (c • onesMatrix m) * (1 - c • onesMatrix m) := by
          rw [sub_mul]
    _ = (1 - c • onesMatrix m) -
          ((c • onesMatrix m) * 1 - (c • onesMatrix m) * (c • onesMatrix m)) := by
          rw [one_mul, mul_sub]
    _ = (1 - c • onesMatrix m) -
          (c • onesMatrix m - (c * c) • (onesMatrix m * onesMatrix m)) := by
          have hcc : (c • onesMatrix m) * (c • onesMatrix m) =
              (c * c) • (onesMatrix m * onesMatrix m) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          rw [hcc, Matrix.smul_mul, Matrix.mul_one]
    _ = (1 - c • onesMatrix m) -
          (c • onesMatrix m - (c * c * (m : ℝ)) • onesMatrix m) := by
          rw [hJ, smul_smul]
    _ = (1 - c • onesMatrix m) - (c • onesMatrix m - c • onesMatrix m) := by
          rw [show c * c * (m : ℝ) = c by rw [mul_assoc, hc, mul_one]]
    _ = 1 - c • onesMatrix m := by
          simp

/-- Centered configuration `j ↦ ∑ i, P i j • X i`. -/
def centeredConfig {m d : ℕ} (X : Config m d) : Config m d :=
  recombine X (centering m)

theorem centeredConfig_apply {m d : ℕ} (X : Config m d) (j : Fin m) :
    centeredConfig X j = X j - (m : ℝ)⁻¹ • ∑ i, X i := by
  unfold centeredConfig
  rw [recombine_apply]
  simp_rw [centering_apply, sub_smul, sum_sub_distrib]
  have hpick : ∑ i, (if i = j then (1 : ℝ) else 0) • X i = X j := by
    simp_rw [ite_smul, one_smul, zero_smul]
    have hflip : (∑ i, if i = j then X i else 0) = ∑ i, if j = i then X i else 0 := by
      refine sum_congr rfl fun i _ => ?_
      by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h]
    rw [hflip]
    exact Fintype.sum_ite_eq j X
  have hshift : ∑ i, (m : ℝ)⁻¹ • X i = (m : ℝ)⁻¹ • ∑ i, X i := by
    rw [← Finset.smul_sum]
  rw [hpick, hshift]

theorem configDot_centered_of_sum_zero {m d : ℕ} (X Z : Config m d)
    (hZ : ∑ i, Z i = 0) :
    configDot (centeredConfig X) Z = configDot X Z := by
  simp_rw [configDot, centeredConfig_apply, inner_sub_left, real_inner_smul_left,
    Finset.sum_sub_distrib]
  have htail : ∑ i, (m : ℝ)⁻¹ * inner ℝ (∑ j, X j) (Z i) = 0 := by
    rw [← Finset.mul_sum, ← inner_sum, hZ, inner_zero_right, mul_zero]
  rw [htail, sub_zero]

theorem procrustesEnergy_unit {m d : ℕ} (X V : Config m d)
    (hX : UnitConfig X) (hV : UnitConfig V) (U : OrthogonalMotion d) :
    procrustesEnergy X V U =
      2 * (m : ℝ) - 2 * configDot X (fun i => U (V i)) := by
  unfold procrustesEnergy configDot
  have hsq : ∀ i, ‖X i - U (V i)‖ ^ 2 = 2 - 2 * inner ℝ (X i) (U (V i)) := by
    intro i
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, hX i, hV i]
    ring
  simp_rw [hsq, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma trace_mul_simplexGram_of_centering {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ)
    (hTP : T * centering m = T) :
    Matrix.trace (T * simplexGram m) = (alpha m)⁻¹ * Matrix.trace T := by
  rw [simplexGram, Matrix.mul_smul, Matrix.trace_smul, hTP, smul_eq_mul]

/-- Squared orthogonal Procrustes distance from a unit configuration `X` to a
unit simplex configuration `V`.

`T` is any real matrix satisfying the stated algebraic hypotheses. Constructing
`T` as a continuous functional calculus square root is left to the caller. -/
theorem procrustesSq_sqrt {m d : ℕ} (hm : 3 ≤ m) (X V : Config m d)
    (hX : UnitConfig X) (hV : UnitConfig V) (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hPT : centering m * T = T) (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m))
    (hK : IsUnit (T + (1 - centering m))) :
    procrustesSq X V = 2 * (m : ℝ) - 2 / alpha m * Matrix.trace T := by
  have hm2 : 2 < m := Nat.lt_of_succ_le hm
  have hm1 : 1 < m := lt_trans (Nat.lt_succ_self 1) hm2
  have hm0 : m ≠ 0 := (lt_trans (Nat.succ_pos 0) hm1).ne'
  have hα : alpha m ≠ 0 := alpha_ne_zero_of_gt_one m hm1
  let P : Matrix (Fin m) (Fin m) ℝ := centering m
  let K : Matrix (Fin m) (Fin m) ℝ := T + (1 - P)
  have hP2 : P * P = P := centering_mul_self hm0
  have hPsym : P.IsSymm := procrustes_centering_isSymm m
  have hTsym : T.IsSymm := (isHermitian_iff_isSymm).1 hT.isHermitian
  have hdet : IsUnit K.det := (isUnit_iff_isUnit_det K).1 hK
  have hKmul : K * K⁻¹ = 1 := mul_nonsing_inv K hdet
  have hmulK : K⁻¹ * K = 1 := nonsing_inv_mul K hdet
  have hKP : K * P = T := by
    dsimp only [K]
    rw [add_mul, sub_mul, one_mul, hTP, hP2]
    simp
  have hPK : P * K = T := by
    dsimp only [K]
    rw [mul_add, mul_sub, mul_one, hPT, hP2]
    simp
  have hKinvT : K⁻¹ * T = P := by
    rw [← hKP, ← mul_assoc, hmulK, one_mul]
  have hTKinv : T * K⁻¹ = P := by
    rw [← hPK, mul_assoc, hKmul, mul_one]
  let A : Matrix (Fin m) (Fin m) ℝ := P * K⁻¹
  have hAT : A * T = P := by
    dsimp only [A]
    rw [mul_assoc, hKinvT, hP2]
  have hTA : T * A = P := by
    dsimp only [A]
    rw [← mul_assoc, hTP, hTKinv]
  have hKsym : K.IsSymm := by
    unfold Matrix.IsSymm
    dsimp only [K]
    rw [transpose_add, transpose_sub, transpose_one, hTsym.eq, hPsym.eq]
  have hKinvSym : (K⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_nonsing_inv, hKsym.eq]
  have hAcomm : K⁻¹ * P = A := by
    rw [← hTKinv, ← mul_assoc, hKinvT]
  have hAsym : A.IsSymm := by
    unfold Matrix.IsSymm
    dsimp only [A]
    rw [transpose_mul, hKinvSym.eq, hPsym.eq]
    exact hAcomm
  have hPA : P * A = A := by
    dsimp only [A]
    rw [← mul_assoc, hP2]
  have hAP : A * P = A := by
    dsimp only [A]
    rw [mul_assoc, hAcomm, hPA]
  let W : Config m d := recombine X A
  have hPGP : P * gram X * P = (alpha m)⁻¹ • (T * T) := by
    rw [hTsq, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hstart : ((A * P) * gram X) * (P * A) = (A * gram X) * A := by
    rw [hAP, hPA]
  have hfinish : ((A * P) * gram X) * (P * A) = (A * (P * gram X * P)) * A := by
    calc
      ((A * P) * gram X) * (P * A)
          = (A * P) * (gram X * (P * A)) := mul_assoc _ _ _
      _ = (A * P) * ((gram X * P) * A) :=
            congrArg (fun M => (A * P) * M) (mul_assoc _ _ _).symm
      _ = ((A * P) * (gram X * P)) * A := (mul_assoc _ _ _).symm
      _ = (A * (P * (gram X * P))) * A :=
            congrArg (fun M => M * A) (mul_assoc _ _ _)
      _ = (A * ((P * gram X) * P)) * A :=
            congrArg (fun M => (A * M) * A) (mul_assoc _ _ _).symm
      _ = (A * (P * gram X * P)) * A := rfl
  have hATTA : (A * (T * T)) * A = P := by
    have h1 : A * (T * T) = (A * T) * T := (Matrix.mul_assoc A T T).symm
    calc
      (A * (T * T)) * A = ((A * T) * T) * A := congrArg (fun M => M * A) h1
      _ = (A * T) * (T * A) := Matrix.mul_assoc (A * T) T A
      _ = P * (T * A) := congrArg (fun M => M * (T * A)) hAT
      _ = P * P := congrArg (fun M => P * M) hTA
      _ = P := hP2
  have hgramW : gram W = simplexGram m := by
    rw [gram_recombine, hAsym.eq, ← hstart, hfinish, hPGP, Matrix.mul_smul, Matrix.smul_mul,
      hATTA, simplexGram]
  have hXP : centeredConfig X = recombine W T := by
    symm
    dsimp only [centeredConfig, W]
    rw [recombine_mul, hAT]
  have hWW : weightedGram T W W = Matrix.trace T / alpha m := by
    rw [weightedGram_self_eq_trace, hgramW, trace_mul_simplexGram_of_centering T hTP,
      mul_comm, ← div_eq_mul_inv]
  have hcross : ∀ Z : Config m d, gram Z = simplexGram m →
      configDot (centeredConfig X) Z ≤ Matrix.trace T / alpha m := by
    intro Z hZ
    have hnn := weightedGram_self_nonneg T hT (W - Z)
    rw [weightedGram_sub_sub, ← weightedGram_comm_of_isSymm hTsym W Z] at hnn
    have hZZ : weightedGram T Z Z = Matrix.trace T / alpha m := by
      rw [weightedGram_self_eq_trace, hZ, trace_mul_simplexGram_of_centering T hTP,
        mul_comm, ← div_eq_mul_inv]
    have hWZ : weightedGram T W Z = configDot (centeredConfig X) Z := by
      rw [weightedGram_eq_configDot_recombine, hXP]
    rw [hWW, hZZ, hWZ] at hnn
    linarith
  have hscale : 2 * (Matrix.trace T / alpha m) = 2 / alpha m * Matrix.trace T := by
    rw [div_eq_mul_inv, mul_comm (Matrix.trace T), ← mul_assoc, ← div_eq_mul_inv]
  have hge : ∀ U' : OrthogonalMotion d,
      2 * (m : ℝ) - 2 / alpha m * Matrix.trace T ≤ procrustesEnergy X V U' := by
    intro U'
    have hZgram : gram (act U' V) = simplexGram m := by
      rw [gram_act, hVgram]
    have hZsum : ∑ i, act U' V i = 0 :=
      config_barycenter_of_simplexGram (act U' V) hm0 hZgram
    have hdotle : configDot X (act U' V) ≤ Matrix.trace T / alpha m := by
      rw [← configDot_centered_of_sum_zero X (act U' V) hZsum]
      exact hcross (act U' V) hZgram
    have hmul : 2 * configDot X (act U' V) ≤ 2 * (Matrix.trace T / alpha m) :=
      mul_le_mul_of_nonneg_left hdotle zero_le_two
    calc
      2 * (m : ℝ) - 2 / alpha m * Matrix.trace T
          = 2 * (m : ℝ) - 2 * (Matrix.trace T / alpha m) := by rw [← hscale]
      _ ≤ 2 * (m : ℝ) - 2 * configDot X (act U' V) := by linarith
      _ = procrustesEnergy X V U' := by
            rw [procrustesEnergy_unit X V hX hV U']
            rfl
  have hgramEq : gram V = gram W := by rw [hVgram, hgramW]
  obtain ⟨U, hU⟩ := exists_orthogonal_of_gram_eq V W hgramEq
  have hWsum : ∑ i, W i = 0 := config_barycenter_of_simplexGram W hm0 hgramW
  have hdotEq : configDot X W = Matrix.trace T / alpha m := by
    rw [← configDot_centered_of_sum_zero X W hWsum, hXP,
      ← weightedGram_eq_configDot_recombine, hWW]
  have hle : procrustesSq X V ≤ 2 * (m : ℝ) - 2 / alpha m * Matrix.trace T := by
    calc
      procrustesSq X V ≤ procrustesEnergy X V U := procrustesSq_le_energy X V U
      _ = 2 * (m : ℝ) - 2 * configDot X W := by
            rw [procrustesEnergy_unit X V hX hV U]
            simp [configDot, hU]
      _ = 2 * (m : ℝ) - 2 * (Matrix.trace T / alpha m) := by rw [hdotEq]
      _ = 2 * (m : ℝ) - 2 / alpha m * Matrix.trace T := by rw [hscale]
  have hgeInf : 2 * (m : ℝ) - 2 / alpha m * Matrix.trace T ≤ procrustesSq X V := by
    apply le_csInf (procrustesEnergy_range_nonempty X V)
    rintro r ⟨U', rfl⟩
    exact hge U'
  exact le_antisymm hle hgeInf

#print axioms gram_recombine
#print axioms recombine_mul
#print axioms weightedGram_eq_configDot_recombine
#print axioms weightedGram_self_eq_trace
#print axioms weightedGram_self_nonneg
#print axioms centering_mul_self
#print axioms configDot_centered_of_sum_zero
#print axioms procrustesEnergy_unit
#print axioms procrustesSq_sqrt

end SimplexFull.Geometry
