import SimplexFull.Shell
import SimplexFull.MatrixCFC
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.DotProduct
noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace SimplexFull.Geometry
lemma centering_idempotent {m : ℕ} (hm : m ≠ 0) :
    centering m * centering m = centering m := by
  conv_lhs => rhs; rw [centering]
  rw [mul_sub, mul_one, Matrix.mul_smul, centering_mul_onesMatrix hm, smul_zero, sub_zero]
lemma centering_posSemidef {m : ℕ} (hm : m ≠ 0) :
    (centering m).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (centering m)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, (centering_isSymm m).eq,
    centering_idempotent hm] using h
lemma compression_posSemidef {m : ℕ} {A : ShapeMatrix m} (hA : A.PosSemidef) :
    (compression A).PosSemidef := by
  simpa only [compression, Matrix.conjTranspose_eq_transpose_of_trivial,
    (centering_isSymm m).eq] using hA.conjTranspose_mul_mul_same (centering m)
def centeredGram {m d : ℕ} (X : Config m d) : ShapeMatrix m :=
  alpha m • compression (gram X)
def centeredRoot {m d : ℕ} (X : Config m d) : ShapeMatrix m :=
  CFC.sqrt (centeredGram X)
lemma alpha_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ alpha m := by
  unfold alpha
  exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hm)) (Nat.cast_nonneg m)
lemma centeredGram_posSemidef {m d : ℕ} (X : Config m d) (hm : 1 ≤ m) :
    (centeredGram X).PosSemidef :=
  (compression_posSemidef (gram_posSemidef X)).smul (alpha_nonneg hm)
#print axioms centeredGram_posSemidef
lemma centeredRoot_posSemidef {m d : ℕ} (X : Config m d) :
    (centeredRoot X).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (centeredGram X))
lemma centeredRoot_mul_self {m d : ℕ} (X : Config m d) (hm : 1 ≤ m) :
    centeredRoot X * centeredRoot X = centeredGram X :=
  CFC.sqrt_mul_sqrt_self _ (centeredGram_posSemidef X hm).nonneg
lemma centeredGram_centered {m d : ℕ} (X : Config m d) (hm : m ≠ 0) :
    centered (centeredGram X) := by
  obtain ⟨h1,h2⟩ := compression_centered hm (gram X)
  constructor
  · rw [centeredGram, Matrix.smul_mul, h1, smul_zero]
  · rw [centeredGram, Matrix.mul_smul, h2, smul_zero]
lemma centered_of_square_centered {m : ℕ} {T A : ShapeMatrix m}
    (hT : T.PosSemidef) (hsq : T*T=A) (hA : centered A) : centered T := by
  have hJ : (onesMatrix m).conjTranspose = onesMatrix m := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, (onesMatrix_isSymm m).eq]
  have hzero : (T * onesMatrix m).conjTranspose * (T * onesMatrix m) = 0 := by
    rw [Matrix.conjTranspose_mul, hJ, hT.isHermitian.eq]
    calc
      onesMatrix m * T * (T * onesMatrix m) = onesMatrix m * (T*T) * onesMatrix m := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hsq, Matrix.mul_assoc, hA.1, mul_zero]
  have hright : T * onesMatrix m = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  refine ⟨hright, ?_⟩
  have h := congrArg Matrix.conjTranspose hright
  simpa only [Matrix.conjTranspose_mul, hJ, hT.isHermitian.eq, Matrix.conjTranspose_zero] using h
lemma centeredRoot_centered {m d : ℕ} (X : Config m d) (hm : 1 ≤ m) :
    centered (centeredRoot X) :=
  centered_of_square_centered (centeredRoot_posSemidef X) (centeredRoot_mul_self X hm)
    (centeredGram_centered X (by omega))
#print axioms centeredRoot_centered
lemma centered_mul_centering {m : ℕ} {A : ShapeMatrix m} (hA : centered A) :
    centering m * A = A ∧ A * centering m = A := by
  constructor
  · rw [centering, sub_mul, one_mul, Matrix.smul_mul, hA.2, smul_zero, sub_zero]
  · rw [centering, mul_sub, mul_one, Matrix.mul_smul, hA.1, smul_zero, sub_zero]
lemma centeredGram_of_simplex {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) : centeredGram V = centering m := by
  rw [centeredGram, hV, compression, simplexGram, Matrix.mul_smul, Matrix.smul_mul,
    centering_idempotent (by omega), centering_idempotent (by omega), smul_smul,
    mul_inv_cancel₀ (alpha_ne_zero_of_gt_one m hm), one_smul]
lemma centeredRoot_of_simplex {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) : centeredRoot V = centering m := by
  rw [centeredRoot, centeredGram_of_simplex V hm hV]
  exact CFC.sqrt_unique (centering_idempotent (by omega)) (centering_posSemidef (by omega)).nonneg
lemma continuous_gram (m d : ℕ) : Continuous (@gram m d) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun X : Config m d => inner ℝ (X i) (X j))
  exact (continuous_apply i : Continuous (fun X : Config m d => X i)).inner
    (continuous_apply j : Continuous (fun X : Config m d => X j))
lemma continuous_centeredGram (m d : ℕ) : Continuous (@centeredGram m d) := by
  unfold centeredGram compression
  exact continuous_const.smul ((continuous_const.mul (continuous_gram m d)).mul continuous_const)
lemma continuous_centeredRoot {m d : ℕ} (hm : 1 ≤ m) : Continuous (@centeredRoot m d) := by
  exact CFC.continuousOn_sqrt.comp_continuous (continuous_centeredGram m d)
    (fun X => (centeredGram_posSemidef X hm).nonneg)
#print axioms continuous_centeredRoot
#print axioms centeredRoot_of_simplex
end SimplexFull.Geometry