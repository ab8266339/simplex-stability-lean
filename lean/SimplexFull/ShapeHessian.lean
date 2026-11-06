import SimplexFull.Shell
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Actual `B0`/`B1` decomposition of an uncompressed shell matrix.

For `m ≥ 3` and `D` in `shellSpace m`, `B = uncompress D` is symmetric, zero on the
diagonal, and has entry sum zero. The row-sum vector `b` determines the standard
component `B1`, and `B0 = B - B1` is symmetric, zero-diagonal, and row-sum free.
These two components are orthogonal in the Frobenius pairing, and
`frobSq B = frobSq B0 + 2 * rowSumSq B / (m - 2)`.
The scalars `E0 = frobSq B0 / (4 * alpha m)` and `E1 = rowSumSq B / (m - 2)` are the
`hN`/`hR` data of `square_shell_hessian_identity`. The resulting quadratic `Q` is
positive when both algebraic gaps are positive. For `m = 3`, `B0` vanishes by a
`Fin 3` case split, so only the second gap is required.

The root Gaussian Hessian is not identified with `Q` here. A uniform coercivity
constant on the shell norm is not proved in this file.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace SimplexFull.Geometry

variable {m : ℕ}

/-- Row-sum vector `bᵢ = ∑ⱼ Bᵢⱼ`. -/
def rowSumVec (B : ShapeMatrix m) : Fin m → ℝ :=
  fun i => ∑ j, B i j

/-- Standard off-diagonal component `(bᵢ + bⱼ) / (m - 2)`. -/
def shapeComponent (b : Fin m → ℝ) : ShapeMatrix m :=
  fun i j => if i = j then 0 else (b i + b j) / ((m : ℝ) - 2)

/-- `B1`, built from the row sums of `B`. -/
def shapeB1 (B : ShapeMatrix m) : ShapeMatrix m :=
  shapeComponent (rowSumVec B)

/-- `B0 = B - B1`. -/
def shapeB0 (B : ShapeMatrix m) : ShapeMatrix m :=
  B - shapeB1 B

/-- Uncompressed shell matrix. -/
def shellB (D : shellSpace m) : ShapeMatrix m :=
  uncompress (D : ShapeMatrix m)

def shellN (D : shellSpace m) : ℝ :=
  frobSq (shellB D)

def shellR (D : shellSpace m) : ℝ :=
  rowSumSq (shellB D)

/-- Pure shape energy `‖B0‖_F² / (4 α)`. -/
def shellE0 (D : shellSpace m) : ℝ :=
  frobSq (shapeB0 (shellB D)) / (4 * alpha m)

/-- Row-sum energy `R / (m - 2)`. -/
def shellE1 (D : shellSpace m) : ℝ :=
  shellR D / ((m : ℝ) - 2)

/-- Quadratic form instantiated by `square_shell_hessian_identity`. -/
def shellQuadratic (m : ℕ) (A B C : ℝ) (D : shellSpace m) : ℝ :=
  - (m : ℝ) * C / 2 * (shellN D - 2 * shellR D / (m : ℝ)) + A * shellN D
    - 2 * (C - B) * shellR D

lemma sub_two_ne (hm : 3 ≤ m) : (m : ℝ) - 2 ≠ 0 := by
  have hlt : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  exact sub_ne_zero.mpr (ne_of_gt hlt)

lemma sub_two_pos (hm : 3 ≤ m) : 0 < (m : ℝ) - 2 := by
  have hlt : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  exact sub_pos.mpr hlt

lemma alpha_pos (hm : 3 ≤ m) : 0 < alpha m := by
  unfold alpha
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h1 : 0 < (m : ℝ) - 1 := by
    have : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    linarith
  exact div_pos h1 hm0

lemma sum_rowSumVec (B : ShapeMatrix m) : ∑ i, rowSumVec B i = entrySum B := by
  simp [rowSumVec, entrySum]

lemma sum_offDiag (i : Fin m) (f : Fin m → ℝ) :
    ∑ j, (if i = j then (0 : ℝ) else f j) = (∑ j, f j) - f i := by
  have hpt : ∀ j, (if i = j then (0 : ℝ) else f j) =
      f j - (if i = j then f j else 0) := by
    intro j
    split_ifs <;> ring
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Fintype.sum_ite_eq]

lemma frobSq_nonneg (A : ShapeMatrix m) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma rowSumSq_nonneg (A : ShapeMatrix m) : 0 ≤ rowSumSq A := by
  unfold rowSumSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma frobSq_eq_zero {A : ShapeMatrix m} (h : frobSq A = 0) : A = 0 := by
  ext i j
  unfold frobSq at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, (A i j) ^ 2 :=
    fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hi : ∑ j, (A i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
  have hj : (A i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 hi j (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp hj

lemma rowSum_eq_zero_of_rowSumSq {A : ShapeMatrix m} (h : rowSumSq A = 0) (i : Fin m) :
    ∑ j, A i j = 0 := by
  unfold rowSumSq at h
  have hi : (∑ j, A i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

lemma shapeComponent_zeroDiagonal (b : Fin m → ℝ) : zeroDiagonal (shapeComponent b) := by
  intro i
  simp [shapeComponent]

lemma shapeComponent_isSymm (b : Fin m → ℝ) : (shapeComponent b).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [shapeComponent]
  · simp [shapeComponent, if_neg hij, if_neg (Ne.symm hij)]
    ring

lemma shapeB1_zeroDiagonal (B : ShapeMatrix m) : zeroDiagonal (shapeB1 B) :=
  shapeComponent_zeroDiagonal _

lemma shapeB1_isSymm (B : ShapeMatrix m) : (shapeB1 B).IsSymm :=
  shapeComponent_isSymm _

theorem shapeB0_zeroDiagonal {B : ShapeMatrix m} (hB : zeroDiagonal B) :
    zeroDiagonal (shapeB0 B) := by
  intro i
  simp [shapeB0, Matrix.sub_apply, zeroDiagonal_apply hB i,
    zeroDiagonal_apply (shapeB1_zeroDiagonal B) i]

theorem shapeB0_isSymm {B : ShapeMatrix m} (hB : B.IsSymm) : (shapeB0 B).IsSymm := by
  rw [Matrix.IsSymm, shapeB0, Matrix.transpose_sub, hB, shapeB1_isSymm B]

theorem rowSum_shapeComponent (hm : 3 ≤ m) {b : Fin m → ℝ} (hb : ∑ i, b i = 0)
    (i : Fin m) : ∑ j, shapeComponent b i j = b i := by
  have hd : (m : ℝ) - 2 ≠ 0 := sub_two_ne hm
  have hpt : ∀ j, shapeComponent b i j =
      (if i = j then (0 : ℝ) else b i + b j) / ((m : ℝ) - 2) := by
    intro j
    by_cases hij : i = j
    · simp [shapeComponent, hij]
    · simp [shapeComponent, hij]
  simp_rw [hpt, sum_div_fin]
  have hsplit : ∀ j, (if i = j then (0 : ℝ) else b i + b j) =
      (if i = j then 0 else b i) + (if i = j then 0 else b j) := by
    intro j
    split_ifs <;> ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hconst : ∑ j, (if i = j then (0 : ℝ) else b i) = ((m : ℝ) - 1) * b i := by
    rw [sum_offDiag, sum_const_fin]
    ring
  have hrest : ∑ j, (if i = j then (0 : ℝ) else b j) = - b i := by
    rw [sum_offDiag, hb]
    ring
  rw [hconst, hrest]
  field_simp [hd]
  ring

theorem rowSum_shapeB0 (hm : 3 ≤ m) {B : ShapeMatrix m} (hE : entrySum B = 0)
    (i : Fin m) : ∑ j, shapeB0 B i j = 0 := by
  have hb : ∑ i, rowSumVec B i = 0 := by rw [sum_rowSumVec, hE]
  simp only [shapeB0, Matrix.sub_apply, Finset.sum_sub_distrib, shapeB1]
  rw [rowSum_shapeComponent hm hb i]
  simp [rowSumVec]

theorem frobSq_shapeB1 (hm : 3 ≤ m) {B : ShapeMatrix m} (hE : entrySum B = 0) :
    frobSq (shapeB1 B) = 2 * rowSumSq B / ((m : ℝ) - 2) := by
  let b : Fin m → ℝ := rowSumVec B
  have hb : ∑ i, b i = 0 := by simp [b, sum_rowSumVec, hE]
  have hd : (m : ℝ) - 2 ≠ 0 := sub_two_ne hm
  have hsq : ∀ i j, (shapeComponent b i j) ^ 2 =
      (if i = j then (0 : ℝ) else (b i + b j) ^ 2) / ((m : ℝ) - 2) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · simp [shapeComponent, hij]
    · simp [shapeComponent, hij]
      rw [div_pow]
  unfold frobSq
  simp_rw [show shapeB1 B = shapeComponent b from rfl, hsq, sum_div_fin]
  have hinner : ∑ i, ∑ j, (if i = j then (0 : ℝ) else (b i + b j) ^ 2) =
      2 * ((m : ℝ) - 2) * ∑ i, (b i) ^ 2 := by
    have hexp : ∀ i j, (if i = j then (0 : ℝ) else (b i + b j) ^ 2) =
        (if i = j then 0 else (b i) ^ 2) + (if i = j then 0 else (b j) ^ 2) +
          (if i = j then 0 else 2 * b i * b j) := by
      intro i j
      split_ifs <;> ring
    simp_rw [hexp, Finset.sum_add_distrib]
    have hA : ∑ i, ∑ j, (if i = j then (0 : ℝ) else (b i) ^ 2) =
        ((m : ℝ) - 1) * ∑ i, (b i) ^ 2 := by
      have hrow : ∀ i, ∑ j, (if i = j then (0 : ℝ) else (b i) ^ 2) =
          ((m : ℝ) - 1) * (b i) ^ 2 := by
        intro i
        rw [sum_offDiag, sum_const_fin]
        ring
      simp_rw [hrow, ← Finset.mul_sum]
    have hB : ∑ i, ∑ j, (if i = j then (0 : ℝ) else (b j) ^ 2) =
        ((m : ℝ) - 1) * ∑ i, (b i) ^ 2 := by
      have hrow : ∀ i, ∑ j, (if i = j then (0 : ℝ) else (b j) ^ 2) =
          ∑ k, (b k) ^ 2 - (b i) ^ 2 := by
        intro i
        rw [sum_offDiag]
      simp_rw [hrow, Finset.sum_sub_distrib, sum_const_fin]
      ring
    have hC : ∑ i, ∑ j, (if i = j then (0 : ℝ) else 2 * b i * b j) =
        -2 * ∑ i, (b i) ^ 2 := by
      have hfac : ∀ i j, (if i = j then (0 : ℝ) else 2 * b i * b j) =
          2 * b i * (if i = j then 0 else b j) := by
        intro i j
        split_ifs <;> ring
      simp_rw [hfac, ← Finset.mul_sum]
      have hoff : ∀ i, ∑ j, (if i = j then (0 : ℝ) else b j) = - b i := by
        intro i
        rw [sum_offDiag, hb]
        ring
      simp_rw [hoff]
      have hsqi : ∀ i, 2 * b i * - b i = -2 * (b i) ^ 2 := by
        intro i
        ring
      simp_rw [hsqi, ← Finset.mul_sum]
    rw [hA, hB, hC]
    ring
  rw [hinner]
  have hS : ∑ i, (b i) ^ 2 = rowSumSq B := by simp [b, rowSumVec, rowSumSq]
  rw [hS]
  field_simp [hd]

theorem frobInner_shapeB0_shapeB1 (hm : 3 ≤ m) {B : ShapeMatrix m} (hS : B.IsSymm)
    (hZ : zeroDiagonal B) (hE : entrySum B = 0) :
    ∑ i, ∑ j, shapeB0 B i j * shapeB1 B i j = 0 := by
  have hd : (m : ℝ) - 2 ≠ 0 := sub_two_ne hm
  have hZ0 : zeroDiagonal (shapeB0 B) := shapeB0_zeroDiagonal hZ
  have hS0 : (shapeB0 B).IsSymm := shapeB0_isSymm hS
  have hrow : ∀ i, ∑ j, shapeB0 B i j = 0 := fun i => rowSum_shapeB0 hm hE i
  have hpt : ∀ i j, shapeB0 B i j * shapeB1 B i j =
      shapeB0 B i j * (rowSumVec B i + rowSumVec B j) / ((m : ℝ) - 2) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [shapeB1, shapeComponent, zeroDiagonal_apply hZ0 i]
    · simp [shapeB1, shapeComponent, hij]
      ring
  simp_rw [hpt, sum_div_fin]
  have hnum : ∑ i, ∑ j, shapeB0 B i j * (rowSumVec B i + rowSumVec B j) = 0 := by
    have hsplit : ∀ i j, shapeB0 B i j * (rowSumVec B i + rowSumVec B j) =
        rowSumVec B i * shapeB0 B i j + rowSumVec B j * shapeB0 B i j := by
      intro i j
      ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 : ∑ i, ∑ j, rowSumVec B i * shapeB0 B i j = 0 := by
      simp_rw [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
    have h2 : ∑ i, ∑ j, rowSumVec B j * shapeB0 B i j = 0 := by
      rw [Finset.sum_comm]
      have hcol : ∀ j, ∑ i, shapeB0 B i j = 0 := by
        intro j
        have hswap : ∑ i, shapeB0 B i j = ∑ i, shapeB0 B j i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hS0.apply j i
        rw [hswap, hrow j]
      simp_rw [← Finset.mul_sum, hcol, mul_zero, Finset.sum_const_zero]
    simp [h1, h2]
  rw [hnum, zero_div]

lemma frobSq_add (X Y : ShapeMatrix m) :
    frobSq (X + Y) = frobSq X + frobSq Y + 2 * ∑ i, ∑ j, X i j * Y i j := by
  unfold frobSq
  have hsq : ∀ i j, ((X + Y) i j) ^ 2 =
      (X i j) ^ 2 + (Y i j) ^ 2 + 2 * X i j * Y i j := by
    intro i j
    rw [show (X + Y) i j = X i j + Y i j by rfl]
    ring
  simp_rw [hsq]
  have hsplit : ∑ i, ∑ j, ((X i j) ^ 2 + (Y i j) ^ 2 + 2 * X i j * Y i j) =
      ∑ i, ∑ j, (X i j) ^ 2 + ∑ i, ∑ j, (Y i j) ^ 2 +
        ∑ i, ∑ j, 2 * X i j * Y i j := by
    simp_rw [Finset.sum_add_distrib]
  rw [hsplit]
  have htwo : ∑ i, ∑ j, 2 * X i j * Y i j = 2 * ∑ i, ∑ j, X i j * Y i j := by
    have hmul : ∀ i j, 2 * X i j * Y i j = 2 * (X i j * Y i j) := by
      intro i j
      ring
    simp_rw [hmul, ← Finset.mul_sum]
  rw [htwo]

/-- `‖B‖_F² = ‖B0‖_F² + 2 R / (m - 2)` for a symmetric zero-diagonal matrix of entry sum zero. -/
theorem frobSq_shape_decomposition (hm : 3 ≤ m) {B : ShapeMatrix m} (hS : B.IsSymm)
    (hZ : zeroDiagonal B) (hE : entrySum B = 0) :
    frobSq B = frobSq (shapeB0 B) + 2 * rowSumSq B / ((m : ℝ) - 2) := by
  have hEq : frobSq B = frobSq (shapeB0 B + shapeB1 B) := by
    congr 1
    simp only [shapeB0]
    exact (sub_add_cancel B (shapeB1 B)).symm
  calc
    frobSq B = frobSq (shapeB0 B + shapeB1 B) := hEq
    _ = frobSq (shapeB0 B) + frobSq (shapeB1 B) +
          2 * ∑ i, ∑ j, shapeB0 B i j * shapeB1 B i j := frobSq_add _ _
    _ = frobSq (shapeB0 B) + frobSq (shapeB1 B) := by
      rw [frobInner_shapeB0_shapeB1 hm hS hZ hE, mul_zero, add_zero]
    _ = frobSq (shapeB0 B) + 2 * rowSumSq B / ((m : ℝ) - 2) := by
      rw [frobSq_shapeB1 hm hE]

lemma shell_facts (H : shellSpace m) :
    (H : ShapeMatrix m).transpose = (H : ShapeMatrix m) ∧
      centering m * (H : ShapeMatrix m) = (H : ShapeMatrix m) ∧
      (H : ShapeMatrix m) * centering m = (H : ShapeMatrix m) ∧
      Matrix.trace (H : ShapeMatrix m) = 0 := by
  have hmem : (H : ShapeMatrix m) ∈ shellSpace m := H.property
  delta shellSpace at hmem
  simpa [Set.mem_setOf] using hmem

lemma shell_centered (hm : m ≠ 0) {D : ShapeMatrix m}
    (hPD : centering m * D = D) (hDP : D * centering m = D) : centered D := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  refine ⟨?_, ?_⟩
  · have hDP' : D * (1 - (m : ℝ)⁻¹ • onesMatrix m) = D := by
      simpa [centering] using hDP
    rw [mul_sub, mul_one, Matrix.mul_smul] at hDP'
    have hzero : (m : ℝ)⁻¹ • (D * onesMatrix m) = 0 := sub_eq_self.mp hDP'
    have hmul := congrArg (fun M : ShapeMatrix m => (m : ℝ) • M) hzero
    simpa [smul_smul, mul_inv_cancel₀ hmR] using hmul
  · have hPD' : (1 - (m : ℝ)⁻¹ • onesMatrix m) * D = D := by
      simpa [centering] using hPD
    rw [sub_mul, one_mul, Matrix.smul_mul] at hPD'
    have hzero : (m : ℝ)⁻¹ • (onesMatrix m * D) = 0 := sub_eq_self.mp hPD'
    have hmul := congrArg (fun M : ShapeMatrix m => (m : ℝ) • M) hzero
    simpa [smul_smul, mul_inv_cancel₀ hmR] using hmul

theorem shellB_isSymm (D : shellSpace m) : (shellB D).IsSymm := by
  have hS : (D : ShapeMatrix m).IsSymm := (shell_facts D).1
  simpa [shellB] using uncompress_isSymm hS

theorem shellB_zeroDiagonal (D : shellSpace m) : zeroDiagonal (shellB D) := by
  simpa [shellB] using uncompress_zeroDiagonal (D : ShapeMatrix m)

theorem entrySum_shellB (hm : m ≠ 0) (D : shellSpace m) : entrySum (shellB D) = 0 := by
  obtain ⟨_, hPD, hDP, htr⟩ := shell_facts D
  rw [shellB, entrySum_uncompress_of_centered (shell_centered hm hPD hDP), htr]
  ring

theorem shellN_decomposition (hm : 3 ≤ m) (D : shellSpace m) :
    shellN D = frobSq (shapeB0 (shellB D)) + 2 * shellR D / ((m : ℝ) - 2) := by
  unfold shellN shellR
  exact frobSq_shape_decomposition hm (shellB_isSymm D) (shellB_zeroDiagonal D)
    (entrySum_shellB (by omega) D)

theorem shell_hN (hm : 3 ≤ m) (D : shellSpace m) :
    shellN D = 4 * (((m : ℝ) - 1) / (m : ℝ)) * shellE0 D + 2 * shellE1 D := by
  have hd : (m : ℝ) - 2 ≠ 0 := sub_two_ne hm
  have hden : 4 * alpha m ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (alpha_pos hm))
  have hα : alpha m = ((m : ℝ) - 1) / (m : ℝ) := rfl
  unfold shellE0 shellE1
  rw [shellN_decomposition hm D, hα]
  have hden' : 4 * (((m : ℝ) - 1) / (m : ℝ)) ≠ 0 := by
    rw [← hα]
    exact hden
  rw [mul_div_cancel₀ (frobSq (shapeB0 (shellB D))) hden']
  field_simp [hd]

theorem shell_hR (hm : 3 ≤ m) (D : shellSpace m) :
    shellR D = ((m : ℝ) - 2) * shellE1 D := by
  unfold shellE1
  exact (mul_div_cancel₀ (shellR D) (sub_two_ne hm)).symm

theorem shellE0_nonneg (hm : 3 ≤ m) (D : shellSpace m) : 0 ≤ shellE0 D := by
  unfold shellE0
  exact div_nonneg (frobSq_nonneg _) (mul_nonneg (by norm_num) (le_of_lt (alpha_pos hm)))

theorem shellE1_nonneg (hm : 3 ≤ m) (D : shellSpace m) : 0 ≤ shellE1 D := by
  unfold shellE1 shellR
  exact div_nonneg (rowSumSq_nonneg _) (le_of_lt (sub_two_pos hm))

lemma shapeB1_eq_zero_of_rowSumSq {B : ShapeMatrix m} (h : rowSumSq B = 0) :
    shapeB1 B = 0 := by
  ext i j
  have hi : rowSumVec B i = 0 := by simpa [rowSumVec] using rowSum_eq_zero_of_rowSumSq h i
  have hj : rowSumVec B j = 0 := by simpa [rowSumVec] using rowSum_eq_zero_of_rowSumSq h j
  by_cases hij : i = j
  · simp [shapeB1, shapeComponent, hij]
  · simp [shapeB1, shapeComponent, hij, hi, hj, zero_div]

theorem shellE_sum_pos (hm : 3 ≤ m) {D : shellSpace m} (hD : D ≠ 0) :
    0 < shellE0 D + shellE1 D := by
  have hE0nn := shellE0_nonneg hm D
  have hE1nn := shellE1_nonneg hm D
  by_contra hle
  have hle' : shellE0 D + shellE1 D ≤ 0 := le_of_not_gt hle
  have hz0 : shellE0 D = 0 := by linarith
  have hz1 : shellE1 D = 0 := by linarith
  have hden0 : 4 * alpha m ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (alpha_pos hm))
  have hf0 : frobSq (shapeB0 (shellB D)) = 0 := by
    have h := hz0
    unfold shellE0 at h
    rw [div_eq_iff hden0] at h
    simpa using h
  have hR0 : rowSumSq (shellB D) = 0 := by
    have h := hz1
    unfold shellE1 shellR at h
    rw [div_eq_iff (sub_two_ne hm)] at h
    simpa using h
  have hB0 : shapeB0 (shellB D) = 0 := frobSq_eq_zero hf0
  have hB1 : shapeB1 (shellB D) = 0 := shapeB1_eq_zero_of_rowSumSq hR0
  have hB : shellB D = 0 := by
    have hsum : shellB D = shapeB0 (shellB D) + shapeB1 (shellB D) := by
      simpa only [shapeB0] using (sub_add_cancel (shellB D) (shapeB1 (shellB D))).symm
    rw [hsum, hB0, hB1, zero_add]
  obtain ⟨_, hPD, hDP, _⟩ := shell_facts D
  have hcomp := compression_uncompress_of_centered (by omega : m ≠ 0)
    (shell_centered (by omega) hPD hDP)
  rw [show uncompress (D : ShapeMatrix m) = shellB D from rfl, hB] at hcomp
  have hzero : (D : ShapeMatrix m) = 0 := by
    simpa [compression] using hcomp.symm
  exact hD (Subtype.ext hzero)

theorem shellQuadratic_identity (hm : 3 ≤ m) (A B C : ℝ) (D : shellSpace m) :
    shellQuadratic m A B C D =
      4 * (((((m : ℝ) - 1) / (m : ℝ)) * A - ((m : ℝ) - 1) * C / 2) * shellE0 D +
        ((A + ((m : ℝ) - 2) * B) / 2 - ((m : ℝ) - 1) * C / 2) * shellE1 D) := by
  simpa [shellQuadratic] using
    square_shell_hessian_identity (m : ℝ) A B C (shellN D) (shellR D) (shellE0 D) (shellE1 D)
      (by exact_mod_cast hm) (shell_hN hm D) (shell_hR hm D)

theorem shellQuadratic_pos (hm : 3 ≤ m) (A B C : ℝ) (D : shellSpace m) (hD : D ≠ 0)
    (hg0 : 0 < ((m : ℝ) - 1) / (m : ℝ) * A - ((m : ℝ) - 1) * C / 2)
    (hg1 : 0 < (A + ((m : ℝ) - 2) * B) / 2 - ((m : ℝ) - 1) * C / 2) :
    0 < shellQuadratic m A B C D := by
  simpa [shellQuadratic] using
    square_shell_hessian_pos (m : ℝ) A B C (shellN D) (shellR D) (shellE0 D) (shellE1 D)
      (by exact_mod_cast hm) (shell_hN hm D) (shell_hR hm D)
      (shellE0_nonneg hm D) (shellE1_nonneg hm D) (shellE_sum_pos hm hD) hg0 hg1

/-- On `Fin 3`, a symmetric zero-diagonal matrix of entry sum zero equals its `B1` component. -/
theorem shapeB0_eq_zero_m3 {B : ShapeMatrix 3} (hS : B.IsSymm) (hZ : zeroDiagonal B)
    (hE : entrySum B = 0) : shapeB0 B = 0 := by
  have h00 : B 0 0 = 0 := zeroDiagonal_apply hZ 0
  have h11 : B 1 1 = 0 := zeroDiagonal_apply hZ 1
  have h22 : B 2 2 = 0 := zeroDiagonal_apply hZ 2
  have h10 : B 1 0 = B 0 1 := hS.apply 0 1
  have h20 : B 2 0 = B 0 2 := hS.apply 0 2
  have h21 : B 2 1 = B 1 2 := hS.apply 1 2
  have hpair : B 0 1 + B 0 2 + B 1 2 = 0 := by
    unfold entrySum at hE
    simp only [Fin.sum_univ_three] at hE
    linarith
  have n02 : (0 : Fin 3) ≠ 2 := by decide
  have n12 : (1 : Fin 3) ≠ 2 := by decide
  have n20 : (2 : Fin 3) ≠ 0 := Ne.symm n02
  have n21 : (2 : Fin 3) ≠ 1 := Ne.symm n12
  have hf2 (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := by
    apply Fin.ext
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hf2, n02, n12, n20, n21, shapeB0, shapeB1, shapeComponent, rowSumVec, Fin.sum_univ_three,
      h00, h11, h22, h10, h20, h21] <;> linarith [hpair]
theorem shellE0_eq_zero_m3 (D : shellSpace 3) : shellE0 D = 0 := by
  have hB0 : shapeB0 (shellB D) = 0 :=
    shapeB0_eq_zero_m3 (shellB_isSymm D) (shellB_zeroDiagonal D)
      (entrySum_shellB (by decide) D)
  unfold shellE0
  rw [hB0]
  simp [frobSq, Matrix.zero_apply]

theorem shellQuadratic_pos_m3 (A B C : ℝ) (D : shellSpace 3) (hD : D ≠ 0)
    (hg1 : 0 < (A + ((3 : ℝ) - 2) * B) / 2 - ((3 : ℝ) - 1) * C / 2) :
    0 < shellQuadratic 3 A B C D := by
  have hm : 3 ≤ (3 : ℕ) := le_rfl
  have hE0 : shellE0 D = 0 := shellE0_eq_zero_m3 D
  have hE1 : 0 < shellE1 D := by
    have hsum := shellE_sum_pos hm hD
    rwa [hE0, zero_add] at hsum
  have hId := shellQuadratic_identity hm A B C D
  rw [hE0] at hId
  have hQ : shellQuadratic 3 A B C D =
      4 * ((((A + ((3 : ℝ) - 2) * B) / 2 - ((3 : ℝ) - 1) * C / 2) * shellE1 D)) := by
    rw [hId]
    ring
  rw [hQ]
  exact mul_pos (by norm_num) (mul_pos hg1 hE1)

#print axioms shapeB0_zeroDiagonal
#print axioms shapeB0_isSymm
#print axioms rowSum_shapeB0
#print axioms frobSq_shapeB1
#print axioms frobInner_shapeB0_shapeB1
#print axioms frobSq_shape_decomposition
#print axioms shellB_isSymm
#print axioms shellB_zeroDiagonal
#print axioms entrySum_shellB
#print axioms shellN_decomposition
#print axioms shell_hN
#print axioms shell_hR
#print axioms shellE0_nonneg
#print axioms shellE1_nonneg
#print axioms shellE_sum_pos
#print axioms shellQuadratic_identity
#print axioms shellQuadratic_pos
#print axioms shapeB0_eq_zero_m3
#print axioms shellE0_eq_zero_m3
#print axioms shellQuadratic_pos_m3

end SimplexFull.Geometry
