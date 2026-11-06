import SimplexFull.GeometryBase
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Finite matrix coordinates for `input/ANALYTIC_PROOF.md`, §§11.3 and 11.6.

`alpha`, `onesMatrix`, and `centering` come from `GeometryBase`.
`J` is `onesMatrix` and `P` is `centering`. Compression is `A ↦ P A P`.
Uncompression is the diagonal correction
`Cᵢⱼ ↦ Cᵢⱼ - (Cᵢᵢ + Cⱼⱼ) / 2`, the matrix form of `A(C)` in §11.3.
`frobSq` is the squared Frobenius norm as a finite sum of squares.
-/

noncomputable section

namespace SimplexFull.Geometry

lemma centering_eq (m : ℕ) :
    centering m = (1 : Matrix (Fin m) (Fin m) ℝ) - (m : ℝ)⁻¹ • onesMatrix m :=
  rfl

/-- Diagonal entries vanish. -/
def zeroDiagonal {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ i, A i i = 0

/-- Row sums and column sums both vanish: `C * J = 0` and `J * C = 0`. -/
def centered {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  C * onesMatrix m = 0 ∧ onesMatrix m * C = 0

/-- Compression `A ↦ P A P`. -/
def compression {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  centering m * A * centering m

/-- Uncompression `Cᵢⱼ - (Cᵢᵢ + Cⱼⱼ) / 2`. -/
def uncompress {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => C i j - (C i i + C j j) / 2

/-- Sum of every entry. -/
def entrySum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j

/-- Half the sum of every entry. On a zero-diagonal matrix this is `∑_{i < j} Aᵢⱼ`. -/
def halfEntrySum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  entrySum A / 2

/-- Squared Frobenius norm `∑ᵢⱼ Aᵢⱼ²`, not an operator norm. -/
def frobSq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Sum of squares of the row sums, equal to `‖A 1‖²`. -/
def rowSumSq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, (∑ j, A i j) ^ 2

lemma zeroDiagonal_apply {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : zeroDiagonal A) (i : Fin m) : A i i = 0 := by
  unfold zeroDiagonal at hA
  exact hA i

lemma centered_mul_ones {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : centered C) :
    C * onesMatrix m = 0 := by
  unfold centered at hC
  exact hC.1

lemma centered_ones_mul {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : centered C) :
    onesMatrix m * C = 0 := by
  unfold centered at hC
  exact hC.2

lemma sum_const_fin {m : ℕ} (a : ℝ) : ∑ _i : Fin m, a = (m : ℝ) * a := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma sum_div_fin {m : ℕ} (f : Fin m → ℝ) (c : ℝ) :
    ∑ i, f i / c = (∑ i, f i) / c := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]

lemma sum_sub_sub_fin {m : ℕ} (a b c : Fin m → ℝ) :
    ∑ x, (a x - b x - c x) = ∑ x, a x - ∑ x, b x - ∑ x, c x := by
  simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

lemma sum_sub_add_fin {m : ℕ} (a b c : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, (a i j - b i j + c i j) =
      ∑ i, ∑ j, a i j - ∑ i, ∑ j, b i j + ∑ i, ∑ j, c i j := by
  simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

lemma trace_eq_sum_diag {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace C = ∑ i, C i i := by
  simp [Matrix.trace, Matrix.diag_apply]

lemma mul_ones_row {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i k : Fin m) :
    (A * onesMatrix m) i k = ∑ j, A i j := by
  simp [Matrix.mul_apply, onesMatrix, mul_one]

lemma mul_ones_col {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i k : Fin m) :
    (onesMatrix m * A) i k = ∑ j, A j k := by
  simp [Matrix.mul_apply, onesMatrix, one_mul]

lemma rowSum_zero_of_centered {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) (i : Fin m) : ∑ j, C i j = 0 := by
  cases m with
  | zero => exact i.elim0
  | succ _ =>
    rw [← mul_ones_row C i 0, centered_mul_ones hC, Matrix.zero_apply]

lemma colSum_zero_of_centered {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) (k : Fin m) : ∑ i, C i k = 0 := by
  cases m with
  | zero => exact k.elim0
  | succ _ =>
    rw [← mul_ones_col C 0 k, centered_ones_mul hC, Matrix.zero_apply]

theorem onesMatrix_mul_self (m : ℕ) :
    onesMatrix m * onesMatrix m = (m : ℝ) • onesMatrix m := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.smul_apply, onesMatrix, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]

theorem centering_mul_onesMatrix {m : ℕ} (hm : m ≠ 0) :
    centering m * onesMatrix m = 0 := by
  rw [centering_eq, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, onesMatrix_mul_self,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul, sub_self]

theorem onesMatrix_mul_centering {m : ℕ} (hm : m ≠ 0) :
    onesMatrix m * centering m = 0 := by
  rw [centering_eq, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, onesMatrix_mul_self,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul, sub_self]

theorem centering_onesMatrix_mul_eq_zero {m : ℕ} (hm : m ≠ 0) :
    centering m * onesMatrix m = 0 ∧ onesMatrix m * centering m = 0 :=
  ⟨centering_mul_onesMatrix hm, onesMatrix_mul_centering hm⟩

theorem onesMatrix_isSymm (m : ℕ) : (onesMatrix m).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [onesMatrix]

theorem centering_isSymm (m : ℕ) : (centering m).IsSymm := by
  rw [Matrix.IsSymm, centering_eq, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]
  rw [onesMatrix_isSymm m]

theorem uncompress_zeroDiagonal {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) :
    zeroDiagonal (uncompress C) := by
  unfold zeroDiagonal
  intro i
  rw [uncompress]
  ring

theorem uncompress_isSymm {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.IsSymm) :
    (uncompress C).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [uncompress]
  rw [hC.apply i j]
  ring

theorem compression_isSymm {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    (compression A).IsSymm := by
  rw [Matrix.IsSymm, compression, Matrix.transpose_mul, Matrix.transpose_mul,
    centering_isSymm m, hA, Matrix.mul_assoc]

theorem compression_centered {m : ℕ} (hm : m ≠ 0) (A : Matrix (Fin m) (Fin m) ℝ) :
    centered (compression A) := by
  unfold centered
  refine ⟨?_, ?_⟩
  · rw [compression, Matrix.mul_assoc, centering_mul_onesMatrix hm, Matrix.mul_zero]
  · rw [compression, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc (onesMatrix m) (centering m) A,
      onesMatrix_mul_centering hm, Matrix.zero_mul, Matrix.zero_mul]

lemma compression_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i k : Fin m) :
    compression A i k =
      A i k - (m : ℝ)⁻¹ * ∑ p, A p k - (m : ℝ)⁻¹ * ∑ j, A i j +
        (m : ℝ)⁻¹ * (m : ℝ)⁻¹ * ∑ j, ∑ p, A p j := by
  set c : ℝ := (m : ℝ)⁻¹
  have hcent : ∀ a b, centering m a b = (if a = b then (1 : ℝ) else 0) - c := by
    intro a b
    simp [centering, onesMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, c]
  have hPA : ∀ j, (centering m * A) i j = A i j - c * ∑ p, A p j := by
    intro j
    rw [Matrix.mul_apply]
    simp_rw [hcent, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hpick : ∑ p, (if i = p then (1 : ℝ) else 0) * A p j = A i j := by
      simp_rw [ite_mul, one_mul, zero_mul]
      exact Fintype.sum_ite_eq i fun p => A p j
    rw [hpick]
  rw [compression, Matrix.mul_apply]
  simp_rw [hPA, hcent]
  have hsplit : ∀ j,
      (A i j - c * ∑ p, A p j) * ((if j = k then (1 : ℝ) else 0) - c) =
        (A i j - c * ∑ p, A p j) * (if j = k then (1 : ℝ) else 0) -
          c * (A i j - c * ∑ p, A p j) := by
    intro j
    ring
  simp_rw [hsplit, Finset.sum_sub_distrib]
  have hpick : ∑ j, (A i j - c * ∑ p, A p j) * (if j = k then (1 : ℝ) else 0) =
      A i k - c * ∑ p, A p k := by
    simp_rw [mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' k fun j => A i j - c * ∑ p, A p j
  have hrest : ∑ j, c * (A i j - c * ∑ p, A p j) =
      c * ∑ j, A i j - c * c * ∑ j, ∑ p, A p j := by
    simp_rw [mul_sub, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hpick, hrest]
  ring

lemma entrySum_swap {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ∑ j, ∑ p, A p j = entrySum A := by
  unfold entrySum
  rw [Finset.sum_comm]

theorem uncompress_compression_of_symm_zeroDiagonal {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (hZ : zeroDiagonal A) :
    uncompress (compression A) = A := by
  ext i k
  have hcolrow : ∀ t, ∑ j, A j t = ∑ j, A t j := by
    intro t
    refine Finset.sum_congr rfl ?_
    intro j _
    exact (hA.apply j t).symm
  have hcomp (p q : Fin m) :
      compression A p q =
        A p q - (m : ℝ)⁻¹ * ∑ j, A q j - (m : ℝ)⁻¹ * ∑ j, A p j +
          (m : ℝ)⁻¹ * (m : ℝ)⁻¹ * entrySum A := by
    rw [compression_apply, hcolrow q, entrySum_swap]
  rw [uncompress, hcomp i k, hcomp i i, hcomp k k, zeroDiagonal_apply hZ i,
    zeroDiagonal_apply hZ k]
  ring

lemma rowSum_uncompress {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) (i : Fin m) :
    ∑ j, uncompress C i j = -((m : ℝ) / 2) * C i i - Matrix.trace C / 2 := by
  simp_rw [uncompress]
  have hsplit : ∀ j, C i j - (C i i + C j j) / 2 =
      C i j - C i i / 2 - C j j / 2 := by
    intro j
    ring
  simp_rw [hsplit, sum_sub_sub_fin]
  rw [rowSum_zero_of_centered hC i, sum_div_fin, sum_div_fin, sum_const_fin,
    ← trace_eq_sum_diag]
  ring

lemma colSum_uncompress {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) (k : Fin m) :
    ∑ i, uncompress C i k = -Matrix.trace C / 2 - ((m : ℝ) / 2) * C k k := by
  simp_rw [uncompress]
  have hsplit : ∀ i, C i k - (C i i + C k k) / 2 =
      C i k - C i i / 2 - C k k / 2 := by
    intro i
    ring
  simp_rw [hsplit, sum_sub_sub_fin]
  rw [colSum_zero_of_centered hC k, sum_div_fin, sum_div_fin, sum_const_fin,
    ← trace_eq_sum_diag]
  ring

theorem entrySum_uncompress_of_centered {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) :
    entrySum (uncompress C) = -(m : ℝ) * Matrix.trace C := by
  unfold entrySum
  simp_rw [rowSum_uncompress hC]
  have hsplit : ∑ i, (-((m : ℝ) / 2) * C i i - Matrix.trace C / 2) =
      -((m : ℝ) / 2) * ∑ i, C i i - (m : ℝ) * (Matrix.trace C / 2) := by
    simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
      sum_const_fin]
  rw [hsplit, ← trace_eq_sum_diag]
  ring

theorem halfEntrySum_uncompress_of_centered {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) :
    halfEntrySum (uncompress C) = -((m : ℝ) / 2) * Matrix.trace C := by
  rw [halfEntrySum, entrySum_uncompress_of_centered hC]
  ring

theorem compression_uncompress_of_centered {m : ℕ} (hm : m ≠ 0)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : centered C) :
    compression (uncompress C) = C := by
  ext i k
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [compression_apply, entrySum_swap, rowSum_uncompress hC i, colSum_uncompress hC k,
    entrySum_uncompress_of_centered hC, uncompress]
  field_simp [hmR]
  ring

lemma cross_sum_centered {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : centered C) :
    ∑ i, ∑ j, C i j * (C i i + C j j) = 0 := by
  have hmul : ∀ i j, C i j * (C i i + C j j) = C i i * C i j + C j j * C i j := by
    intro i j
    ring
  simp_rw [hmul, Finset.sum_add_distrib]
  have h1 : ∑ i, ∑ j, C i i * C i j = 0 := by
    simp_rw [← Finset.mul_sum, rowSum_zero_of_centered hC, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ i, ∑ j, C j j * C i j = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, colSum_zero_of_centered hC, mul_zero, Finset.sum_const_zero]
  simp [h1, h2]

lemma sum_sq_pair {m : ℕ} (u : Fin m → ℝ) :
    ∑ i, ∑ j, ((u i + u j) / 2) ^ 2 =
      ((m : ℝ) / 2) * ∑ i, u i ^ 2 + (∑ i, u i) ^ 2 / 2 := by
  have hsq : ∀ i j, ((u i + u j) / 2) ^ 2 =
      (u i ^ 2 + u j ^ 2 + 2 * u i * u j) / 4 := by
    intro i j
    ring
  simp_rw [hsq]
  have hdiv : ∑ i, ∑ j, (u i ^ 2 + u j ^ 2 + 2 * u i * u j) / 4 =
      (∑ i, ∑ j, (u i ^ 2 + u j ^ 2 + 2 * u i * u j)) / 4 := by
    simp_rw [sum_div_fin]
  rw [hdiv]
  have hsum : ∑ i, ∑ j, (u i ^ 2 + u j ^ 2 + 2 * u i * u j) =
      (∑ i, ∑ j : Fin m, (u i) ^ 2) + (∑ i : Fin m, ∑ j, (u j) ^ 2) +
        ∑ i, ∑ j, (2 * u i * u j) := by
    simp_rw [Finset.sum_add_distrib]
  let s : ℝ := ∑ i, (u i) ^ 2
  let t : ℝ := ∑ i, u i
  have hA : ∑ i, ∑ j : Fin m, (u i) ^ 2 = (m : ℝ) * s := by
    simp_rw [sum_const_fin]
    rw [← Finset.mul_sum]
  have hB : ∑ i : Fin m, ∑ j, (u j) ^ 2 = (m : ℝ) * s := by
    rw [sum_const_fin]
  have hC : ∑ i, ∑ j, 2 * u i * u j = 2 * t * t := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hsum, hA, hB, hC]
  ring

lemma frobSq_uncompress {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : centered C) :
    frobSq (uncompress C) =
      frobSq C + ((m : ℝ) / 2) * ∑ i, (C i i) ^ 2 + (Matrix.trace C) ^ 2 / 2 := by
  have hsq : ∀ i j, (uncompress C i j) ^ 2 =
      (C i j) ^ 2 - C i j * (C i i + C j j) + ((C i i + C j j) / 2) ^ 2 := by
    intro i j
    simp only [uncompress]
    ring
  unfold frobSq
  simp_rw [hsq]
  rw [sum_sub_add_fin, cross_sum_centered hC]
  rw [sum_sq_pair (fun i : Fin m => C i i)]
  rw [← frobSq, trace_eq_sum_diag]
  ring

lemma rowSumSq_uncompress_tracefree {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) (htr : Matrix.trace C = 0) :
    rowSumSq (uncompress C) = ((m : ℝ) ^ 2 / 4) * ∑ i, (C i i) ^ 2 := by
  unfold rowSumSq
  simp_rw [rowSum_uncompress hC, htr]
  have hterm : ∀ i, (-((m : ℝ) / 2) * C i i - (0 : ℝ) / 2) ^ 2 =
      ((m : ℝ) ^ 2 / 4) * (C i i) ^ 2 := by
    intro i
    ring
  simp_rw [hterm, ← Finset.mul_sum]

/-- Trace-free centered `C` and `B = uncompress C` satisfy
`‖C‖_F² = ‖B‖_F² - (2 / m) ∑ᵢ (rowᵢ B)²`. -/
theorem frobSq_centered_tracefree {m : ℕ} (hm : m ≠ 0) {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : centered C) (htr : Matrix.trace C = 0) :
    frobSq C =
      frobSq (uncompress C) - (2 / (m : ℝ)) * rowSumSq (uncompress C) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hB : frobSq (uncompress C) =
      frobSq C + ((m : ℝ) / 2) * ∑ i, (C i i) ^ 2 := by
    simpa [htr] using frobSq_uncompress hC
  have hcoeff : (2 / (m : ℝ)) * rowSumSq (uncompress C) =
      ((m : ℝ) / 2) * ∑ i, (C i i) ^ 2 := by
    rw [rowSumSq_uncompress_tracefree hC htr]
    field_simp [hmR]
    ring
  rw [hcoeff, hB]
  ring

#print axioms uncompress_zeroDiagonal
#print axioms uncompress_isSymm
#print axioms compression_isSymm
#print axioms onesMatrix_mul_self
#print axioms centering_mul_onesMatrix
#print axioms onesMatrix_mul_centering
#print axioms centering_onesMatrix_mul_eq_zero
#print axioms compression_centered
#print axioms uncompress_compression_of_symm_zeroDiagonal
#print axioms compression_uncompress_of_centered
#print axioms entrySum_uncompress_of_centered
#print axioms halfEntrySum_uncompress_of_centered
#print axioms frobSq_centered_tracefree

end SimplexFull.Geometry
