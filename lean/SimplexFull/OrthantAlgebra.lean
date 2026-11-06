import SimplexFull.GaussianDensity
import SimplexFull.GramCoordinates
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite matrix moment combinatorics

Quadratic-form moments for a symmetric zero-diagonal real matrix, as finite sums against an
explicit 2- and 4-index table. Coordinates are treated as i.i.d. with mean `a` and variance `s`.
Because `Aᵢᵢ = 0`, every monomial `Aᵢⱼ Aₖₗ xᵢ xⱼ xₖ xₗ` that survives has each index of
multiplicity at most 2, so the table uses only `a` and `s`.

`quadDensityCoeff` is the second-order density ratio
`trace(A*A)/4 + (xᵀ A x)²/8 - xᵀ (A*A) x/2`.
Substituting the truncated-Gaussian parameters `a = -q`, `s = σ` with `1 - σ = q*h` is pure
algebra. Orthant integrals are not proved in this file.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace SimplexFull.Covariance

open SimplexFull.Geometry

variable {m : ℕ}

/-- Kronecker delta on coordinates, as a real number. -/
def kronecker (i j : Fin m) : ℝ :=
  if i = j then 1 else 0

/-- Number of times `t` occurs among four indices. -/
def indexMult (t i j k l : Fin m) : ℕ :=
  (if t = i then 1 else 0) + (if t = j then 1 else 0) +
    (if t = k then 1 else 0) + (if t = l then 1 else 0)

/-- Two-index moment `E[Xᵢ Xⱼ]` for i.i.d. coordinates of mean `a` and variance `s`. -/
def moment2 (a s : ℝ) (i j : Fin m) : ℝ :=
  if i = j then a ^ 2 + s else a ^ 2

/-- Four-index moment table.
The value is `a⁴` plus the six second-moment pairings plus the three Wick pairings.
On every tuple in which each index has multiplicity at most 2, this is the i.i.d. product
moment determined by mean `a` and variance `s`. Multiplicity 3 and 4 are not claimed to be
moments of a non-Gaussian law; a zero diagonal removes them from the sums below. -/
def moment4 (a s : ℝ) (i j k l : Fin m) : ℝ :=
  a ^ 4 +
    a ^ 2 * s * (kronecker i j + kronecker i k + kronecker i l +
      kronecker j k + kronecker j l + kronecker k l) +
    s ^ 2 * (kronecker i j * kronecker k l + kronecker i k * kronecker j l +
      kronecker i l * kronecker j k)

/-- Row sum `(A 1)ᵢ`. -/
def rowSum (A : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j

/-- Contraction of `A` against the two-index table: formal `E[xᵀ A x]`. -/
def quadMoment (a s : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * moment2 a s i j

/-- Contraction of `Aᵢⱼ Aₖₗ` against the four-index table: formal `E[(xᵀ A x)²]`. -/
def quadSquareMoment (a s : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * moment4 a s i j k l

/-- Second-order density-ratio coefficient `trace(A*A)/4 + (quad A x)²/8 - quad (A*A) x/2`. -/
def quadDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Matrix.trace (A * A) / 4 + (quad A x) ^ 2 / 8 - quad (A * A) x / 2

/-- The same coefficient with coordinate monomials replaced by the moment table. -/
def quadDensityCoeffMoment (a s : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  Matrix.trace (A * A) / 4 + quadSquareMoment a s A / 8 - quadMoment a s (A * A) / 2

/-- Linear term `E[quad A]/2` plus the quadratic density coefficient, in the moment table. -/
def secondOrderMoment (a s : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  quadMoment a s A / 2 + quadDensityCoeffMoment a s A

lemma sum_eq_of_ite (i : Fin m) (f : Fin m → ℝ) :
    ∑ j, (if i = j then f j else 0) = f i := by
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_univ]

lemma sum_kronecker (i : Fin m) (f : Fin m → ℝ) :
    ∑ j, f j * kronecker i j = f i := by
  unfold kronecker
  simp_rw [mul_ite, mul_one, mul_zero]
  exact sum_eq_of_ite i f

lemma moment2_eq (a s : ℝ) (i j : Fin m) :
    moment2 a s i j = a ^ 2 + if i = j then s else 0 := by
  unfold moment2
  by_cases h : i = j
  · simp [h]
  · simp [h]

lemma rowSumSq_eq (A : Matrix (Fin m) (Fin m) ℝ) :
    rowSumSq A = ∑ i, (rowSum A i) ^ 2 := by
  unfold rowSumSq
  rfl

lemma symm_apply_comm {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (i j : Fin m) :
    A i j = A j i :=
  (hA.apply j i)

lemma ne_of_entry_ne_zero {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A)
    {i j : Fin m} (h : A i j ≠ 0) : i ≠ j := by
  intro hij
  apply h
  rw [hij]
  exact zeroDiagonal_apply hZ j

lemma pairIndicator_le_one {a b : Fin m} (h : a ≠ b) (t : Fin m) :
    (if t = a then 1 else 0) + (if t = b then 1 else 0) ≤ 1 := by
  by_cases ha : t = a
  · subst ha
    simp only [if_pos rfl, if_neg h]
    norm_num
  · by_cases hb : t = b
    · simp only [if_neg ha, if_pos hb]
      norm_num
    · simp only [if_neg ha, if_neg hb]
      norm_num

lemma indexMult_le_two_of_ne {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) (t : Fin m) :
    indexMult t i j k l ≤ 2 := by
  have h1 : (if t = i then 1 else 0) + (if t = j then 1 else 0) ≤ 1 :=
    pairIndicator_le_one hij t
  have h2 : (if t = k then 1 else 0) + (if t = l then 1 else 0) ≤ 1 :=
    pairIndicator_le_one hkl t
  calc
    indexMult t i j k l
        = ((if t = i then 1 else 0) + (if t = j then 1 else 0)) +
            ((if t = k then 1 else 0) + (if t = l then 1 else 0)) := by
          unfold indexMult
          exact Nat.add_assoc
            ((if t = i then 1 else 0) + (if t = j then 1 else 0))
            (if t = k then 1 else 0) (if t = l then 1 else 0)
    _ ≤ 1 + 1 := Nat.add_le_add h1 h2
    _ = 2 := by norm_num

/-- A zero diagonal kills every summand in which some index has multiplicity ≥ 3. -/
lemma indexMult_le_two_of_coeff {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A)
    {i j k l : Fin m} (hij : A i j ≠ 0) (hkl : A k l ≠ 0) (t : Fin m) :
    indexMult t i j k l ≤ 2 :=
  indexMult_le_two_of_ne (ne_of_entry_ne_zero hZ hij) (ne_of_entry_ne_zero hZ hkl) t

lemma moment4_distinct (a s : ℝ) {i j k l : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    moment4 a s i j k l = a ^ 4 := by
  unfold moment4 kronecker
  simp [hij, hik, hil, hjk, hjl, hkl]

lemma moment4_one_square (a s : ℝ) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    moment4 a s i i j k = a ^ 2 * (a ^ 2 + s) := by
  unfold moment4 kronecker
  simp [hij, hik, hjk]
  ring

lemma moment4_repeat_pair (a s : ℝ) {i j : Fin m} (hij : i ≠ j) :
    moment4 a s i j i j = (a ^ 2 + s) ^ 2 := by
  unfold moment4 kronecker
  simp [hij, hij.symm]
  ring

lemma moment4_two_squares (a s : ℝ) {i j : Fin m} (hij : i ≠ j) :
    moment4 a s i i j j = (a ^ 2 + s) ^ 2 := by
  unfold moment4 kronecker
  simp [hij, hij.symm]
  ring

lemma sum_diag_zero {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) :
    ∑ i, A i i = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  exact zeroDiagonal_apply hZ i

lemma sum_const_mul_fin (c : ℝ) (f : Fin m → ℝ) : ∑ i, c * f i = c * ∑ i, f i :=
  (Finset.mul_sum Finset.univ f c).symm

lemma sum_mul_const_fin (f : Fin m → ℝ) (c : ℝ) : ∑ i, f i * c = (∑ i, f i) * c :=
  (Finset.sum_mul Finset.univ f c).symm

lemma sum_sum_const_mul (c : ℝ) (f : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, c * f i j = c * ∑ i, ∑ j, f i j :=
  (Finset.sum_congr rfl fun i _ => sum_const_mul_fin c (fun j => f i j)).trans
    (sum_const_mul_fin c (fun i => ∑ j, f i j))

lemma sum_sum_mul_const (f : Fin m → Fin m → ℝ) (c : ℝ) :
    ∑ i, ∑ j, f i j * c = (∑ i, ∑ j, f i j) * c :=
  (Finset.sum_congr rfl fun i _ => sum_mul_const_fin (fun j => f i j) c).trans
    (sum_mul_const_fin (fun i => ∑ j, f i j) c)

lemma entrySum_factor (A : Matrix (Fin m) (Fin m) ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l = entrySum A * entrySum A := by
  unfold entrySum
  have hinner : ∀ i j, ∑ k, ∑ l, A i j * A k l = A i j * ∑ k, ∑ l, A k l := by
    intro i j
    exact (Finset.sum_congr rfl fun k _ =>
      sum_const_mul_fin (A i j) (fun l => A k l)).trans
      (sum_const_mul_fin (A i j) (fun k => ∑ l, A k l))
  exact (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => hinner i j).trans
    (sum_sum_mul_const (fun i j => A i j) (∑ k, ∑ l, A k l))

theorem quadMoment_zeroDiagonal {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) (a s : ℝ) :
    quadMoment a s A = a ^ 2 * entrySum A := by
  unfold quadMoment entrySum
  simp_rw [moment2_eq, mul_add, Finset.sum_add_distrib]
  have hdiag : ∑ i, ∑ j, A i j * (if i = j then s else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp_rw [mul_ite, mul_zero]
    have hpick : ∑ j, (if i = j then A i j * s else 0) = A i i * s :=
      sum_eq_of_ite i (fun j => A i j * s)
    rw [hpick, zeroDiagonal_apply hZ i]
    ring
  have hmain : ∑ i, ∑ j, A i j * a ^ 2 = a ^ 2 * ∑ i, ∑ j, A i j := by
    have hcomm : ∀ i j, A i j * a ^ 2 = a ^ 2 * A i j := by
      intro i j
      ring
    simp_rw [hcomm, ← Finset.mul_sum]
  rw [hdiag, add_zero, hmain]

lemma sum_mul_self_diag {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ j, A i j * A j i = frobSq A := by
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply i j]
  ring

lemma sum_triple_rowSumSq {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ k, ∑ j, A i j * A j k = rowSumSq A := by
  have hstep1 : ∑ i, ∑ k, ∑ j, A i j * A j k = ∑ i, ∑ j, ∑ k, A i j * A j k := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hstep2 : ∑ i, ∑ j, ∑ k, A i j * A j k = ∑ j, ∑ i, ∑ k, A i j * A j k :=
    Finset.sum_comm
  have hstep3 : ∑ j, ∑ i, ∑ k, A i j * A j k = ∑ j, ∑ i, A i j * ∑ k, A j k := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Finset.mul_sum Finset.univ (fun k => A j k) (A i j)).symm
  have hstep4 : ∑ j, ∑ i, A i j * ∑ k, A j k = ∑ j, (∑ i, A i j) * ∑ k, A j k := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finset.sum_mul Finset.univ (fun i => A i j) (∑ k, A j k)).symm
  have hsym : ∑ j, (∑ i, A i j) * ∑ k, A j k = ∑ j, (∑ i, A j i) * ∑ k, A j k := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine congrArg (fun t => t * ∑ k, A j k) ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hA.apply j i
  have hsq : ∑ j, (∑ i, A j i) * ∑ k, A j k = rowSumSq A := by
    unfold rowSumSq
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (pow_two (∑ i, A j i)).symm
  exact hstep1.trans hstep2 |>.trans hstep3 |>.trans hstep4 |>.trans hsym |>.trans hsq

theorem trace_mul_self_eq_frobSq {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    Matrix.trace (A * A) = frobSq A := by
  simp_rw [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact sum_mul_self_diag hA

theorem quadMoment_mul_symm {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (a s : ℝ) :
    quadMoment a s (A * A) = s * frobSq A + a ^ 2 * rowSumSq A := by
  unfold quadMoment
  simp_rw [Matrix.mul_apply, moment2_eq]
  have hsplit : ∀ i k,
      (∑ j, A i j * A j k) * (a ^ 2 + if i = k then s else 0) =
        (∑ j, A i j * A j k) * a ^ 2 +
          (∑ j, A i j * A j k) * (if i = k then s else 0) := by
    intro i k
    exact mul_add _ _ _
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hvar : ∑ i, ∑ k, (∑ j, A i j * A j k) * (if i = k then s else 0) =
      s * frobSq A := by
    have hpick : ∀ i, ∑ k, (∑ j, A i j * A j k) * (if i = k then s else 0) =
        (∑ j, A i j * A j i) * s := by
      intro i
      have hform : ∀ k, (∑ j, A i j * A j k) * (if i = k then s else 0) =
          if i = k then (∑ j, A i j * A j k) * s else 0 := by
        intro k
        by_cases hk : i = k
        · simp [hk]
        · simp [hk]
      simp_rw [hform]
      exact sum_eq_of_ite i (fun k => (∑ j, A i j * A j k) * s)
    simp_rw [hpick]
    have hsum : ∑ i, (∑ j, A i j * A j i) * s = (∑ i, ∑ j, A i j * A j i) * s := by
      simp_rw [← Finset.sum_mul]
    rw [hsum, sum_mul_self_diag hA]
    ring
  have hmean : ∑ i, ∑ k, (∑ j, A i j * A j k) * a ^ 2 = a ^ 2 * rowSumSq A := by
    have hcomm : ∀ i k, (∑ j, A i j * A j k) * a ^ 2 = a ^ 2 * ∑ j, A i j * A j k := by
      intro i k
      ring
    simp_rw [hcomm, ← Finset.mul_sum]
    rw [sum_triple_rowSumSq hA]
  rw [hmean, hvar]
  ring

lemma contract_one (A : Matrix (Fin m) (Fin m) ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l = entrySum A * entrySum A :=
  entrySum_factor A

lemma scaleKronecker (c : ℝ) (p : Fin m) (g : Fin m → ℝ) :
    ∑ t, c * g t * kronecker p t = c * g p := by
  have hmul : ∀ t, c * g t * kronecker p t = c * (g t * kronecker p t) := fun t => by ring
  exact (Finset.sum_congr rfl fun t _ => hmul t).trans
    ((sum_const_mul_fin c (fun t => g t * kronecker p t)).trans
      (congrArg (fun z => c * z) (sum_kronecker p g)))

lemma contract_kronecker_ij {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker i j = 0 := by
  have hper : ∀ i j, ∑ k, ∑ l, A i j * A k l * kronecker i j =
      (A i j * kronecker i j) * ∑ k, ∑ l, A k l := by
    intro i j
    have hmul : ∀ k l, A i j * A k l * kronecker i j =
        (A i j * kronecker i j) * A k l := fun k l => by ring
    exact (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hmul k l).trans
      (sum_sum_const_mul (A i j * kronecker i j) (fun k l => A k l))
  have hdiag : ∑ i, ∑ j, A i j * kronecker i j = ∑ i, A i i :=
    Finset.sum_congr rfl fun i _ => sum_kronecker i (fun j => A i j)
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hper i j).trans
    ((sum_sum_mul_const (fun i j => A i j * kronecker i j) (∑ k, ∑ l, A k l)).trans
      ((congrArg (fun t => t * ∑ k, ∑ l, A k l) hdiag).trans
        ((congrArg (fun t => t * ∑ k, ∑ l, A k l) (sum_diag_zero hZ)).trans (zero_mul _))))

lemma contract_kronecker_kl {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker k l = 0 := by
  have hl : ∀ i j k, ∑ l, A i j * A k l * kronecker k l = A i j * A k k :=
    fun i j k => scaleKronecker (A i j) k (fun l => A k l)
  have h2 : ∑ i, ∑ j, ∑ k, A i j * A k k = ∑ i, ∑ j, A i j * ∑ k, A k k :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      sum_const_mul_fin (A i j) (fun k => A k k)
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => hl i j k).trans
    (h2.trans ((sum_sum_mul_const (fun i j => A i j) (∑ k, A k k)).trans
      ((congrArg (fun t => (∑ i, ∑ j, A i j) * t) (sum_diag_zero hZ)).trans (mul_zero _))))

lemma sum_rowProd_eq_rowSumSq (A : Matrix (Fin m) (Fin m) ℝ) :
    ∑ i, (∑ j, A i j) * ∑ l, A i l = rowSumSq A := by
  unfold rowSumSq
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (pow_two (∑ j, A i j)).symm

lemma contract_kronecker_ik (A : Matrix (Fin m) (Fin m) ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker i k = rowSumSq A := by
  have hinner : ∀ i j l, ∑ k, A i j * A k l * kronecker i k = A i j * A i l :=
    fun i j l => scaleKronecker (A i j) i (fun k => A k l)
  have hswap : ∀ i j, ∑ k, ∑ l, A i j * A k l * kronecker i k = ∑ l, A i j * A i l := by
    intro i j
    have hcomm : ∑ k, ∑ l, A i j * A k l * kronecker i k =
        ∑ l, ∑ k, A i j * A k l * kronecker i k := Finset.sum_comm
    exact hcomm.trans (Finset.sum_congr rfl fun l _ => hinner i j l)
  have hfac : ∑ i, ∑ j, ∑ l, A i j * A i l = ∑ i, (∑ j, A i j) * ∑ l, A i l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Finset.sum_congr rfl fun j _ => sum_const_mul_fin (A i j) (fun l => A i l)).trans
      (sum_mul_const_fin (fun j => A i j) (∑ l, A i l))
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hswap i j).trans
    (hfac.trans (sum_rowProd_eq_rowSumSq A))

lemma contract_kronecker_jl {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker j l = rowSumSq A := by
  have hkill : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker j l =
      ∑ i, ∑ j, ∑ k, A i j * A k j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmul : ∀ l, A i j * A k l * kronecker j l = A i j * (A k l * kronecker j l) := by
      intro l
      ring
    simp_rw [hmul, ← Finset.mul_sum]
    refine congrArg (fun t => A i j * t) ?_
    exact sum_kronecker j (fun l => A k l)
  have hfactor : ∑ i, ∑ j, ∑ k, A i j * A k j = ∑ j, (∑ i, A i j) * ∑ k, A k j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finset.sum_congr rfl fun i _ => sum_const_mul_fin (A i j) (fun k => A k j)).trans
      (sum_mul_const_fin (fun i => A i j) (∑ k, A k j))
  have hsym : ∑ j, (∑ i, A i j) * ∑ k, A k j = ∑ j, (rowSum A j) * rowSum A j := by
    unfold rowSum
    refine Finset.sum_congr rfl fun j _ => ?_
    have hleft : ∑ i, A i j = ∑ i, A j i := by
      refine Finset.sum_congr rfl fun i _ => hA.apply j i
    have hright : ∑ k, A k j = ∑ k, A j k := by
      refine Finset.sum_congr rfl fun k _ => hA.apply j k
    exact congrArg (fun t : ℝ => t*t) hleft
  rw [hkill, hfactor, hsym, rowSumSq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_two]

lemma contract_kronecker_il {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker i l = rowSumSq A := by
  have hkill : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker i l =
      ∑ i, ∑ j, ∑ k, A i j * A k i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmul : ∀ l, A i j * A k l * kronecker i l = A i j * (A k l * kronecker i l) := by
      intro l
      ring
    simp_rw [hmul, ← Finset.mul_sum]
    refine congrArg (fun t => A i j * t) ?_
    exact sum_kronecker i (fun l => A k l)
  have hfactor : ∑ i, ∑ j, ∑ k, A i j * A k i = ∑ i, (∑ j, A i j) * ∑ k, A k i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinner : ∀ j, ∑ k, A i j * A k i = A i j * ∑ k, A k i := by
      intro j
      exact (Finset.mul_sum Finset.univ (fun k => A k i) (A i j)).symm
    simp_rw [hinner, ← Finset.sum_mul]
  have hsym : ∑ i, (∑ j, A i j) * ∑ k, A k i = ∑ i, (rowSum A i) * rowSum A i := by
    unfold rowSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have hright : ∑ k, A k i = ∑ k, A i k := by
      refine Finset.sum_congr rfl fun k _ => hA.apply i k
    rw [hright]
  rw [hkill, hfactor, hsym, rowSumSq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_two]

lemma contract_kronecker_jk {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker j k = rowSumSq A := by
  have hkill : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * kronecker j k =
      ∑ i, ∑ j, ∑ l, A i j * A j l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hmul : ∀ k, A i j * A k l * kronecker j k = A i j * (A k l * kronecker j k) := by
      intro k
      ring
    simp_rw [hmul, ← Finset.mul_sum]
    refine congrArg (fun t => A i j * t) ?_
    exact sum_kronecker j (fun k => A k l)
  have hfactor : ∑ i, ∑ j, ∑ l, A i j * A j l = ∑ j, (∑ i, A i j) * ∑ l, A j l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finset.sum_congr rfl fun i _ => sum_const_mul_fin (A i j) (fun k => A j k)).trans
      (sum_mul_const_fin (fun i => A i j) (∑ k, A j k))
  have hsym : ∑ j, (∑ i, A i j) * ∑ l, A j l = ∑ j, (rowSum A j) * rowSum A j := by
    unfold rowSum
    refine Finset.sum_congr rfl fun j _ => ?_
    have hleft : ∑ i, A i j = ∑ i, A j i := by
      refine Finset.sum_congr rfl fun i _ => hA.apply j i
    rw [hleft]
  rw [hkill, hfactor, hsym, rowSumSq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_two]

lemma contract_pair_ij_kl {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (kronecker i j * kronecker k l) = 0 := by
  have hz : ∀ i j, A i j*kronecker i j=0 := by
    intro i j
    by_cases he : i=j
    · subst j
      rw [zeroDiagonal_apply hZ i, zero_mul]
    · simp [kronecker, he]
  have ht : ∀ i j k l, A i j*A k l*(kronecker i j*kronecker k l)=0 := by
    intro i j k l
    calc
      _ = (A i j*kronecker i j)*(A k l*kronecker k l) := by ring
      _ = 0 := by rw [hz, zero_mul]
  simp_rw [ht]
  simp
lemma contract_pair_ik_jl (A : Matrix (Fin m) (Fin m) ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (kronecker i k * kronecker j l) = frobSq A := by
  have hkill : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (kronecker i k * kronecker j l) =
      ∑ i, ∑ j, A i j * A i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have hl : ∀ l, ∑ k, A i j * A k l * (kronecker i k * kronecker j l) =
        A i j * kronecker j l * A i l := by
      intro l
      have hmul : ∀ k, A i j * A k l * (kronecker i k * kronecker j l) =
          (A i j * kronecker j l) * (A k l * kronecker i k) := by
        intro k
        ring
      simp_rw [hmul, ← Finset.mul_sum]
      exact congrArg (fun t => (A i j * kronecker j l) * t) (sum_kronecker i (fun k => A k l))
    simp_rw [hl]
    have hmul : ∀ l, A i j * kronecker j l * A i l = A i j * (A i l * kronecker j l) := by
      intro l
      ring
    simp_rw [hmul, ← Finset.mul_sum]
    exact congrArg (fun t => A i j * t) (sum_kronecker j (fun l => A i l))
  rw [hkill]
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma contract_pair_il_jk {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (kronecker i l * kronecker j k) = frobSq A := by
  have hkill : ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (kronecker i l * kronecker j k) =
      ∑ i, ∑ j, A i j * A j i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have hk : ∀ k, ∑ l, A i j * A k l * (kronecker i l * kronecker j k) =
        A i j * kronecker j k * A k i := by
      intro k
      have hmul : ∀ l, A i j * A k l * (kronecker i l * kronecker j k) =
          (A i j * kronecker j k) * (A k l * kronecker i l) := by
        intro l
        ring
      simp_rw [hmul, ← Finset.mul_sum]
      exact congrArg (fun t => (A i j * kronecker j k) * t) (sum_kronecker i (fun l => A k l))
    simp_rw [hk]
    have hmul : ∀ k, A i j * kronecker j k * A k i = A i j * (A k i * kronecker j k) := by
      intro k
      ring
    simp_rw [hmul, ← Finset.mul_sum]
    exact congrArg (fun t => A i j * t) (sum_kronecker j (fun k => A k i))
  rw [hkill, sum_mul_self_diag hA]

lemma sum4_add3 (f g h : Fin m → Fin m → Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (f i j k l + g i j k l + h i j k l) =
      (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) +
        (∑ i, ∑ j, ∑ k, ∑ l, g i j k l) +
        ∑ i, ∑ j, ∑ k, ∑ l, h i j k l := by
  simp_rw [Finset.sum_add_distrib]

lemma sum4_const (c : ℝ) (f : Fin m → Fin m → Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, c * f i j k l = c * ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
  simp_rw [← Finset.mul_sum]

theorem quadSquareMoment_symm_zeroDiagonal {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) (a s : ℝ) :
    quadSquareMoment a s A =
      2 * s ^ 2 * frobSq A + 4 * a ^ 2 * s * rowSumSq A + a ^ 4 * (entrySum A) ^ 2 := by
  unfold quadSquareMoment
  have hmul : ∀ i j k l, A i j * A k l * moment4 a s i j k l =
      a ^ 4 * (A i j * A k l) +
        (a ^ 2 * s) * (A i j * A k l * (kronecker i j + kronecker i k + kronecker i l +
          kronecker j k + kronecker j l + kronecker k l)) +
        s ^ 2 * (A i j * A k l * (kronecker i j * kronecker k l +
          kronecker i k * kronecker j l + kronecker i l * kronecker j k)) := by
    intro i j k l
    unfold moment4
    ring
  simp_rw [hmul]
  rw [sum4_add3
    (fun i j k l => a ^ 4 * (A i j * A k l))
    (fun i j k l => (a ^ 2 * s) * (A i j * A k l * (kronecker i j + kronecker i k +
      kronecker i l + kronecker j k + kronecker j l + kronecker k l)))
    (fun i j k l => s ^ 2 * (A i j * A k l * (kronecker i j * kronecker k l +
      kronecker i k * kronecker j l + kronecker i l * kronecker j k)))]
  have h4 : ∑ i, ∑ j, ∑ k, ∑ l, a ^ 4 * (A i j * A k l) =
      a ^ 4 * (entrySum A * entrySum A) := by
    rw [sum4_const, contract_one]
  have hdist : ∀ i j k l, A i j * A k l * (kronecker i j + kronecker i k + kronecker i l +
      kronecker j k + kronecker j l + kronecker k l) =
      A i j * A k l * kronecker i j + A i j * A k l * kronecker i k +
        A i j * A k l * kronecker i l + A i j * A k l * kronecker j k +
        A i j * A k l * kronecker j l + A i j * A k l * kronecker k l := by
    intro i j k l
    ring
  have hpair : ∀ i j k l, A i j * A k l * (kronecker i j * kronecker k l +
      kronecker i k * kronecker j l + kronecker i l * kronecker j k) =
      A i j * A k l * (kronecker i j * kronecker k l) +
        A i j * A k l * (kronecker i k * kronecker j l) +
        A i j * A k l * (kronecker i l * kronecker j k) := by
    intro i j k l
    ring
  have hcross : ∑ i, ∑ j, ∑ k, ∑ l, (a ^ 2 * s) * (A i j * A k l *
      (kronecker i j + kronecker i k + kronecker i l + kronecker j k + kronecker j l +
        kronecker k l)) =
      (a ^ 2 * s) * (4 * rowSumSq A) := by
    rw [sum4_const]
    simp_rw [hdist, Finset.sum_add_distrib]
    rw [contract_kronecker_ij hZ, contract_kronecker_ik,
      contract_kronecker_il hA, contract_kronecker_jk hA,
      contract_kronecker_jl hA, contract_kronecker_kl hZ]
    ring
  have hsq : ∑ i, ∑ j, ∑ k, ∑ l, s ^ 2 * (A i j * A k l *
      (kronecker i j * kronecker k l + kronecker i k * kronecker j l +
        kronecker i l * kronecker j k)) =
      s ^ 2 * (2 * frobSq A) := by
    rw [sum4_const]
    simp_rw [hpair]
    rw [sum4_add3
      (fun i j k l => A i j * A k l * (kronecker i j * kronecker k l))
      (fun i j k l => A i j * A k l * (kronecker i k * kronecker j l))
      (fun i j k l => A i j * A k l * (kronecker i l * kronecker j k))]
    rw [contract_pair_ij_kl hZ, contract_pair_ik_jl, contract_pair_il_jk hA]
    ring
  rw [h4, hcross, hsq]
  ring

lemma sum_cross_left (A : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) (a : ℝ) :
    ∑ i, ∑ j, a * z i * A i j = a * ∑ i, (∑ j, A i j) * z i := by
  have h1 : ∀ i, ∑ j, a * z i * A i j = a * z i * ∑ j, A i j := by
    intro i
    exact (Finset.mul_sum Finset.univ (fun j => A i j) (a * z i)).symm
  simp_rw [h1]
  have h2 : ∀ i, a * z i * ∑ j, A i j = a * ((∑ j, A i j) * z i) := by
    intro i
    ring
  simp_rw [h2, ← Finset.mul_sum]

lemma sum_cross_right {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (z : Fin m → ℝ) (a : ℝ) :
    ∑ i, ∑ j, a * A i j * z j = a * ∑ i, (∑ j, A i j) * z i := by
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i, a * A i j * z j = a * z j * ∑ i, A i j := by
    intro j
    have hmul : ∀ i, a * A i j * z j = a * z j * A i j := by
      intro i
      ring
    simp_rw [hmul]
    exact (Finset.mul_sum Finset.univ (fun i => A i j) (a * z j)).symm
  simp_rw [h2]
  have h3 : ∀ j, a * z j * ∑ i, A i j = a * ((∑ i, A j i) * z j) := by
    intro j
    have hsym : ∑ i, A i j = ∑ i, A j i := by
      refine Finset.sum_congr rfl fun i _ => hA.apply j i
    rw [hsym]
    ring
  simp_rw [h3, ← Finset.mul_sum]

lemma sum_const_sq (A : Matrix (Fin m) (Fin m) ℝ) (a : ℝ) :
    ∑ i, ∑ j, a ^ 2 * A i j = a ^ 2 * ∑ i, ∑ j, A i j := by
  simp_rw [← Finset.mul_sum]

/-- Pointwise expansion `x = a + (x - a)` of the quadratic form. Symmetry identifies the two
cross terms; a zero diagonal is not required. -/
theorem quad_center_expand {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm)
    (x : Fin m → ℝ) (a : ℝ) :
    ∑ i, ∑ j, x i * A i j * x j =
      a ^ 2 * ∑ i, ∑ j, A i j +
        2 * a * ∑ i, (∑ j, A i j) * (x i - a) +
        ∑ i, ∑ j, (x i - a) * A i j * (x j - a) := by
  have hx : ∀ i, x i = (x i - a) + a := fun i => (sub_add_cancel (x i) a).symm
  calc
    ∑ i, ∑ j, x i * A i j * x j
        = ∑ i, ∑ j, ((x i - a) + a) * A i j * ((x j - a) + a) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = ∑ i, ∑ j, ((x i - a) * A i j * (x j - a) + a * (x i - a) * A i j +
          a * A i j * (x j - a) + a ^ 2 * A i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = ∑ i, ∑ j, (x i - a) * A i j * (x j - a) +
          ∑ i, ∑ j, a * (x i - a) * A i j +
          ∑ i, ∑ j, a * A i j * (x j - a) +
          ∑ i, ∑ j, a ^ 2 * A i j := by
          simp_rw [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (x i - a) * A i j * (x j - a) +
          a * ∑ i, (∑ j, A i j) * (x i - a) +
          a * ∑ i, (∑ j, A i j) * (x i - a) +
          a ^ 2 * ∑ i, ∑ j, A i j := by
          rw [sum_cross_left A (fun i => x i - a) a,
            sum_cross_right hA (fun i => x i - a) a, sum_const_sq A a]
    _ = a ^ 2 * ∑ i, ∑ j, A i j +
          2 * a * ∑ i, (∑ j, A i j) * (x i - a) +
          ∑ i, ∑ j, (x i - a) * A i j * (x j - a) := by
          ring

theorem quad_center_expand_euclidean {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm)
    (x : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    quad A x =
      a ^ 2 * entrySum A +
        2 * a * ∑ i, (∑ j, A i j) * (x i - a) +
        ∑ i, ∑ j, (x i - a) * A i j * (x j - a) := by
  simpa [quad, entrySum] using quad_center_expand hA (fun i => x i) a

lemma sum_sq_four (f : Fin m → Fin m → ℝ) :
    (∑ i, ∑ j, f i j) ^ 2 = ∑ i, ∑ j, ∑ k, ∑ l, f i j * f k l := by
  have h1 : (∑ i, ∑ j, f i j) * ∑ k, ∑ l, f k l =
      ∑ i, ∑ j, f i j * ∑ k, ∑ l, f k l :=
    (sum_sum_mul_const f (∑ k, ∑ l, f k l)).symm
  have h2 : ∑ i, ∑ j, f i j * ∑ k, ∑ l, f k l =
      ∑ i, ∑ j, ∑ k, ∑ l, f i j * f k l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (sum_sum_const_mul (f i j) f).symm
  exact (pow_two _).trans (h1.trans h2)

theorem quad_sq_monomials (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    (quad A x) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (x i * x j * x k * x l) := by
  unfold quad
  rw [sum_sq_four (fun i j => x i * A i j * x j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma densityCoeff_poly (F R T a s : ℝ) :
    F / 4 + (2 * s ^ 2 * F + 4 * a ^ 2 * s * R + a ^ 4 * T ^ 2) / 8 -
        (s * F + a ^ 2 * R) / 2 =
      F * (1 - s) ^ 2 / 4 - a ^ 2 * R * (1 - s) / 2 + a ^ 4 * T ^ 2 / 8 := by
  field_simp
  ring

lemma densityCoeff_trunc (F R T q h σ : ℝ) (hσ : 1 - σ = q * h) :
    F / 4 + (2 * σ ^ 2 * F + 4 * q ^ 2 * σ * R + q ^ 4 * T ^ 2) / 8 -
        (σ * F + q ^ 2 * R) / 2 =
      (q * h) ^ 2 / 4 * F - q ^ 2 * (q * h) / 2 * R + q ^ 4 / 8 * T ^ 2 := by
  have ha2 : (-q) ^ 2 = q ^ 2 := by ring
  have ha4 : (-q) ^ 4 = q ^ 4 := by ring
  have hpoly := densityCoeff_poly F R T (-q) σ
  rw [ha2, ha4] at hpoly
  rw [hpoly, hσ]
  ring

/-- `trace(A*A)/4 + E[(quad A)²]/8 - E[quad (A*A)]/2` at mean `-q` and variance `σ`. -/
theorem quadDensityCoeffMoment_truncGauss {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) {q h σ : ℝ} (hσ : 1 - σ = q * h) :
    quadDensityCoeffMoment (-q) σ A =
      (q * h) ^ 2 / 4 * frobSq A - q ^ 2 * (q * h) / 2 * rowSumSq A +
        q ^ 4 / 8 * (entrySum A) ^ 2 := by
  unfold quadDensityCoeffMoment
  rw [quadSquareMoment_symm_zeroDiagonal hA hZ (-q) σ, quadMoment_mul_symm hA (-q) σ,
    trace_mul_self_eq_frobSq hA]
  have ha2 : (-q) ^ 2 = q ^ 2 := by ring
  have ha4 : (-q) ^ 4 = q ^ 4 := by ring
  rw [ha2, ha4]
  simpa using densityCoeff_trunc (frobSq A) (rowSumSq A) (entrySum A) q h σ hσ

theorem quadDensityCoeffMoment_div_qsq {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) {q h σ : ℝ} (hq : q ≠ 0) (hσ : 1 - σ = q * h) :
    quadDensityCoeffMoment (-q) σ A / q ^ 2 =
      h ^ 2 / 4 * frobSq A - (q * h / 2) * rowSumSq A + q ^ 2 / 8 * (entrySum A) ^ 2 := by
  rw [quadDensityCoeffMoment_truncGauss hA hZ hσ]
  field_simp [hq]

theorem secondOrderMoment_div_qsq {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) {q h σ : ℝ} (hq : q ≠ 0) (hσ : 1 - σ = q * h) :
    secondOrderMoment (-q) σ A / q ^ 2 =
      entrySum A / 2 + h ^ 2 / 4 * frobSq A - (q * h / 2) * rowSumSq A +
        q ^ 2 / 8 * (entrySum A) ^ 2 := by
  unfold secondOrderMoment
  rw [quadMoment_zeroDiagonal hZ (-q) σ]
  have ha2 : (-q) ^ 2 = q ^ 2 := by ring
  rw [ha2]
  have hdiv : (q ^ 2 * entrySum A / 2 + quadDensityCoeffMoment (-q) σ A) / q ^ 2 =
      entrySum A / 2 + quadDensityCoeffMoment (-q) σ A / q ^ 2 := by
    field_simp [hq]
  rw [hdiv, quadDensityCoeffMoment_div_qsq hA hZ hq hσ]
  ring

/-- Algebraic form of the quadratic ratio, divided by `q²`.
`halfEntrySum A = entrySum A / 2` and `frobSq A / 2` is half the sum of squares.
This is not an integral. -/
theorem secondOrderMoment_triangle {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) {q h σ : ℝ} (hq : q ≠ 0) (hσ : 1 - σ = q * h) :
    secondOrderMoment (-q) σ A / q ^ 2 =
      halfEntrySum A + (h ^ 2 / 2) * (frobSq A / 2) -
        (q * h / 2) * rowSumSq A + (q ^ 2 / 2) * (halfEntrySum A) ^ 2 := by
  rw [secondOrderMoment_div_qsq hA hZ hq hσ]
  simp only [halfEntrySum]
  field_simp
  ring

#print axioms quadMoment_zeroDiagonal
#print axioms quadMoment_mul_symm
#print axioms quadSquareMoment_symm_zeroDiagonal
#print axioms quad_center_expand
#print axioms quadDensityCoeffMoment_truncGauss
#print axioms secondOrderMoment_div_qsq
#print axioms secondOrderMoment_triangle

end SimplexFull.Covariance
