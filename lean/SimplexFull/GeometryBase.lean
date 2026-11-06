import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Geometric base for the strict-normal shell in `input/ANALYTIC_PROOF.md`, Section 11.

`simplexGram m` is the algebraic Gram `α⁻¹ (I - J / m)` with `α = (m - 1) / m`.
`Orthogonal d` is the orthogonal group `O(d)` as linear isometric equivalences of
Euclidean `d`-space. `normalConfig` is the strict-normal family
`i ↦ k • V i + t • z`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace SimplexFull.Geometry

abbrev Config (m d : Nat) := Fin m → EuclideanSpace Real (Fin d)

def gram (X : Config m d) : Matrix (Fin m) (Fin m) Real :=
  Matrix.gram Real X

lemma gram_apply (X : Config m d) (i j : Fin m) :
    gram X i j = inner ℝ (X i) (X j) :=
  rfl

def UnitConfig (X : Config m d) : Prop :=
  ∀ i, norm (X i) = 1

def alpha (m : Nat) : Real :=
  ((m : Real) - 1) / (m : Real)

def onesMatrix (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  fun _ _ => 1

def centering (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  (1 : Matrix (Fin m) (Fin m) Real) - (m : Real)⁻¹ • onesMatrix m

def simplexGram (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  (alpha m)⁻¹ • centering m

/-- `O(d)`, as linear isometric automorphisms of Euclidean `d`-space. -/
abbrev Orthogonal (d : Nat) :=
  EuclideanSpace Real (Fin d) ≃ₗᵢ[Real] EuclideanSpace Real (Fin d)

/-- Action of `O(d)` on an `m`-point configuration. -/
def act {m d : Nat} (U : Orthogonal d) (X : Config m d) : Config m d :=
  fun i => U (X i)

/-- Two configurations lie on the same `O(d)` orbit. -/
def orthoOrbit {m d : Nat} (X Y : Config m d) : Prop :=
  ∃ U : Orthogonal d, ∀ i, Y i = U (X i)

def onesVec (m : Nat) : Fin m → Real :=
  fun _ => 1

/-- Strict-normal configuration `i ↦ k • V i + t • z`. -/
def normalConfig {m d : Nat} (k t : Real) (V : Config m d)
    (z : EuclideanSpace Real (Fin d)) : Config m d :=
  fun i => k • V i + t • z

theorem gram_posSemidef {m d : Nat} (X : Config m d) :
    Matrix.PosSemidef (gram X) :=
  Matrix.posSemidef_gram Real X

theorem gram_diagonal_unit {m d : Nat} (X : Config m d) (hX : UnitConfig X)
    (i : Fin m) : gram X i i = 1 := by
  rw [gram_apply, real_inner_self_eq_norm_sq, hX i, one_pow]

theorem orthoOrbit_refl {m d : Nat} (X : Config m d) : orthoOrbit X X := by
  refine ⟨LinearIsometryEquiv.refl Real (EuclideanSpace Real (Fin d)), fun i => ?_⟩
  simp

theorem orthoOrbit_symm {m d : Nat} {X Y : Config m d} (h : orthoOrbit X Y) :
    orthoOrbit Y X := by
  rcases h with ⟨U, hU⟩
  refine ⟨U.symm, fun i => ?_⟩
  rw [hU i]
  exact (U.symm_apply_apply (X i)).symm

theorem orthoOrbit_trans {m d : Nat} {X Y Z : Config m d}
    (hXY : orthoOrbit X Y) (hYZ : orthoOrbit Y Z) : orthoOrbit X Z := by
  rcases hXY with ⟨U, hU⟩
  rcases hYZ with ⟨W, hW⟩
  refine ⟨U.trans W, fun i => ?_⟩
  rw [LinearIsometryEquiv.trans_apply, ← hU i, ← hW i]

theorem gram_act {m d : Nat} (U : Orthogonal d) (X : Config m d) :
    gram (act U X) = gram X := by
  ext i j
  rw [gram_apply, gram_apply]
  simp only [act]
  rw [LinearIsometryEquiv.inner_map_map]

theorem gram_orthoOrbit {m d : Nat} {X Y : Config m d} (h : orthoOrbit X Y) :
    gram Y = gram X := by
  rcases h with ⟨U, hU⟩
  ext i j
  rw [gram_apply, gram_apply, hU i, hU j, LinearIsometryEquiv.inner_map_map]

theorem gram_normalConfig {m d : Nat} (k t : Real) (V : Config m d)
    (z : EuclideanSpace Real (Fin d))
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : norm z = 1) :
    gram (normalConfig k t V z) =
      k ^ 2 • gram V + t ^ 2 • onesMatrix m := by
  ext i j
  simp only [gram_apply, normalConfig, Matrix.add_apply, Matrix.smul_apply, onesMatrix,
    smul_eq_mul]
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [real_inner_smul_left, inner_smul_right, real_inner_smul_left, inner_smul_right,
    real_inner_smul_left, inner_smul_right, real_inner_smul_left, inner_smul_right]
  rw [hperp i, ← real_inner_comm z (V j), hperp j, real_inner_self_eq_norm_sq, hz, one_pow]
  ring

theorem unitConfig_normalConfig {m d : Nat} (k t : Real) (V : Config m d)
    (z : EuclideanSpace Real (Fin d)) (hV : UnitConfig V)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : norm z = 1)
    (hkt : k ^ 2 + t ^ 2 = 1) :
    UnitConfig (normalConfig k t V z) := by
  intro i
  have hii := congr_fun (congr_fun (gram_normalConfig k t V z hperp hz) i) i
  have hinner :
      inner ℝ (normalConfig k t V z i) (normalConfig k t V z i) = 1 := by
    simpa [Matrix.add_apply, Matrix.smul_apply, onesMatrix, smul_eq_mul, gram_apply,
      real_inner_self_eq_norm_sq, hV i, one_pow, mul_one, hkt] using hii
  rw [norm_eq_sqrt_real_inner, hinner, Real.sqrt_one]

theorem alpha_eq_one_sub_inv (m : Nat) (hm : m ≠ 0) :
    alpha m = 1 - (m : Real)⁻¹ := by
  have hmR : (m : Real) ≠ 0 := Nat.cast_ne_zero.mpr hm
  unfold alpha
  field_simp [hmR]

theorem centering_apply_diag (m : Nat) (i : Fin m) :
    centering m i i = 1 - (m : Real)⁻¹ := by
  simp [centering, onesMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_one]

theorem alpha_ne_zero_of_gt_one (m : Nat) (hm : 1 < m) : alpha m ≠ 0 := by
  have hm0 : m ≠ 0 := (Nat.lt_trans Nat.zero_lt_one hm).ne'
  unfold alpha
  apply div_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hm)
  · exact Nat.cast_ne_zero.mpr hm0

theorem simplexGram_diagonal (m : Nat) (hm : 1 < m) (i : Fin m) :
    simplexGram m i i = 1 := by
  have hm0 : m ≠ 0 := (Nat.lt_trans Nat.zero_lt_one hm).ne'
  have hcent : centering m i i = alpha m := by
    rw [centering_apply_diag, alpha_eq_one_sub_inv m hm0]
  rw [simplexGram, Matrix.smul_apply, smul_eq_mul, hcent,
    inv_mul_cancel₀ (alpha_ne_zero_of_gt_one m hm)]

theorem simplexGram_offDiag (m : Nat) (hm : 1 < m) {i j : Fin m} (hij : i ≠ j) :
    simplexGram m i j = -((m : Real) - 1)⁻¹ := by
  have hm0 : m ≠ 0 := (Nat.lt_trans Nat.zero_lt_one hm).ne'
  have hmR : (m : Real) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hm1R : (m : Real) ≠ 1 := by exact_mod_cast Nat.ne_of_gt hm
  rw [simplexGram, Matrix.smul_apply, smul_eq_mul, centering, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_neg hij, onesMatrix]
  simp only [mul_one, zero_sub]
  unfold alpha
  field_simp [hmR, hm1R]

/-- Each row of the centering matrix sums to zero, so the all-ones vector is a barycenter. -/
theorem centering_mulVec_ones (m : Nat) (hm : m ≠ 0) :
    Matrix.mulVec (centering m) (onesVec m) = 0 := by
  ext i
  rw [centering, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [onesVec, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  have hrow : (Matrix.mulVec (onesMatrix m) (onesVec m)) i = (m : Real) := by
    unfold Matrix.mulVec dotProduct
    simp [onesMatrix, onesVec, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hrow, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), sub_self]

theorem simplexGram_mulVec_ones (m : Nat) (hm : m ≠ 0) :
    Matrix.mulVec (simplexGram m) (onesVec m) = 0 := by
  rw [simplexGram, Matrix.smul_mulVec, centering_mulVec_ones m hm, smul_zero]

theorem simplexGram_row_sum (m : Nat) (hm : m ≠ 0) (i : Fin m) :
    ∑ j : Fin m, simplexGram m i j = 0 := by
  have h := congr_fun (simplexGram_mulVec_ones m hm) i
  unfold Matrix.mulVec dotProduct at h
  simpa [onesVec, mul_one] using h

/-- A configuration with Gram `simplexGram m` has vector barycenter zero. -/
theorem config_barycenter_of_simplexGram {m d : Nat} (X : Config m d)
    (hm : m ≠ 0) (hG : gram X = simplexGram m) :
    ∑ i, X i = 0 := by
  have hsq : ‖∑ i, X i‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [sum_inner Finset.univ (fun i => X i) (∑ j, X j)]
    simp_rw [inner_sum Finset.univ (fun j => X j), ← gram_apply]
    simp_rw [show ∀ i, ∑ j, gram X i j = 0 by
      intro i
      rw [hG]
      exact simplexGram_row_sum m hm i]
    simp
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

#print axioms gram_posSemidef
#print axioms gram_diagonal_unit
#print axioms orthoOrbit_refl
#print axioms orthoOrbit_symm
#print axioms orthoOrbit_trans
#print axioms gram_act
#print axioms gram_orthoOrbit
#print axioms gram_normalConfig
#print axioms unitConfig_normalConfig
#print axioms alpha_eq_one_sub_inv
#print axioms centering_apply_diag
#print axioms alpha_ne_zero_of_gt_one
#print axioms simplexGram_diagonal
#print axioms simplexGram_offDiag
#print axioms centering_mulVec_ones
#print axioms simplexGram_mulVec_ones
#print axioms simplexGram_row_sum
#print axioms config_barycenter_of_simplexGram

end SimplexFull.Geometry
