import SimplexFull.Shell
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.End
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Permutation stationarity for the square-root shell chart.

The linear-functional lemma is the orbit computation: a linear form invariant under
`A.submatrix σ σ` for every `σ : Equiv.Perm (Fin m)` vanishes on zero-diagonal matrices
whose entries sum to zero, for `m ≥ 2`. Chart equivariance and the Fréchet derivative
of a conjugation-invariant loss are proved afterwards. The linear lemma is not that
stationarity theorem.
-/

set_option maxHeartbeats 1600000

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace SimplexFull.Geometry.Symmetry

open SimplexFull.Geometry Matrix

variable {m : ℕ}

lemma submatrix_add_apply (A B : ShapeMatrix m) (σ : Equiv.Perm (Fin m)) :
    (A + B).submatrix σ σ = A.submatrix σ σ + B.submatrix σ σ := by
  ext i j
  simp [submatrix_apply, Matrix.add_apply]

lemma submatrix_sub_apply (A B : ShapeMatrix m) (σ : Equiv.Perm (Fin m)) :
    (A - B).submatrix σ σ = A.submatrix σ σ - B.submatrix σ σ := by
  ext i j
  simp [submatrix_apply, Matrix.sub_apply]

lemma submatrix_smul_apply (c : ℝ) (A : ShapeMatrix m) (σ : Equiv.Perm (Fin m)) :
    (c • A).submatrix σ σ = c • A.submatrix σ σ := by
  ext i j
  simp [submatrix_apply, Matrix.smul_apply]

lemma submatrix_mul_perm (A B : ShapeMatrix m) (σ : Equiv.Perm (Fin m)) :
    (A * B).submatrix σ σ = A.submatrix σ σ * B.submatrix σ σ :=
  (submatrix_mul_equiv A B σ σ σ).symm

lemma submatrix_zero_apply (σ : Equiv.Perm (Fin m)) :
    (0 : ShapeMatrix m).submatrix σ σ = 0 := by
  ext i j
  simp [submatrix_apply]

lemma submatrix_onesMatrix (σ : Equiv.Perm (Fin m)) :
    (onesMatrix m).submatrix σ σ = onesMatrix m := by
  ext i j
  simp [onesMatrix, submatrix_apply]

lemma submatrix_centering (σ : Equiv.Perm (Fin m)) :
    (centering m).submatrix σ σ = centering m := by
  ext i j
  simp only [submatrix_apply, centering, onesMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_one, σ.apply_eq_iff_eq]

lemma submatrix_shellLift (σ : Equiv.Perm (Fin m)) (C : ShapeMatrix m) :
    (shellLift C).submatrix σ σ = shellLift (C.submatrix σ σ) := by
  ext i j
  simp [shellLift, submatrix_apply]

/-- Two swaps carry any ordered pair of distinct indices to any other. -/
lemma exists_perm_send_distinct_pair {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin m), σ a = c ∧ σ b = d := by
  let τ : Equiv.Perm (Fin m) := Equiv.swap a c
  let b' : Fin m := τ b
  refine ⟨Equiv.swap b' d * τ, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply]
    have hta : τ a = c := Equiv.swap_apply_left a c
    rw [hta]
    have hb'c : b' ≠ c := by
      intro h
      apply hab
      apply τ.injective
      rw [show τ b = c from h, hta]
    rw [Equiv.swap_apply_of_ne_of_ne hb'c.symm hcd]
  · rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left b' d

lemma linearMap_eq_sum_single (L : ShapeMatrix m →ₗ[ℝ] ℝ) (A : ShapeMatrix m) :
    L A = ∑ i, ∑ j, A i j * L (single i j (1 : ℝ)) := by
  refine (congr_arg L (matrix_eq_sum_single A)).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : single i j (A i j) = A i j • single i j (1 : ℝ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, smul_eq_mul]

/-- `L (single i j 1)` depends only on whether the index pair is diagonal. -/
theorem invariantLinear_single_offDiag
    (L : ShapeMatrix m →ₗ[ℝ] ℝ)
    (hL : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m, L (A.submatrix σ σ) = L A)
    {i j p q : Fin m} (hij : i ≠ j) (hpq : p ≠ q) :
    L (single i j (1 : ℝ)) = L (single p q (1 : ℝ)) := by
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_send_distinct_pair hij hpq
  have hsub := submatrix_single_equiv σ σ p q (1 : ℝ)
  have hσp : σ.symm p = i := by rw [← hσi, Equiv.symm_apply_apply]
  have hσq : σ.symm q = j := by rw [← hσj, Equiv.symm_apply_apply]
  rw [hσp, hσq] at hsub
  have hL' := hL σ (single p q (1 : ℝ))
  rw [hsub] at hL'
  exact hL'

theorem invariantLinear_single_diag
    (L : ShapeMatrix m →ₗ[ℝ] ℝ)
    (hL : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m, L (A.submatrix σ σ) = L A)
    (i k : Fin m) :
    L (single i i (1 : ℝ)) = L (single k k (1 : ℝ)) := by
  let σ : Equiv.Perm (Fin m) := Equiv.swap i k
  have hsub := submatrix_single_equiv σ σ k k (1 : ℝ)
  have hk : σ.symm k = i := by rw [Equiv.symm_swap, Equiv.swap_apply_right]
  rw [hk] at hsub
  have hL' := hL σ (single k k (1 : ℝ))
  rw [hsub] at hL'
  exact hL'

/-- On a zero-diagonal matrix the invariant form is the off-diagonal value times the entry sum. -/
theorem invariantLinear_eq_mul_entrySum_of_zeroDiagonal
    (hm : 2 ≤ m)
    (L : ShapeMatrix m →ₗ[ℝ] ℝ)
    (hL : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m, L (A.submatrix σ σ) = L A)
    {A : ShapeMatrix m} (hA : zeroDiagonal A) :
    ∃ b : ℝ, L A = b * entrySum A := by
  let i0 : Fin m := ⟨0, by omega⟩
  let j0 : Fin m := ⟨1, by omega⟩
  have hne : i0 ≠ j0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, j0] at hv
  let b : ℝ := L (single i0 j0 (1 : ℝ))
  refine ⟨b, ?_⟩
  rw [entrySum, linearMap_eq_sum_single L A]
  have hterm : ∀ i j, A i j * L (single i j (1 : ℝ)) = A i j * b := by
    intro i j
    by_cases hij : i = j
    · rw [hij, hA j, zero_mul, zero_mul]
    · rw [invariantLinear_single_offDiag L hL hij hne]
  simp_rw [hterm, ← Finset.sum_mul]
  rw [mul_comm]

theorem invariantLinear_vanishes_of_zeroDiagonal_entrySum
    (hm : 2 ≤ m)
    (L : ShapeMatrix m →ₗ[ℝ] ℝ)
    (hL : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m, L (A.submatrix σ σ) = L A)
    {A : ShapeMatrix m} (hA : zeroDiagonal A) (hsum : entrySum A = 0) :
    L A = 0 := by
  obtain ⟨b, hb⟩ := invariantLinear_eq_mul_entrySum_of_zeroDiagonal hm L hL hA
  rw [hb, hsum, mul_zero]

theorem squareShellC_submatrix (tau : ℝ) (D : ShapeMatrix m) (σ : Equiv.Perm (Fin m)) :
    (squareShellC m tau D).submatrix σ σ = squareShellC m tau (D.submatrix σ σ) := by
  unfold squareShellC
  rw [submatrix_sub_apply, submatrix_mul_perm, submatrix_add_apply, submatrix_smul_apply,
    submatrix_centering]

theorem shellCovariance_submatrix (tau : ℝ) (D : ShapeMatrix m) (σ : Equiv.Perm (Fin m)) :
    (shellCovariance m tau D).submatrix σ σ = shellCovariance m tau (D.submatrix σ σ) := by
  unfold shellCovariance
  rw [submatrix_add_apply, submatrix_one_equiv, submatrix_shellLift, squareShellC_submatrix]

theorem shellCovariance_zero_submatrix (tau : ℝ) (σ : Equiv.Perm (Fin m)) :
    (shellCovariance m tau 0).submatrix σ σ = shellCovariance m tau 0 := by
  rw [shellCovariance_submatrix, submatrix_zero_apply]

lemma centering_idempotent (hm : m ≠ 0) : centering m * centering m = centering m := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [centering]
  set c : ℝ := (m : ℝ)⁻¹
  have hc : c * (m : ℝ) = 1 := inv_mul_cancel₀ hmR
  have hJ : onesMatrix m * onesMatrix m = (m : ℝ) • onesMatrix m := onesMatrix_mul_self m
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
          rw [hcc, Matrix.smul_mul, mul_one]
    _ = (1 - c • onesMatrix m) -
          (c • onesMatrix m - (c * c * (m : ℝ)) • onesMatrix m) := by
          rw [hJ, smul_smul]
    _ = (1 - c • onesMatrix m) - (c • onesMatrix m - c • onesMatrix m) := by
          rw [show c * c * (m : ℝ) = c by rw [mul_assoc, hc, mul_one]]
    _ = 1 - c • onesMatrix m := by
          simp

lemma mul_square_expand (A B : ShapeMatrix m) :
    (A + B) * (A + B) = A * A + A * B + B * A + B * B := by
  rw [mul_add, add_mul, add_mul]
  rw [add_assoc, add_left_comm (B * A) (A * B) (B * B), ← add_assoc, ← add_assoc]

lemma smul_mul_smul_matrix (a b : ℝ) (A B : ShapeMatrix m) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma shellLift_eq_uncompress (C : ShapeMatrix m) : shellLift C = uncompress C := rfl

lemma shellLift_add (A B : ShapeMatrix m) : shellLift (A + B) = shellLift A + shellLift B :=
  (shellLiftLinear m).map_add A B

lemma shellLift_smul (c : ℝ) (A : ShapeMatrix m) : shellLift (c • A) = c • shellLift A :=
  (shellLiftLinear m).map_smul c A

lemma squareShellC_ray (hm : m ≠ 0) (tau : ℝ) {H : ShapeMatrix m}
    (hPH : centering m * H = H) (hHP : H * centering m = H) (t : ℝ) :
    squareShellC m tau (t • H) =
      (chartKappa m tau ^ 2 - 1) • centering m +
        (2 * chartKappa m tau * t) • H +
        (t ^ 2) • (H * H) := by
  have hPP : centering m * centering m = centering m := centering_idempotent hm
  set κ : ℝ := chartKappa m tau
  set P : ShapeMatrix m := centering m
  unfold squareShellC
  rw [mul_square_expand, smul_mul_smul_matrix, smul_mul_smul_matrix, smul_mul_smul_matrix,
    smul_mul_smul_matrix, hPP, hPH, hHP]
  have hcross : (κ * t) • H + (t * κ) • H = (2 * κ * t) • H := by
    rw [← add_smul]
    congr 1
    ring
  rw [add_assoc ((κ * κ) • P), hcross, ← pow_two, ← pow_two]
  have hP : (κ ^ 2) • P - P = (κ ^ 2 - 1) • P := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  calc
    (κ ^ 2) • P + (2 * κ * t) • H + (t ^ 2) • (H * H) - P
        = ((κ ^ 2) • P - P) + (2 * κ * t) • H + (t ^ 2) • (H * H) := by
          abel
    _ = (κ ^ 2 - 1) • P + (2 * κ * t) • H + (t ^ 2) • (H * H) := by
          rw [hP]

/-- Along a shell ray the covariance is affine in `t` at first order:
the linear term is `(2 κ) • uncompress H`. -/
theorem shellCovariance_ray (hm : m ≠ 0) (tau : ℝ) {H : ShapeMatrix m}
    (hPH : centering m * H = H) (hHP : H * centering m = H) (t : ℝ) :
    shellCovariance m tau (t • H) =
      shellCovariance m tau 0 +
        t • ((2 * chartKappa m tau) • uncompress H) +
        (t ^ 2) • uncompress (H * H) := by
  set κ : ℝ := chartKappa m tau
  set P : ShapeMatrix m := centering m
  have hsq := squareShellC_ray hm tau hPH hHP t
  have hsq0 : squareShellC m tau 0 = (κ ^ 2 - 1) • P := by
    simpa [zero_smul, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (squareShellC_ray hm tau hPH hHP 0)
  have hsplit : shellLift ((κ ^ 2 - 1) • P + (2 * κ * t) • H + (t ^ 2) • (H * H)) =
      (κ ^ 2 - 1) • shellLift P + (2 * κ * t) • shellLift H + (t ^ 2) • shellLift (H * H) := by
    rw [shellLift_add, shellLift_add, shellLift_smul, shellLift_smul, shellLift_smul]
  have hconst : shellLift ((κ ^ 2 - 1) • P) = (κ ^ 2 - 1) • shellLift P :=
    shellLift_smul (κ ^ 2 - 1) P
  have hscale : (2 * κ * t) • shellLift H = t • ((2 * κ) • shellLift H) := by
    rw [show 2 * κ * t = t * (2 * κ) by ring, ← smul_smul]
  calc
    shellCovariance m tau (t • H)
        = 1 + shellLift (squareShellC m tau (t • H)) := by
          rw [shellCovariance]
    _ = 1 + shellLift ((κ ^ 2 - 1) • P + (2 * κ * t) • H + (t ^ 2) • (H * H)) := by
          rw [hsq]
    _ = 1 + ((κ ^ 2 - 1) • shellLift P + (2 * κ * t) • shellLift H +
          (t ^ 2) • shellLift (H * H)) := by
          rw [hsplit]
    _ = (1 + (κ ^ 2 - 1) • shellLift P) + (2 * κ * t) • shellLift H +
          (t ^ 2) • shellLift (H * H) := by
          abel
    _ = (1 + shellLift ((κ ^ 2 - 1) • P)) + t • ((2 * κ) • shellLift H) +
          (t ^ 2) • shellLift (H * H) := by
          rw [← hconst, hscale]
    _ = shellCovariance m tau 0 + t • ((2 * κ) • shellLift H) +
          (t ^ 2) • shellLift (H * H) := by
          rw [shellCovariance, hsq0]
    _ = shellCovariance m tau 0 + t • ((2 * κ) • uncompress H) +
          (t ^ 2) • uncompress (H * H) := by
          rw [shellLift_eq_uncompress, shellLift_eq_uncompress]

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

theorem entrySum_uncompress_shell (hm : m ≠ 0) (H : shellSpace m) :
    entrySum (uncompress (H : ShapeMatrix m)) = 0 := by
  have hmem : (H : ShapeMatrix m).transpose = (H : ShapeMatrix m) ∧
      centering m * (H : ShapeMatrix m) = (H : ShapeMatrix m) ∧
      (H : ShapeMatrix m) * centering m = (H : ShapeMatrix m) ∧
      Matrix.trace (H : ShapeMatrix m) = 0 := by
    simpa [shellSpace, Set.mem_setOf] using H.property
  obtain ⟨_, hPH, hHP, htr⟩ := hmem
  rw [entrySum_uncompress_of_centered (shell_centered hm hPH hHP), htr]
  ring

lemma differentiable_squareShellC (tau : ℝ) :
    Differentiable ℝ (fun D : ShapeMatrix m => squareShellC m tau D) := by
  unfold squareShellC
  fun_prop

lemma differentiable_shellCovariance (tau : ℝ) :
    Differentiable ℝ (fun D : ShapeMatrix m => shellCovariance m tau D) := by
  have hlift : Differentiable ℝ (fun D : ShapeMatrix m => shellLift (squareShellC m tau D)) :=
    (LinearMap.toContinuousLinearMap (shellLiftLinear m)).differentiable.comp
      (differentiable_squareShellC tau)
  have hconst : Differentiable ℝ (fun _ : ShapeMatrix m => (1 : ShapeMatrix m)) :=
    differentiable_const (1 : ShapeMatrix m)
  simpa [shellCovariance] using hconst.add hlift

lemma hasDerivAt_quadratic_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y V W : E) :
    HasDerivAt (fun t : ℝ => Y + t • V + (t ^ 2) • W) V 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => Y) (0 : E) 0 := hasDerivAt_const 0 Y
  have hlin0 : HasDerivAt (fun t : ℝ => t • V) ((1 : ℝ) • V) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const V
  have hlin : HasDerivAt (fun t : ℝ => t • V) V 0 := by
    simpa using hlin0
  have hpow0 : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℝ) * (0 : ℝ) ^ (2 - 1)) 0 :=
    hasDerivAt_pow 2 0
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using hpow0
  have hquad0 : HasDerivAt (fun t : ℝ => (t ^ 2) • W) ((0 : ℝ) • W) 0 :=
    hpow.smul_const W
  have hquad : HasDerivAt (fun t : ℝ => (t ^ 2) • W) 0 0 := by
    simpa using hquad0
  have hsum0 : HasDerivAt (fun t : ℝ => Y + t • V) ((0 : E) + V) 0 :=
    hconst.add hlin
  have hsum : HasDerivAt (fun t : ℝ => Y + t • V) V 0 := by
    simpa using hsum0
  have htotal : HasDerivAt (fun t : ℝ => Y + t • V + (t ^ 2) • W) (V + (0 : E)) 0 :=
    hsum.add hquad
  simpa using htotal

def submatrixLinear (σ : Equiv.Perm (Fin m)) : ShapeMatrix m →ₗ[ℝ] ShapeMatrix m where
  toFun A := A.submatrix σ σ
  map_add' A B := submatrix_add_apply A B σ
  map_smul' c A := by
    ext i j
    simp [submatrix_apply, Matrix.smul_apply, smul_eq_mul]

lemma fderiv_submatrix_invariant {Y : ShapeMatrix m} (loss : ShapeMatrix m → ℝ)
    (hloss_inv : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m,
      loss (A.submatrix σ σ) = loss A)
    (hloss : DifferentiableAt ℝ loss Y)
    (hY : ∀ σ : Equiv.Perm (Fin m), Y.submatrix σ σ = Y)
    (σ : Equiv.Perm (Fin m)) (V : ShapeMatrix m) :
    (fderiv ℝ loss Y) (V.submatrix σ σ) = (fderiv ℝ loss Y) V := by
  let c : ShapeMatrix m →ₗ[ℝ] ShapeMatrix m := submatrixLinear σ
  let cL : ShapeMatrix m →L[ℝ] ShapeMatrix m := LinearMap.toContinuousLinearMap c
  have hc_apply : ∀ A, cL A = A.submatrix σ σ := by
    intro A
    simp [cL, c, submatrixLinear, LinearMap.coe_toContinuousLinearMap']
  have hcY : cL Y = Y := by rw [hc_apply, hY σ]
  have hfeq : loss ∘ (⇑cL) = loss := by
    funext A
    rw [Function.comp_apply, hc_apply]
    exact hloss_inv σ A
  have hcomp : fderiv ℝ (loss ∘ (⇑cL)) Y =
      (fderiv ℝ loss (cL Y)).comp (fderiv ℝ (⇑cL) Y) :=
    fderiv_comp Y (by rw [hcY]; exact hloss) cL.differentiableAt
  rw [hfeq, hcY, cL.fderiv] at hcomp
  have happ : (fderiv ℝ loss Y) V = (fderiv ℝ loss Y) (cL V) := by
    have happly := congr_arg (fun T : ShapeMatrix m →L[ℝ] ℝ => T V) hcomp
    simpa [ContinuousLinearMap.comp_apply] using happly
  rw [← hc_apply V]
  exact happ.symm

/-- A differentiable real loss invariant under `A.submatrix σ σ` has vanishing derivative,
at `D = 0` and at every `tau`, along every direction in `shellSpace`. -/
theorem loss_fderiv_shellCovariance_vanishes
    (hm : 2 ≤ m) (tau : ℝ) (loss : ShapeMatrix m → ℝ)
    (hloss_inv : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m,
      loss (A.submatrix σ σ) = loss A)
    (hloss : DifferentiableAt ℝ loss (shellCovariance m tau 0))
    (H : shellSpace m) :
    (fderiv ℝ (fun D : ShapeMatrix m => loss (shellCovariance m tau D)) 0)
        (H : ShapeMatrix m) = 0 := by
  have hm0 : m ≠ 0 := by omega
  set Hmat : ShapeMatrix m := (H : ShapeMatrix m)
  have hmem : Hmat.transpose = Hmat ∧ centering m * Hmat = Hmat ∧
      Hmat * centering m = Hmat ∧ Matrix.trace Hmat = 0 := by
    simpa [shellSpace, Set.mem_setOf, Hmat] using H.property
  obtain ⟨_, hPH, hHP, _⟩ := hmem
  set Y : ShapeMatrix m := shellCovariance m tau 0
  set κ : ℝ := chartKappa m tau
  set V : ShapeMatrix m := (2 * κ) • uncompress Hmat
  set W : ShapeMatrix m := uncompress (Hmat * Hmat)
  have hpath : ∀ t : ℝ, shellCovariance m tau (t • Hmat) = Y + t • V + (t ^ 2) • W := by
    intro t
    simpa [Y, V, W, κ] using shellCovariance_ray hm0 tau hPH hHP t
  have hcurve : HasDerivAt (fun t : ℝ => shellCovariance m tau (t • Hmat)) V 0 := by
    have hEq : (fun t : ℝ => shellCovariance m tau (t • Hmat)) =
        fun t : ℝ => Y + t • V + (t ^ 2) • W := by
      funext t
      exact hpath t
    rw [hEq]
    exact hasDerivAt_quadratic_ray Y V W
  have hpoint : Y = shellCovariance m tau ((0 : ℝ) • Hmat) := by
    rw [zero_smul]
  have hloss_path : HasDerivAt (fun t : ℝ => loss (shellCovariance m tau (t • Hmat)))
      ((fderiv ℝ loss Y) V) 0 :=
    hloss.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve hpoint
  have hLinv : ∀ σ : Equiv.Perm (Fin m), ∀ A : ShapeMatrix m,
      ((fderiv ℝ loss Y).toLinearMap) (A.submatrix σ σ) =
        ((fderiv ℝ loss Y).toLinearMap) A := by
    intro σ A
    simpa using fderiv_submatrix_invariant loss hloss_inv hloss
      (fun σ' => shellCovariance_zero_submatrix tau σ') σ A
  have hLU : ((fderiv ℝ loss Y).toLinearMap) (uncompress Hmat) = 0 :=
    invariantLinear_vanishes_of_zeroDiagonal_entrySum hm (fderiv ℝ loss Y).toLinearMap hLinv
      (uncompress_zeroDiagonal Hmat) (entrySum_uncompress_shell hm0 H)
  have hV : (fderiv ℝ loss Y) V = 0 := by
    have hsmul := (fderiv ℝ loss Y).map_smul (2 * κ) (uncompress Hmat)
    rw [hsmul]
    have happly : (fderiv ℝ loss Y) (uncompress Hmat) = 0 := by
      simpa using hLU
    rw [happly, smul_zero]
  rw [hV] at hloss_path
  have hcov : DifferentiableAt ℝ (fun D : ShapeMatrix m => shellCovariance m tau D) 0 :=
    (differentiable_shellCovariance tau).differentiableAt
  have hφ : DifferentiableAt ℝ (fun D : ShapeMatrix m => loss (shellCovariance m tau D)) 0 :=
    DifferentiableAt.fun_comp' 0 hloss hcov
  have hscale : HasDerivAt (fun t : ℝ => t • Hmat) Hmat 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Hmat
  have hbase : (0 : ShapeMatrix m) = (0 : ℝ) • Hmat := by
    rw [zero_smul]
  have hφ_path : HasDerivAt (fun t : ℝ => loss (shellCovariance m tau (t • Hmat)))
      ((fderiv ℝ (fun D : ShapeMatrix m => loss (shellCovariance m tau D)) 0) Hmat) 0 :=
    hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hscale hbase
  exact hφ_path.unique hloss_path

#print axioms invariantLinear_single_offDiag
#print axioms invariantLinear_single_diag
#print axioms invariantLinear_eq_mul_entrySum_of_zeroDiagonal
#print axioms invariantLinear_vanishes_of_zeroDiagonal_entrySum
#print axioms squareShellC_submatrix
#print axioms shellCovariance_submatrix
#print axioms shellCovariance_ray
#print axioms entrySum_uncompress_shell
#print axioms loss_fderiv_shellCovariance_vanishes

end SimplexFull.Geometry.Symmetry
