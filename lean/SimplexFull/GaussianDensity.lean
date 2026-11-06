import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Multivariate Gaussian density

Actual Lebesgue density on `EuclideanSpace ℝ (Fin m)`,
`ρ(R, x) = (√((2π)^m det R))⁻¹ exp(- xᵀ R⁻¹ x / 2)`.

This file does not assume Gaussian integral axioms. The value at the identity is the product of
one-dimensional standard Gaussian densities from `ProbabilityTheory.gaussianPDFReal`.
-/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators Real

namespace SimplexFull.Covariance

variable {m : ℕ}

/-- Quadratic form `xᵀ M x`, written as a coordinate sum so it matches `dot x (M * x)`. -/
def quad (M : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

lemma quad_eq_dotProduct (M : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    quad M x = (fun i => x i) ⬝ᵥ M.mulVec (fun i => x i) := by
  classical
  simp only [quad, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.mul_sum, mul_assoc]

lemma quad_zero (x : EuclideanSpace ℝ (Fin m)) : quad (0 : Matrix (Fin m) (Fin m) ℝ) x = 0 := by
  simp [quad]

lemma quad_add (M N : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    quad (M + N) x = quad M x + quad N x := by
  simp only [quad, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma quad_smul (c : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    quad (c • M) x = c * quad M x := by
  simp only [quad, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, x i * (c * M i j) * x j = c * (x i * M i j * x j) by intros; ring,
    ← Finset.mul_sum]

lemma quad_one (x : EuclideanSpace ℝ (Fin m)) :
    quad (1 : Matrix (Fin m) (Fin m) ℝ) x = ‖x‖ ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold quad
  simp only [Matrix.one_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j _ hji
    rw [if_neg hji.symm]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- On a field, the matrix inverse is `(det)⁻¹` times the adjugate, including the zero case. -/
lemma inv_eq_inv_det_smul_adjugate (R : Matrix (Fin m) (Fin m) ℝ) :
    R⁻¹ = (R.det)⁻¹ • R.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

lemma matrix_inv_one : (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ = 1 := by
  rw [inv_eq_inv_det_smul_adjugate, Matrix.det_one, Matrix.adjugate_one, inv_one, one_smul]

/-- Multivariate Gaussian density with covariance `R`.
`rho R x = (√((2π)^m det R))⁻¹ exp(-xᵀ R⁻¹ x / 2)`. -/
def rho (R : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ m * R.det))⁻¹ * Real.exp (-quad R⁻¹ x / 2)

lemma rho_eq_adjugate (R : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    rho R x =
      (Real.sqrt ((2 * Real.pi) ^ m * R.det))⁻¹ *
        Real.exp ((-(R.det⁻¹ * quad R.adjugate x)) / 2) := by
  rw [rho, inv_eq_inv_det_smul_adjugate, quad_smul]

theorem rho_of_det_nonpos {R : Matrix (Fin m) (Fin m) ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hR : R.det ≤ 0) : rho R x = 0 := by
  unfold rho
  have hmul : (2 * Real.pi) ^ m * R.det ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) _)
      hR
  rw [Real.sqrt_eq_zero_of_nonpos hmul, _root_.inv_zero, zero_mul]

theorem rho_pos {R : Matrix (Fin m) (Fin m) ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hR : 0 < R.det) : 0 < rho R x := by
  unfold rho
  have hbase : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hsqrt : 0 < Real.sqrt ((2 * Real.pi) ^ m * R.det) :=
    Real.sqrt_pos.2 (mul_pos (pow_pos hbase m) hR)
  exact mul_pos (inv_pos.2 hsqrt) (Real.exp_pos _)

theorem rho_one (x : EuclideanSpace ℝ (Fin m)) :
    rho (1 : Matrix (Fin m) (Fin m) ℝ) x =
      (Real.sqrt ((2 * Real.pi) ^ m))⁻¹ * Real.exp (-‖x‖ ^ 2 / 2) := by
  simp [rho, quad_one, Matrix.det_one]

/-- At the identity, the density is the product of standard one-dimensional Gaussian densities.
This pins the normalization to `ProbabilityTheory.gaussianPDFReal 0 1`. -/
theorem rho_one_eq_prod_gaussianPDFReal (x : EuclideanSpace ℝ (Fin m)) :
    rho (1 : Matrix (Fin m) (Fin m) ℝ) x =
      ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i) := by
  rw [rho_one, EuclideanSpace.real_norm_sq_eq]
  simp_rw [ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  have hpi : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_nonneg
  have hsqrt : Real.sqrt ((2 * Real.pi) ^ m) = Real.sqrt (2 * Real.pi) ^ m := by
    calc
      Real.sqrt ((2 * Real.pi) ^ m) = ((2 * Real.pi) ^ m) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      _ = ((2 * Real.pi) ^ (m : ℝ)) ^ (1 / 2 : ℝ) := by rw [Real.rpow_natCast]
      _ = (2 * Real.pi) ^ ((m : ℝ) * (1 / 2)) := by rw [← Real.rpow_mul hpi]
      _ = (2 * Real.pi) ^ ((1 / 2) * (m : ℝ)) := by
        congr 1
        exact mul_comm _ _
      _ = ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ (m : ℝ) := by rw [Real.rpow_mul hpi]
      _ = ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ m := by rw [Real.rpow_natCast]
      _ = Real.sqrt (2 * Real.pi) ^ m := by rw [← Real.sqrt_eq_rpow]
  have hexp : Real.exp (-(∑ i, (x i) ^ 2) / 2) = ∏ i, Real.exp (-(x i) ^ 2 / 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  rw [hsqrt, hexp, ← inv_pow, Finset.prod_mul_distrib]
  congr 1
  simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The identity density integrates to one against Lebesgue measure on Euclidean space. -/
theorem integral_rho_one :
    ∫ x : EuclideanSpace ℝ (Fin m), rho (1 : Matrix (Fin m) (Fin m) ℝ) x = 1 := by
  have hμ : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin m) → ℝ)) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm
  rw [← hμ.integral_comp' (rho (1 : Matrix (Fin m) (Fin m) ℝ))]
  have hprod : ∀ y : Fin m → ℝ,
      rho (1 : Matrix (Fin m) (Fin m) ℝ) (MeasurableEquiv.toLp 2 ((Fin m) → ℝ) y) =
        ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (y i) := by
    intro y
    rw [MeasurableEquiv.toLp_apply, rho_one_eq_prod_gaussianPDFReal]
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_pow (fun y : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 y)]
  rw [ProbabilityTheory.integral_gaussianPDFReal_eq_one (0 : ℝ) one_ne_zero, Fintype.card_fin,
    one_pow]

/-! ### Smoothness in the spatial variable -/

lemma contDiff_coord (i : Fin m) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin m) => x i) := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin m) => x i) =
      (fun y : Fin m → ℝ => y i) ∘ EuclideanSpace.equiv (Fin m) ℝ := by
    ext x
    rfl
  rw [hfun]
  exact (contDiff_apply (𝕜 := ℝ) (E := ℝ) i).comp
    (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap.contDiff

lemma contDiff_quad (M : Matrix (Fin m) (Fin m) ℝ) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin m) => quad M x) := by
  unfold quad
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact ((contDiff_coord i).mul contDiff_const).mul (contDiff_coord j)

/-- For each fixed covariance, the density is a smooth function of the Euclidean coordinate. -/
theorem contDiff_rho (R : Matrix (Fin m) (Fin m) ℝ) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin m) => rho R x) := by
  unfold rho
  exact contDiff_const.mul
    (ContDiff.exp <| (contDiff_quad R⁻¹).neg.div_const 2)

theorem continuous_rho (R : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin m) => rho R x) :=
  (contDiff_rho R).continuous

theorem differentiable_rho (R : Matrix (Fin m) (Fin m) ℝ) :
    Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin m) => rho R x) :=
  (contDiff_rho R).differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

/-! ### Smoothness along covariance lines, where the determinant is positive -/

lemma contDiff_line_entry (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    ContDiff ℝ ⊤ (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) i j) := by
  have hfun : (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) i j) =
      fun t => ((1 : Matrix (Fin m) (Fin m) ℝ) i j) + t * A i j := by
    ext t
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [hfun]
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

lemma contDiff_det_entries (f : Fin m → Fin m → ℝ → ℝ) (hf : ∀ i j, ContDiff ℝ ⊤ (f i j)) :
    ContDiff ℝ ⊤ (fun t : ℝ => (Matrix.of (fun i j => f i j t)).det) := by
  classical
  have hdet : (fun t : ℝ => (Matrix.of (fun i j => f i j t)).det) =
      fun t => ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, f (σ i) i t := by
    ext t
    simp [Matrix.det_apply, Matrix.of_apply]
  rw [hdet]
  refine ContDiff.sum fun σ _ => ?_
  have hsmul : (fun t : ℝ => Equiv.Perm.sign σ • ∏ i, f (σ i) i t) =
      fun t => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, f (σ i) i t := by
    ext t
    rw [Units.smul_def, zsmul_eq_mul]
  rw [hsmul]
  exact contDiff_const.mul (contDiff_prod fun i _ => hf (σ i) i)

lemma contDiff_det_line (A : Matrix (Fin m) (Fin m) ℝ) :
    ContDiff ℝ ⊤ (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det) := by
  have hdet : (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det) =
      fun t => (Matrix.of (fun i j => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) i j)).det := by
    ext t
    congr 1
  rw [hdet]
  exact contDiff_det_entries _ fun i j => contDiff_line_entry A i j

lemma contDiff_updateRow_entry (A : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) (v : Fin m → ℝ)
    (p q : Fin m) :
    ContDiff ℝ ⊤ (fun t : ℝ => (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).updateRow j v) p q) := by
  by_cases hp : p = j
  · have hfun : (fun t : ℝ =>
        (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).updateRow j v) p q) = fun _ => v q := by
      ext t
      simp [Matrix.updateRow_apply, hp]
    rw [hfun]
    exact contDiff_const
  · have hfun : (fun t : ℝ =>
        (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).updateRow j v) p q) =
        fun t => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) p q := by
      ext t
      simp [Matrix.updateRow_apply, hp]
    rw [hfun]
    exact contDiff_line_entry A p q

lemma contDiff_adjugate_entry (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    ContDiff ℝ ⊤ (fun t : ℝ => (adjugate ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)) i j) := by
  simp_rw [Matrix.adjugate_apply]
  have hdet : (fun t : ℝ =>
        (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).updateRow j (Pi.single i (1 : ℝ))).det) =
      fun t => (Matrix.of (fun p q =>
        (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).updateRow j (Pi.single i (1 : ℝ))) p q)).det := by
    ext t
    congr 1
  rw [hdet]
  exact contDiff_det_entries _
    fun p q => contDiff_updateRow_entry A j (Pi.single i (1 : ℝ)) p q

lemma contDiff_adjQuad (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ ⊤ (fun t : ℝ => quad (adjugate ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)) x) := by
  unfold quad
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_const.mul (contDiff_adjugate_entry A i j)).mul contDiff_const

lemma contDiffAt_rho_line_expr (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m))
    {t0 : ℝ} (hdet : 0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det) :
    ContDiffAt ℝ ⊤ (fun t : ℝ =>
      (Real.sqrt ((2 * Real.pi) ^ m * ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det))⁻¹ *
        Real.exp ((-(((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det⁻¹ *
          quad (adjugate ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)) x)) / 2)) t0 := by
  have hbase : (2 * Real.pi) ^ m ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hdet_ne : ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det ≠ 0 := ne_of_gt hdet
  have harg_ne : (2 * Real.pi) ^ m * ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det ≠ 0 :=
    mul_ne_zero hbase hdet_ne
  have hsqrt_ne : Real.sqrt ((2 * Real.pi) ^ m * ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det) ≠ 0 := by
    refine (Real.sqrt_pos.2 ?_).ne'
    exact mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) m) hdet
  refine ContDiffAt.mul ?_ ?_
  · exact ((contDiff_const.mul (contDiff_det_line A)).contDiffAt.sqrt harg_ne).inv hsqrt_ne
  · exact ContDiffAt.exp <|
      (((contDiff_det_line A).contDiffAt.inv hdet_ne).mul (contDiff_adjQuad A x).contDiffAt).neg.div_const
        2

/-- Along any matrix line `t ↦ I + tA`, the density is `C^∞` at parameters whose determinant is
positive. That is the open set on which `I + tA` is invertible and the Gaussian prefactor is smooth. -/
theorem contDiffAt_rho_line (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) {t0 : ℝ}
    (hdet : 0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det) :
    ContDiffAt ℝ ⊤ (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) t0 := by
  have heq : (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) =
      fun t =>
        (Real.sqrt ((2 * Real.pi) ^ m * ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det))⁻¹ *
          Real.exp ((-(((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det⁻¹ *
            quad (adjugate ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)) x)) / 2) := by
    ext t
    simpa using rho_eq_adjugate ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x
  rw [heq]
  exact contDiffAt_rho_line_expr A x hdet

theorem differentiableAt_rho_line (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m))
    {t0 : ℝ} (hdet : 0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det) :
    DifferentiableAt ℝ (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) t0 :=
  (contDiffAt_rho_line A x hdet).differentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

theorem continuousAt_rho_line (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m))
    {t0 : ℝ} (hdet : 0 < ((1 : Matrix (Fin m) (Fin m) ℝ) + t0 • A).det) :
    ContinuousAt (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) t0 :=
  (contDiffAt_rho_line A x hdet).continuousAt

/-- The identity has determinant one, so every covariance line is smooth at `t = 0`. -/
theorem contDiffAt_rho_line_zero (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ContDiffAt ℝ ⊤ (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x) 0 := by
  refine contDiffAt_rho_line A x ?_
  simp [Matrix.det_one]

end SimplexFull.Covariance
