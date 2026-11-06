import SimplexFull.GeometryBase
import SimplexFull.GramCoordinates
import SimplexFull.SquareShellAlgebra
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option maxHeartbeats 400000
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry

abbrev ShapeMatrix (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

def chartKappa (m : ℕ) (tau : ℝ) : ℝ := 1 - tau / (2 * (m : ℝ))

def squareShellC (m : ℕ) (tau : ℝ) (D : ShapeMatrix m) : ShapeMatrix m :=
  (chartKappa m tau • centering m + D) *
    (chartKappa m tau • centering m + D) - centering m

def shellLift {m : ℕ} (C : ShapeMatrix m) : ShapeMatrix m :=
  fun i j => C i j - (C i i + C j j) / 2

def shellLiftLinear (m : ℕ) : ShapeMatrix m →ₗ[ℝ] ShapeMatrix m where
  toFun := shellLift
  map_add' := by
    intro A B
    ext i j
    simp only [shellLift, Matrix.add_apply]
    ring
  map_smul' := by
    intro c A
    ext i j
    simp only [shellLift, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def shellCovariance (m : ℕ) (tau : ℝ) (D : ShapeMatrix m) : ShapeMatrix m :=
  1 + shellLift (squareShellC m tau D)

@[simp] theorem shellLift_diag {m : ℕ} (C : ShapeMatrix m) (i : Fin m) :
    shellLift C i i = 0 := by
  dsimp [shellLift]
  ring

@[simp] theorem shellCovariance_diag (m : ℕ) (tau : ℝ) (D : ShapeMatrix m)
    (i : Fin m) : shellCovariance m tau D i i = 1 := by
  simp [shellCovariance]

theorem contDiff_chartKappa (m : ℕ) : ContDiff ℝ ⊤ (chartKappa m) := by
  unfold chartKappa
  fun_prop

theorem contDiff_squareShellC (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ShapeMatrix m => squareShellC m p.1 p.2) := by
  unfold squareShellC chartKappa
  fun_prop

theorem contDiff_shellLift (m : ℕ) : ContDiff ℝ ⊤ (@shellLift m) :=
  (LinearMap.toContinuousLinearMap (shellLiftLinear m)).contDiff
theorem contDiff_shellCovariance (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ShapeMatrix m => shellCovariance m p.1 p.2) := by
  unfold shellCovariance
  exact contDiff_const.add ((contDiff_shellLift m).comp (contDiff_squareShellC m))

#print axioms contDiff_squareShellC
#print axioms contDiff_shellCovariance
@[irreducible] def shellSpace (m : ℕ) : Submodule ℝ (ShapeMatrix m) where
  carrier := {D | D.transpose = D ∧ centering m * D = D ∧
    D * centering m = D ∧ Matrix.trace D = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro A B ⟨hAt, hAP, hPA, htrA⟩ ⟨hBt, hBP, hPB, htrB⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Matrix.transpose_add, hAt, hBt]
    · rw [mul_add, hAP, hBP]
    · rw [add_mul, hPA, hPB]
    · rw [Matrix.trace_add, htrA, htrB, add_zero]
  smul_mem' := by
    rintro c D ⟨hDt, hPD, hDP, htr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Matrix.transpose_smul, hDt]
    · rw [Matrix.mul_smul, hPD]
    · rw [Matrix.smul_mul, hDP]
    · rw [Matrix.trace_smul, htr, smul_zero]

def shellCovarianceOnSpace (m : ℕ) (tau : ℝ) (D : shellSpace m) : ShapeMatrix m :=
  shellCovariance m tau D

end SimplexFull.Geometry