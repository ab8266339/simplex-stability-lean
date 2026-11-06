import SimplexFull.SecondChain
import SimplexFull.ShellObjective
import SimplexFull.ShellSymmetry

/-!
Square-chart Hessian of `shellLoss`.

At `tau = 0`, `shellCovariance_ray` is the quadratic path
`I + (2 t) • uncompress D + t² • uncompress (D * D)`. The scalar second derivative
of `shellLoss` along `(0, t • D)` is the Fréchet Hessian at `(0, 0)` in the direction
`(0, D)`, and the same scalar is the extended-loss second derivative along that path.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator Topology

namespace SimplexFull.Geometry

variable {m : ℕ} [NeZero m]

local instance : NormedAddCommGroup (ShapeMatrix m →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (ShapeMatrix m →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (ShapeMatrix m →L[ℝ] (ShapeMatrix m →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (ShapeMatrix m →L[ℝ] (ShapeMatrix m →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((ℝ × shellSpace m) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ ((ℝ × shellSpace m) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup
    ((ℝ × shellSpace m) →L[ℝ] ((ℝ × shellSpace m) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ
    ((ℝ × shellSpace m) →L[ℝ] ((ℝ × shellSpace m) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

theorem shellCovarianceOnSpace_zero_ray (D : shellSpace m) (t : ℝ) :
    shellCovarianceOnSpace m 0 (t • D) =
      1 + (2 * t) • uncompress (D : ShapeMatrix m) +
        (t ^ 2) • uncompress ((D : ShapeMatrix m) * (D : ShapeMatrix m)) := by
  have hmem : (D : ShapeMatrix m) ∈ shellSpace m := D.property
  delta shellSpace at hmem
  have hfacts : (D : ShapeMatrix m).transpose = (D : ShapeMatrix m) ∧
      centering m * (D : ShapeMatrix m) = (D : ShapeMatrix m) ∧
      (D : ShapeMatrix m) * centering m = (D : ShapeMatrix m) ∧
      Matrix.trace (D : ShapeMatrix m) = 0 := by
    simpa [Set.mem_setOf] using hmem
  have hPD : centering m * (D : ShapeMatrix m) = D := hfacts.2.1
  have hDP : (D : ShapeMatrix m) * centering m = D := hfacts.2.2.1
  have hcoe : ((t • D : shellSpace m) : ShapeMatrix m) = t • (D : ShapeMatrix m) :=
    Submodule.coe_smul t D
  have hray := Symmetry.shellCovariance_ray (NeZero.ne m) (0 : ℝ) hPD hDP t
  have hκ : chartKappa m 0 = 1 := by simp [chartKappa]
  rw [shellCovarianceOnSpace, hcoe, hray, shellCovariance_zero, hκ]
  simp only [mul_one]
  have hcoeff : t • ((2 : ℝ) • uncompress (D : ShapeMatrix m)) =
      (2 * t) • uncompress (D : ShapeMatrix m) := by
    rw [smul_smul]
    congr 1
    ring
  rw [hcoeff]

/-- Fréchet Hessian of `shellLoss` at `(0, 0)` on the vertical vector `(0, D)`. -/
theorem shellLoss_hessian_sqChart (mu : ℝ) (D : shellSpace m) :
    (fderiv ℝ (fderiv ℝ (shellLoss (m := m) mu)) ((0 : ℝ), (0 : shellSpace m)) ((0 : ℝ), D))
        ((0 : ℝ), D) =
      4 * ((fderiv ℝ (fderiv ℝ (extendedLoss (m := m) mu)) (1 : ShapeMatrix m)
            (uncompress (D : ShapeMatrix m)))
          (uncompress (D : ShapeMatrix m))) +
        2 * ((fderiv ℝ (extendedLoss (m := m) mu) (1 : ShapeMatrix m))
          (uncompress ((D : ShapeMatrix m) * (D : ShapeMatrix m)))) := by
  set B : ShapeMatrix m := uncompress (D : ShapeMatrix m)
  set C : ShapeMatrix m := uncompress ((D : ShapeMatrix m) * (D : ShapeMatrix m))
  have hzero : (0 : ℝ × shellSpace m) = ((0 : ℝ), (0 : shellSpace m)) := by
    ext <;> simp
  have hS : ContDiffAt ℝ 2 (shellLoss (m := m) mu) ((0 : ℝ), (0 : shellSpace m)) := by
    rw [← hzero]
    exact contDiffAt_shellLoss_zero (m := m) mu
  have hline := secondDeriv_line (f := shellLoss (m := m) mu)
    (x := ((0 : ℝ), (0 : shellSpace m))) (v := ((0 : ℝ), D)) hS
  have hquad := secondDeriv_quadPath (f := extendedLoss (m := m) mu)
    (x := (1 : ShapeMatrix m)) (B := B) (C := C) (contDiffAt_extendedLoss_one (m := m) mu)
  have hfun : (fun t : ℝ =>
        shellLoss (m := m) mu (((0 : ℝ), (0 : shellSpace m)) + t • ((0 : ℝ), D))) =
      fun t : ℝ => extendedLoss (m := m) mu (1 + (2 * t) • B + (t ^ 2) • C) := by
    funext t
    have harg : ((0 : ℝ), (0 : shellSpace m)) + t • ((0 : ℝ), D) = (0, t • D) := by
      apply Prod.ext
      · simp
      · simp
    rw [shellLoss, harg, shellCovarianceOnSpace_zero_ray D t]
  rw [hfun] at hline
  exact hline.symm.trans hquad

#print axioms shellCovarianceOnSpace_zero_ray
#print axioms shellLoss_hessian_sqChart

end SimplexFull.Geometry
