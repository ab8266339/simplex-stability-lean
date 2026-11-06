import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Ring

/-!
Second derivative of a scalar along the quadratic path `t ↦ x + (2 t) • B + t² • C`.

`C²` at `x` gives an eventual first-derivative identity by composing `fderiv` with the
path, then `Filter.EventuallyEq.deriv_eq` moves that identity onto the second derivative.
The derivative of the pointwise application is `HasDerivAt.clm_apply`.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter ContinuousLinearMap
open scoped Topology

namespace SimplexFull.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

/-- Velocity of `s ↦ x + (2 s) • B + s² • C` is `2 • B + (2 s) • C`. -/
theorem hasDerivAt_quadPath (x B C : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + (2 * s) • B + (s ^ 2) • C)
      ((2 : ℝ) • B + (2 * t) • C) t := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) t := hasDerivAt_const_mul 2
  have hB : HasDerivAt (fun s : ℝ => (2 * s) • B) ((2 : ℝ) • B) t := hlin.smul_const B
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa [pow_one] using hasDerivAt_pow 2 t
  have hC : HasDerivAt (fun s : ℝ => (s ^ 2) • C) ((2 * t) • C) t := hsq.smul_const C
  have hx : HasDerivAt (fun _ : ℝ => x) 0 t := hasDerivAt_const t x
  have hsum := (hx.add hB).add hC
  simp only [zero_add] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]

/-- Acceleration of the quadratic path is the constant `2 • C`. -/
theorem hasDerivAt_quadVelocity (B C : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (2 : ℝ) • B + (2 * s) • C) ((2 : ℝ) • C) t := by
  have hconst : HasDerivAt (fun _ : ℝ => (2 : ℝ) • B) 0 t := hasDerivAt_const t ((2 : ℝ) • B)
  have hlin : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) t := hasDerivAt_const_mul 2
  have hC : HasDerivAt (fun s : ℝ => (2 * s) • C) ((2 : ℝ) • C) t := hlin.smul_const C
  have hsum := hconst.add hC
  simp only [zero_add] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]

/-- Second derivative of `f` along `t ↦ x + (2 t) • B + t² • C`, at `t = 0`. -/
theorem secondDeriv_quadPath {f : E → ℝ} {x B C : E} (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun t : ℝ => f (x + (2 * t) • B + (t ^ 2) • C))) 0 =
      4 * ((fderiv ℝ (fderiv ℝ f) x B) B) + 2 * ((fderiv ℝ f x) C) := by
  let g : ℝ → E := fun s => x + (2 * s) • B + (s ^ 2) • C
  let v : ℝ → E := fun s => (2 : ℝ) • B + (2 * s) • C
  have hgv : ∀ t, HasDerivAt g (v t) t := by
    intro t
    simpa only [g, v] using hasDerivAt_quadPath x B C t
  have hg0 : g 0 = x := by simp [g]
  have hvel0 : v 0 = (2 : ℝ) • B := by simp [v]
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have htend : Tendsto g (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa [hg0] using (hgv 0).continuousAt.tendsto
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (g t) := htend.eventually hnear
  have hfirst : deriv (fun t => f (g t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (fderiv ℝ f (g t)) (v t) := by
    filter_upwards [hdiff] with t ht
    have hfd := (ht.hasFDerivAt.comp_hasDerivAt t (hgv t)).deriv
    have hcomp_fun : f ∘ g = fun s => f (g s) := by
      funext s
      rfl
    rw [hcomp_fun] at hfd
    exact hfd
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hdf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    hf1.differentiableAt_one.hasFDerivAt
  have hcomp : HasDerivAt (fun t => fderiv ℝ f (g t))
      ((fderiv ℝ (fderiv ℝ f) x) (v 0)) 0 := by
    have hfd := hdf.comp_hasDerivAt_of_eq 0 (hgv 0) hg0.symm
    have hcomp_fun : fderiv ℝ f ∘ g = fun s => fderiv ℝ f (g s) := by
      funext s
      rfl
    rw [hcomp_fun] at hfd
    exact hfd
  have happ : HasDerivAt (fun t => (fderiv ℝ f (g t)) (v t))
      (((fderiv ℝ (fderiv ℝ f) x) (v 0)) (v 0) + (fderiv ℝ f (g 0)) ((2 : ℝ) • C)) 0 :=
    hcomp.clm_apply (by simpa only [v] using hasDerivAt_quadVelocity B C 0)
  have hscalar : ((fderiv ℝ (fderiv ℝ f) x) ((2 : ℝ) • B)) ((2 : ℝ) • B) +
      (fderiv ℝ f x) ((2 : ℝ) • C) =
      4 * ((fderiv ℝ (fderiv ℝ f) x B) B) + 2 * ((fderiv ℝ f x) C) := by
    set H := fderiv ℝ (fderiv ℝ f) x
    have hsmul : H ((2 : ℝ) • B) = (2 : ℝ) • H B := H.map_smul (2 : ℝ) B
    have houter : ((2 : ℝ) • H B) ((2 : ℝ) • B) = (2 : ℝ) • (H B) ((2 : ℝ) • B) := by
      rw [smul_apply]
    have hinner : (H B) ((2 : ℝ) • B) = (2 : ℝ) • (H B) B := (H B).map_smul (2 : ℝ) B
    have hC : (fderiv ℝ f x) ((2 : ℝ) • C) = (2 : ℝ) • (fderiv ℝ f x) C :=
      (fderiv ℝ f x).map_smul (2 : ℝ) C
    rw [hsmul, houter, hinner, hC, smul_smul, smul_eq_mul, smul_eq_mul]
    ring
  calc
    deriv (deriv (fun t => f (g t))) 0
        = deriv (fun t => (fderiv ℝ f (g t)) (v t)) 0 := Filter.EventuallyEq.deriv_eq hfirst
    _ = ((fderiv ℝ (fderiv ℝ f) x) (v 0)) (v 0) +
          (fderiv ℝ f (g 0)) ((2 : ℝ) • C) := happ.deriv
    _ = ((fderiv ℝ (fderiv ℝ f) x) ((2 : ℝ) • B)) ((2 : ℝ) • B) +
          (fderiv ℝ f x) ((2 : ℝ) • C) := by rw [hvel0, hg0]
    _ = 4 * ((fderiv ℝ (fderiv ℝ f) x B) B) + 2 * ((fderiv ℝ f x) C) := hscalar

/-- The second derivative along the affine line `t ↦ x + t • v` is the Fréchet Hessian. -/
theorem secondDeriv_line {f : E → ℝ} {x v : E} (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 = (fderiv ℝ (fderiv ℝ f) x v) v := by
  set B : E := (1 / 2 : ℝ) • v
  have hscale (t : ℝ) : (2 * t) • B = t • v := by
    simp only [B, smul_smul]
    congr 1
    ring
  have hfun : (fun t : ℝ => f (x + t • v)) =
      fun t => f (x + (2 * t) • B + (t ^ 2) • (0 : E)) := by
    funext t
    rw [hscale t, smul_zero, add_zero]
  rw [hfun]
  have hquad := secondDeriv_quadPath (f := f) (x := x) (B := B) (C := (0 : E)) hf
  rw [hquad, map_zero (fderiv ℝ f x), mul_zero, add_zero]
  set H := fderiv ℝ (fderiv ℝ f) x
  have hlin : H B = (1 / 2 : ℝ) • H v := by
    simp only [B]
    exact H.map_smul (1 / 2 : ℝ) v
  have happ : ((1 / 2 : ℝ) • H v) B = (1 / 2 : ℝ) • (H v) B := by
    rw [smul_apply]
  have happ2 : (H v) ((1 / 2 : ℝ) • v) = (1 / 2 : ℝ) • (H v) v := (H v).map_smul (1 / 2 : ℝ) v
  rw [hlin, happ]
  simp only [B]
  rw [happ2, smul_smul, smul_eq_mul]
  ring

#print axioms secondDeriv_quadPath
#print axioms secondDeriv_line

end SimplexFull.Geometry
