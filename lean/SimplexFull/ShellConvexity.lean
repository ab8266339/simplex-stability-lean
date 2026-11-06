import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Analytic engine for the strict-normal shell, corresponding to the second-derivative
criterion in `input/ANALYTIC_PROOF.md`, Section 11.7.

`HessianCLM E` is the actual continuous bilinear Hessian codomain
`(ℝ × E) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ)`. The first lemmas turn continuity of a map into that
codomain, plus coercivity on vertical directions `(0, v)` at the origin, into a
neighborhood lower bound `(c / 2) ‖v‖²`. No minimization statement is assumed.
-/

noncomputable section

open scoped ContDiff Topology
open Bornology Filter Metric Set

namespace SimplexFull.Geometry.Convexity

variable {E : Type*} [NormedAddCommGroup E]

/-- The product norm is the sup norm, so a vertical vector `(0, v)` has norm `‖v‖`. -/
lemma norm_vertical (v : E) : ‖((0 : ℝ), v)‖ = ‖v‖ := by
  rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg v)]

variable [NormedSpace ℝ E]

local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

/-- Continuous bilinear maps `(ℝ × E) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ)`, the codomain of
`fderiv ℝ (fderiv ℝ f)` for `f : (ℝ × E) → ℝ`. -/
abbrev HessianCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (ℝ × E) →L[ℝ] ((ℝ × E) →L[ℝ] ℝ)

/-- Operator-norm control of the vertical quadratic form:
`|(B - B₀) (0, v) (0, v)| ≤ ‖B - B₀‖ * ‖v‖²`. -/
theorem hessianForm_sub_le (B₀ B : HessianCLM E) (v : E) :
    |B (0, v) (0, v) - B₀ (0, v) (0, v)| ≤ ‖B - B₀‖ * ‖v‖ ^ 2 := by
  rw [← Real.norm_eq_abs]
  have hpoint :
      B (0, v) (0, v) - B₀ (0, v) (0, v) = (B - B₀) ((0 : ℝ), v) ((0 : ℝ), v) := by
    simp
  rw [hpoint]
  have houter := ContinuousLinearMap.le_opNorm ((B - B₀) ((0 : ℝ), v)) ((0 : ℝ), v)
  have hinner := ContinuousLinearMap.le_opNorm (B - B₀) ((0 : ℝ), v)
  have hstep :
      ‖(B - B₀) ((0 : ℝ), v) ((0 : ℝ), v)‖ ≤ ‖B - B₀‖ * ‖v‖ * ‖v‖ := by
    refine houter.trans ?_
    have hmul := mul_le_mul_of_nonneg_right hinner (norm_nonneg ((0 : ℝ), v))
    simpa [norm_vertical] using hmul
  calc
    ‖(B - B₀) ((0 : ℝ), v) ((0 : ℝ), v)‖ ≤ ‖B - B₀‖ * ‖v‖ * ‖v‖ := hstep
    _ = ‖B - B₀‖ * ‖v‖ ^ 2 := by ring

/-- Coercivity at `B₀` survives an operator-norm perturbation of size at most `c / 2`. -/
theorem hessianForm_lower_of_opNorm {B₀ B : HessianCLM E} {c : ℝ}
    (hcoer : ∀ v : E, c * ‖v‖ ^ 2 ≤ B₀ (0, v) (0, v))
    (hclose : ‖B - B₀‖ ≤ c / 2) (v : E) :
    (c / 2) * ‖v‖ ^ 2 ≤ B (0, v) (0, v) := by
  have hdiff : |B (0, v) (0, v) - B₀ (0, v) (0, v)| ≤ (c / 2) * ‖v‖ ^ 2 :=
    (hessianForm_sub_le B₀ B v).trans
      (mul_le_mul_of_nonneg_right hclose (sq_nonneg ‖v‖))
  rw [abs_le] at hdiff
  have hlow : B₀ (0, v) (0, v) - (c / 2) * ‖v‖ ^ 2 ≤ B (0, v) (0, v) := by
    linarith
  linarith [hcoer v]

/-- An open norm ball in `ℝ` is a neighborhood of the origin. -/
lemma real_norm_ball_mem_nhds_zero {δ : ℝ} (hδ : 0 < δ) :
    {y : ℝ | ‖y‖ < δ} ∈ 𝓝 (0 : ℝ) := by
  have hsub : {y : ℝ | ‖y‖ < δ} = ball 0 δ := by
    ext y
    simp [mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  rw [hsub]
  exact ball_mem_nhds 0 hδ

/-- If every vector of the closed unit ball is sent into the open `ε / 2` ball of the codomain,
the operator norm is strictly less than `ε`. -/
lemma opNorm_lt_of_unitBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (ℝ × E) →L[ℝ] F} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ x ∈ closedBall (0 : ℝ × E) 1, ‖f x‖ ≤ ε / 2) :
    ‖f‖ < ε := by
  have hhalf : 0 ≤ ε / 2 := (half_pos hε).le
  have hle : ‖f‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound f hhalf ?_
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · set u : ℝ × E := ‖x‖⁻¹ • x
      have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ hxnorm]
      have hu_mem : u ∈ closedBall (0 : ℝ × E) 1 := by
        rw [mem_closedBall, dist_eq_norm, sub_zero, hu]
      have hxsmul : ‖x‖ • u = x := by
        simp [u, smul_smul, mul_inv_cancel₀ hxnorm]
      have hfx : f x = ‖x‖ • f u := by
        conv_lhs => rw [← hxsmul]
        rw [map_smul]
      calc
        ‖f x‖ = ‖‖x‖ • f u‖ := by rw [hfx]
        _ = ‖x‖ * ‖f u‖ := by
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
        _ ≤ ‖x‖ * (ε / 2) :=
          mul_le_mul_of_nonneg_left (hf u hu_mem) (norm_nonneg x)
        _ = (ε / 2) * ‖x‖ := by ring
  exact hle.trans_lt (half_lt_self hε)

/-- An open operator-norm ball is a bounded-convergence neighborhood of zero, once the same
fact is known one level down in the codomain. -/
lemma clm_norm_ball_mem_nhds_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsTopologicalAddGroup F] {ε : ℝ} (hε : 0 < ε)
    (hcod : {y : F | ‖y‖ < ε / 2} ∈ 𝓝 (0 : F)) :
    {f : (ℝ × E) →L[ℝ] F | ‖f‖ < ε} ∈ 𝓝 (0 : (ℝ × E) →L[ℝ] F) := by
  rw [ContinuousLinearMap.hasBasis_nhds_zero.mem_iff]
  refine ⟨(closedBall (0 : ℝ × E) 1, {y : F | ‖y‖ < ε / 2}), ⟨?_, ?_⟩, ?_⟩
  · exact NormedSpace.isVonNBounded_closedBall ℝ (ℝ × E) 1
  · exact hcod
  · intro f hf
    refine opNorm_lt_of_unitBall hε ?_
    intro x hx
    exact (hf x hx).le

/-- Open operator-norm balls in `(ℝ × E) →L[ℝ] ℝ`. -/
lemma innerCLM_norm_ball_mem_nhds_zero {ε : ℝ} (hε : 0 < ε) :
    {f : (ℝ × E) →L[ℝ] ℝ | ‖f‖ < ε} ∈ 𝓝 (0 : (ℝ × E) →L[ℝ] ℝ) :=
  clm_norm_ball_mem_nhds_zero hε (real_norm_ball_mem_nhds_zero (half_pos hε))

/-- Open operator-norm balls in the Hessian codomain. -/
lemma hessianCLM_norm_ball_mem_nhds_zero {ε : ℝ} (hε : 0 < ε) :
    {f : HessianCLM E | ‖f‖ < ε} ∈ 𝓝 (0 : HessianCLM E) :=
  clm_norm_ball_mem_nhds_zero hε (innerCLM_norm_ball_mem_nhds_zero (half_pos hε))

/-- Continuity of `B` at the origin upgrades coercivity `c` to a ball on which every
vertical quadratic form is at least `c / 2`. -/
theorem exists_hessianForm_lower {B : (ℝ × E) → HessianCLM E}
    (hB : ContinuousAt B 0) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : E, c * ‖v‖ ^ 2 ≤ B 0 (0, v) (0, v)) :
    ∃ δ > 0, ∀ p : ℝ × E, ‖p‖ < δ →
      ∀ v : E, (c / 2) * ‖v‖ ^ 2 ≤ B p (0, v) (0, v) := by
  unfold ContinuousAt at hB
  have htend :
      Tendsto (fun p : ℝ × E => B p - B 0) (𝓝 (0 : ℝ × E)) (𝓝 (0 : HessianCLM E)) :=
    (tendsto_sub_nhds_zero_iff (u := B) (x := B 0) (l := 𝓝 (0 : ℝ × E))).2 hB
  have hnear :
      {p : ℝ × E | ‖B p - B 0‖ < c / 2} ∈ 𝓝 (0 : ℝ × E) := by
    have hpre := htend (hessianCLM_norm_ball_mem_nhds_zero (half_pos hc))
    simpa [Set.preimage, Set.mem_setOf] using hpre
  have hzero : (0 : ℝ × E) = ((0 : ℝ), (0 : E)) := Prod.ext rfl rfl
  rw [hzero, nhds_prod_eq, mem_prod_iff] at hnear
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hnear
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp ht₁
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp ht₂
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro p hp v
  have hp₁ : ‖p.1‖ < ε := lt_of_le_of_lt (norm_fst_le p) (lt_of_lt_of_le hp (min_le_left ε δ))
  have hp₂ : ‖p.2‖ < δ := lt_of_le_of_lt (norm_snd_le p) (lt_of_lt_of_le hp (min_le_right ε δ))
  have hp_prod : p ∈ t₁ ×ˢ t₂ := by
    refine ⟨hεball ?_, hδball ?_⟩
    · rw [mem_ball, dist_eq_norm, sub_zero]
      exact hp₁
    · rw [mem_ball, dist_eq_norm, sub_zero]
      exact hp₂
  have hclose : ‖B p - B 0‖ < c / 2 := hsub hp_prod
  exact hessianForm_lower_of_opNorm hcoer hclose.le v

/-- A globally `C²` map has a continuous Hessian `fderiv ℝ (fderiv ℝ f)`. -/
theorem hessian_continuous_of_contDiff {f : (ℝ × E) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous fun p => fderiv ℝ (fderiv ℝ f) p := by
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) :=
    ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1) (f := f)).1 hf).2.2
  exact hf'.continuous_fderiv (by simp)

/-- On an open set, `C²` gives continuity of the actual Hessian, not only of an
iterated multilinear derivative. -/
theorem hessian_continuousOn_of_contDiffOn {U : Set (ℝ × E)} {f : (ℝ × E) → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (fun p => fderiv ℝ (fderiv ℝ f) p) U := by
  have hf' : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU le_rfl
  exact hf'.continuousOn_fderiv_of_isOpen hU le_rfl

/-- Local strict minimum along vertical slices.

`f` is `C²` on an open neighborhood of the origin, the vertical derivative
`fderiv ℝ f (τ, 0) (0, ·)` vanishes for every small `τ`, and the vertical Hessian at the
origin is coercive. The conclusion is not assumed: Taylor expansion of
`t ↦ f (τ, t • x)` with Lagrange remainder produces the quadratic lower bound.
-/
theorem exists_local_quadratic_min
    {U : Set (ℝ × E)} {f : (ℝ × E) → ℝ} {c : ℝ}
    (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : E)) ∈ U)
    (hf : ContDiffOn ℝ 2 f U) (hc : 0 < c)
    (hcoer : ∀ v : E,
      c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) ((0 : ℝ), (0 : E)) (0, v) (0, v))
    (hcrit : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ v : E, fderiv ℝ f (τ, (0 : E)) (0, v) = 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ τ : ℝ, |τ| < ε → ∀ x : E, ‖x‖ < δ →
      f (τ, (0 : E)) + (c / 4) * ‖x‖ ^ 2 ≤ f (τ, x) ∧
      (f (τ, x) = f (τ, (0 : E)) ↔ x = 0) := by
  have hB : ContinuousAt (fun p => fderiv ℝ (fderiv ℝ f) p) ((0 : ℝ), (0 : E)) :=
    (hessian_continuousOn_of_contDiffOn hU hf).continuousAt (hU.mem_nhds h0)
  have hzero_prod : (0 : ℝ × E) = ((0 : ℝ), (0 : E)) := Prod.ext rfl rfl
  have hcoer0 : ∀ v : E,
      c * ‖v‖ ^ 2 ≤ (fun p => fderiv ℝ (fderiv ℝ f) p) 0 (0, v) (0, v) := by
    intro v
    simpa [hzero_prod] using hcoer v
  obtain ⟨δH, hδH, hH⟩ := exists_hessianForm_lower hB hc hcoer0
  obtain ⟨δU, hδU, hUball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨εc, hεc, hcritε⟩ := Metric.eventually_nhds_iff.mp hcrit
  set ρ : ℝ := min δH (min δU εc)
  have hρ : 0 < ρ := lt_min hδH (lt_min hδU hεc)
  have hρH : ρ ≤ δH := min_le_left _ _
  have hρU : ρ ≤ δU := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρε : ρ ≤ εc := le_trans (min_le_right _ _) (min_le_right _ _)
  have hU_of_norm {p : ℝ × E} (hp : ‖p‖ < δU) : p ∈ U := by
    apply hUball
    rw [Metric.mem_ball, dist_eq_norm, ← hzero_prod, sub_zero]
    exact hp
  refine ⟨ρ, hρ, ρ, hρ, ?_⟩
  intro τ hτ x hxlt
  have hτρ : |τ| < ρ := hτ
  have hcritτ : ∀ v : E, fderiv ℝ f (τ, (0 : E)) (0, v) = 0 :=
    hcritε (y := τ) <| by
      rw [Real.dist_eq, sub_zero]
      exact lt_of_lt_of_le hτρ hρε
  let γ : ℝ → ℝ × E := fun s => (τ, s • x)
  let g : ℝ → ℝ := f ∘ γ
  have hγderiv (t : ℝ) : HasDerivAt γ (0, x) t := by
    have hcτ : HasDerivAt (fun _ : ℝ => τ) 0 t := hasDerivAt_const t τ
    have hs : HasDerivAt (fun s : ℝ => s • x) ((1 : ℝ) • x) t :=
      (hasDerivAt_id t).smul_const x
    simpa [γ, one_smul] using hcτ.prodMk hs
  have hγcont : ContDiff ℝ 2 γ :=
    (contDiff_const.prodMk ((contDiff_id : ContDiff ℝ 2 (id : ℝ → ℝ)).smul_const x) : _)
  have hball (t : ℝ) (ht : |t| ≤ 1) : ‖γ t‖ < ρ := by
    dsimp [γ]
    rw [norm_smul, Real.norm_eq_abs]
    have hmul : |t| * ‖x‖ ≤ ‖x‖ := by
      simpa using mul_le_mul_of_nonneg_right ht (norm_nonneg x)
    exact max_lt hτρ (lt_of_le_of_lt hmul hxlt)
  have hmem (t : ℝ) (ht : |t| < 1) : γ t ∈ U :=
    hU_of_norm (lt_of_lt_of_le (hball t ht.le) hρU)
  have hHas (t : ℝ) (ht : |t| < 1) :=
    ((hf.contDiffAt (hU.mem_nhds (hmem t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      t (hγderiv t)
  have hφ (t : ℝ) (ht : |t| < 1) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU le_rfl
    have hfd :=
      ((h1.contDiffAt (hU.mem_nhds (hmem t ht))).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hfd.comp_hasDerivAt t (hγderiv t)
    exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), x)).hasFDerivAt.comp_hasDerivAt t hcomp
  have hgcont : ContDiffOn ℝ 2 g (uIcc 0 1) := by
    refine hf.comp hγcont.contDiffOn ?_
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have htabs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    exact hU_of_norm (lt_of_lt_of_le (hball t htabs) hρU)
  have hdw : derivWithin g (uIcc 0 1) 0 = 0 := by
    have habs : |(0 : ℝ)| < 1 := by norm_num
    have hhas := hHas 0 habs
    have hzero : (fderiv ℝ f (γ 0)) ((0 : ℝ), x) = 0 := by
      simpa [γ, zero_smul] using hcritτ x
    have hhas0 : HasDerivAt g 0 0 := by simpa [hzero] using hhas
    have hunq : UniqueDiffWithinAt ℝ (uIcc (0 : ℝ) 1) 0 := by
      rw [uIcc_of_le zero_le_one]
      exact uniqueDiffOn_Icc_zero_one 0 ⟨le_rfl, zero_le_one⟩
    rw [hhas0.differentiableAt.derivWithin hunq, hhas0.deriv]
  obtain ⟨ξ, hξ, htaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x₀ := 0) (x := 1) (n := 1)
      zero_ne_one hgcont
  rw [uIoo_of_le zero_le_one] at hξ
  have hξabs : |ξ| < 1 := by
    rw [abs_of_pos hξ.1]
    exact hξ.2
  have hsec : iteratedDeriv 2 g ξ =
      (fderiv ℝ (fderiv ℝ f) (γ ξ) ((0 : ℝ), x)) ((0 : ℝ), x) := by
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one]
    have heq : deriv g =ᶠ[𝓝 ξ] (fun s => (fderiv ℝ f (γ s)) ((0 : ℝ), x)) := by
      filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with t ht
      have htabs : |t| < 1 := by
        rw [abs_of_pos ht.1]
        exact ht.2
      exact (hHas t htabs).deriv
    have hφ' := (hφ ξ hξabs).congr_of_eventuallyEq heq
    simpa [ContinuousLinearMap.apply_apply] using hφ'.deriv
  have hξnorm : ‖γ ξ‖ < δH := lt_of_lt_of_le (hball ξ hξabs.le) hρH
  have hlow_form : (c / 2) * ‖x‖ ^ 2 ≤ iteratedDeriv 2 g ξ := by
    rw [hsec]
    exact hH (γ ξ) hξnorm x
  have hpoly : taylorWithinEval g 1 (uIcc (0 : ℝ) 1) 0 1 = g 0 := by
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      iteratedDerivWithin_zero, iteratedDerivWithin_one, hdw]
    simp [Nat.factorial, smul_eq_mul]
  have hdiff : g 1 - g 0 = iteratedDeriv 2 g ξ / 2 := by
    rw [hpoly] at htaylor
    simpa [Nat.factorial, pow_two] using htaylor
  have hg0 : g 0 = f (τ, (0 : E)) := by simp [g, γ, zero_smul]
  have hg1 : g 1 = f (τ, x) := by simp [g, γ, one_smul]
  have hquart : (c / 4) * ‖x‖ ^ 2 ≤ g 1 - g 0 := by
    calc (c / 4) * ‖x‖ ^ 2
        = (c / 2) * ‖x‖ ^ 2 / 2 := by ring
      _ ≤ iteratedDeriv 2 g ξ / 2 :=
          div_le_div_of_nonneg_right hlow_form (by norm_num)
      _ = g 1 - g 0 := hdiff.symm
  have hc4 : 0 < c / 4 := div_pos hc (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hg0, hg1] at hquart
    linarith
  · constructor
    · intro heq
      have hle0 : (c / 4) * ‖x‖ ^ 2 ≤ 0 := by
        rw [hg0, hg1, heq, sub_self] at hquart
        exact hquart
      rw [← mul_zero (c / 4)] at hle0
      have hsq : ‖x‖ ^ 2 = 0 :=
        le_antisymm (le_of_mul_le_mul_left hle0 hc4) (sq_nonneg _)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    · rintro rfl
      rfl

#print axioms norm_vertical
#print axioms hessian_continuous_of_contDiff
#print axioms hessian_continuousOn_of_contDiffOn
#print axioms exists_local_quadratic_min
#print axioms hessianForm_sub_le
#print axioms hessianForm_lower_of_opNorm
#print axioms exists_hessianForm_lower

end SimplexFull.Geometry.Convexity
