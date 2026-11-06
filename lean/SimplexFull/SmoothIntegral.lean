import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Differentiation under the integral

`F0 p x` is a Banach-valued integrand, `F1 p x` its Fréchet derivative in the parameter,
and `F2 p x` the derivative of that derivative. On an open parameter set these hypotheses

* `HasFDerivAt (F0 · x) (F1 p x) p` and `HasFDerivAt (F1 · x) (F2 p x) p` for every `p ∈ s`,
* spatial almost-everywhere strong measurability of `F0`, `F1`, and `F2`,
* integrability of `F0 p` at every `p ∈ s`,
* one integrable function bounding `‖F1 p ·‖` on `s`, and one bounding `‖F2 p ·‖`,
* `ContinuousOn (F2 · x) s`

imply that `p ↦ ∫ F0 p` is `C^2` on `s`, with first derivative `∫ F1` and second derivative `∫ F2`.
No integrated smoothness is assumed. A third derivative of `F0` is not required: continuity of the
integrated second derivative is dominated convergence applied to `F2`.

Matrix parameters are normed by `Matrix.Norms.L2Operator`; open that scope at the instantiation
site. The intended integrand is the precision-Gaussian slice
`F0(M, x) = exp(λ max x) * exp(-quad M x / 2)`, with
`F1 = (-F0 / 2) • qL x` and `F2 = (F0 / 4) • ((qL x).smulRight (qL x))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace SimplexFull.SmoothIntegral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- An almost-everywhere norm bound by an integrable scalar gives Bochner integrability. -/
theorem integrable_of_dominated
    {G : Type*} [NormedAddCommGroup G] {f : X → G} {b : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : Integrable b μ)
    (hle : ∀ᵐ x ∂μ, ‖f x‖ ≤ b x) : Integrable f μ :=
  hb.mono' hf hle

omit [NormedSpace ℝ P] in
/-- Dominated convergence: a common integrable bound and spatial continuity in the parameter
give continuity of the integral on `s`. -/
theorem continuousOn_integral_of_dominated
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P → X → G} {b : X → ℝ} {s : Set P}
    (h_meas : ∀ p ∈ s, AEStronglyMeasurable (F p) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ p ∈ s, ‖F p x‖ ≤ b x)
    (hb : Integrable b μ)
    (h_cont : ∀ᵐ x ∂μ, ContinuousOn (F · x) s) :
    ContinuousOn (fun p => ∫ x, F p x ∂μ) s :=
  continuousOn_of_dominated h_meas (fun p hp => h_bound.mono fun _ hx => hx p hp) hb h_cont

/-- Derivative of `p ↦ ∫ F0 p` at a point of an open set, under one integrable bound on `F1`. -/
theorem hasFDerivAt_integral
    {F0 : P → X → E} {F1 : P → X → P →L[ℝ] E}
    {s : Set P} {b1 : X → ℝ} {p : P}
    (hs : IsOpen s) (hp : p ∈ s)
    (hF0_meas : ∀ q ∈ s, AEStronglyMeasurable (F0 q) μ)
    (hF0_int : Integrable (F0 p) μ)
    (hF1_meas : AEStronglyMeasurable (F1 p) μ)
    (hF1_bound : ∀ᵐ x ∂μ, ∀ q ∈ s, ‖F1 q x‖ ≤ b1 x)
    (hb1 : Integrable b1 μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ q ∈ s, HasFDerivAt (F0 · x) (F1 q x) q) :
    HasFDerivAt (fun q => ∫ x, F0 q x ∂μ) (∫ x, F1 p x ∂μ) p := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s) (hs.mem_nhds hp)
    ?_ hF0_int hF1_meas hF1_bound hb1 h_diff
  filter_upwards [hs.mem_nhds hp] with q hq
  exact hF0_meas q hq

/-- The Fréchet derivative of the parametric integral is the integral of `F1`. -/
theorem fderiv_integral
    {F0 : P → X → E} {F1 : P → X → P →L[ℝ] E}
    {s : Set P} {b1 : X → ℝ} {p : P}
    (hs : IsOpen s) (hp : p ∈ s)
    (hF0_meas : ∀ q ∈ s, AEStronglyMeasurable (F0 q) μ)
    (hF0_int : Integrable (F0 p) μ)
    (hF1_meas : AEStronglyMeasurable (F1 p) μ)
    (hF1_bound : ∀ᵐ x ∂μ, ∀ q ∈ s, ‖F1 q x‖ ≤ b1 x)
    (hb1 : Integrable b1 μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ q ∈ s, HasFDerivAt (F0 · x) (F1 q x) q) :
    fderiv ℝ (fun q => ∫ x, F0 q x ∂μ) p = ∫ x, F1 p x ∂μ :=
  (hasFDerivAt_integral hs hp hF0_meas hF0_int hF1_meas hF1_bound hb1 h_diff).fderiv

omit [MeasurableSpace X] in
/-- Pointwise parameter derivatives are continuous on `s`. -/
theorem continuousOn_of_hasFDerivAt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P → X → G} {F' : P → X → P →L[ℝ] G} {s : Set P}
    (h_diff : ∀ x, ∀ p ∈ s, HasFDerivAt (F · x) (F' p x) p) :
    ∀ x, ContinuousOn (F · x) s := by
  intro x p hp
  exact (h_diff x p hp).differentiableAt.continuousAt.continuousWithinAt

/-- On an open set, `C^{n+1}` follows from differentiability and `C^n` of a derivative that
agrees with `fderiv` on the set. -/
theorem contDiffOn_succ_of_hasFDerivAt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : P → G} {f' : P → P →L[ℝ] G} {s : Set P} {n : ℕ}
    (hs : IsOpen s)
    (h_diff : ∀ p ∈ s, HasFDerivAt f (f' p) p)
    (h_cont : ContDiffOn ℝ n f' s) :
    ContDiffOn ℝ (n + 1) f s := by
  rw [show (n + 1 : ℕ∞ω) = (n : ℕ) + 1 from rfl]
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨fun p hp => (h_diff p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact h_cont.congr fun p hp => (h_diff p hp).fderiv

/-- Integrated `C^2` regularity, with the first and second derivatives under the integral. -/
theorem contDiffOn_integral
    {F0 : P → X → E}
    {F1 : P → X → P →L[ℝ] E}
    {F2 : P → X → P →L[ℝ] (P →L[ℝ] E)}
    {s : Set P} {b1 b2 : X → ℝ}
    (hs : IsOpen s)
    (h_diff0 : ∀ x, ∀ p ∈ s, HasFDerivAt (F0 · x) (F1 p x) p)
    (h_diff1 : ∀ x, ∀ p ∈ s, HasFDerivAt (F1 · x) (F2 p x) p)
    (hF0_meas : ∀ p ∈ s, AEStronglyMeasurable (F0 p) μ)
    (hF1_meas : ∀ p ∈ s, AEStronglyMeasurable (F1 p) μ)
    (hF2_meas : ∀ p ∈ s, AEStronglyMeasurable (F2 p) μ)
    (hF0_int : ∀ p ∈ s, Integrable (F0 p) μ)
    (hF1_bound : ∀ᵐ x ∂μ, ∀ p ∈ s, ‖F1 p x‖ ≤ b1 x)
    (hb1 : Integrable b1 μ)
    (hF2_bound : ∀ᵐ x ∂μ, ∀ p ∈ s, ‖F2 p x‖ ≤ b2 x)
    (hb2 : Integrable b2 μ)
    (hF2_cont : ∀ x, ContinuousOn (F2 · x) s) :
    ContDiffOn ℝ 2 (fun p => ∫ x, F0 p x ∂μ) s ∧
      (∀ p ∈ s, fderiv ℝ (fun q => ∫ x, F0 q x ∂μ) p = ∫ x, F1 p x ∂μ) ∧
      (∀ p ∈ s, fderiv ℝ (fderiv ℝ (fun q => ∫ x, F0 q x ∂μ)) p =
        ∫ x, F2 p x ∂μ) := by
  let I : P → E := fun p => ∫ x, F0 p x ∂μ
  let I1 : P → P →L[ℝ] E := fun p => ∫ x, F1 p x ∂μ
  let I2 : P → P →L[ℝ] (P →L[ℝ] E) := fun p => ∫ x, F2 p x ∂μ
  have hHas0 : ∀ p ∈ s, HasFDerivAt I (I1 p) p := by
    intro p hp
    exact hasFDerivAt_integral hs hp hF0_meas (hF0_int p hp) (hF1_meas p hp)
      hF1_bound hb1 (Eventually.of_forall fun x => h_diff0 x)
  have hF1_int : ∀ p ∈ s, Integrable (F1 p) μ := by
    intro p hp
    exact integrable_of_dominated (hF1_meas p hp) hb1 (hF1_bound.mono fun x hx => hx p hp)
  have hHas1 : ∀ p ∈ s, HasFDerivAt I1 (I2 p) p := by
    intro p hp
    exact hasFDerivAt_integral hs hp hF1_meas (hF1_int p hp) (hF2_meas p hp)
      hF2_bound hb2 (Eventually.of_forall fun x => h_diff1 x)
  have hI2_cont : ContinuousOn I2 s :=
    continuousOn_integral_of_dominated hF2_meas hF2_bound hb2 (Eventually.of_forall hF2_cont)
  have hI1_c1 : ContDiffOn ℝ 1 I1 s :=
    contDiffOn_succ_of_hasFDerivAt (n := 0) hs hHas1 (contDiffOn_zero.2 hI2_cont)
  have hI_c2 : ContDiffOn ℝ 2 I s :=
    contDiffOn_succ_of_hasFDerivAt (n := 1) hs hHas0 hI1_c1
  refine ⟨hI_c2, fun p hp => (hHas0 p hp).fderiv, fun p hp => ?_⟩
  have hagree : fderiv ℝ I =ᶠ[𝓝 p] I1 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hHas0 q hq).fderiv
  exact hagree.fderiv_eq.trans (hHas1 p hp).fderiv

#print axioms SimplexFull.SmoothIntegral.hasFDerivAt_integral
#print axioms SimplexFull.SmoothIntegral.fderiv_integral
#print axioms SimplexFull.SmoothIntegral.continuousOn_integral_of_dominated
#print axioms SimplexFull.SmoothIntegral.contDiffOn_integral

end SimplexFull.SmoothIntegral
