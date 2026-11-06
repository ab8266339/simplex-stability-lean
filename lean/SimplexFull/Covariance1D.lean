import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Separation.Basic

/-!
# One-dimensional integral covariance

General Lebesgue lemma on `ℝ`. It is the covariance identity used for tilted expectations,
instantiated later with a concrete weight. No Gaussian density is assumed here.

Given a continuous strictly monotone `f` and a continuous strictly positive weight `w`,
with `w`, `x ↦ x w x`, `x ↦ f x * w x`, and `x ↦ x f x * w x` integrable, set
`Z = ∫ w` and `x̄ = (∫ x w x) / Z`. The covariance numerator
`(∫ x f w) Z - (∫ f w) (∫ x w)` equals `Z` times
`∫ (f x - f x̄) (x - x̄) w x`, and that integral is strictly positive.
-/

noncomputable section

open Filter MeasureTheory

namespace SimplexFull

/-- Covariance integrand `(f x - f x̄) (x - x̄) w x`. -/
def covIntegrand (f w : ℝ → ℝ) (xbar : ℝ) : ℝ → ℝ :=
  fun x => (f x - f xbar) * (x - xbar) * w x

lemma mul_sub_nonneg_of_strictMono {f : ℝ → ℝ} (hf : StrictMono f) (a b : ℝ) :
    0 ≤ (f a - f b) * (a - b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hfa : f a - f b < 0 := sub_neg.mpr (hf hab)
    have ha : a - b < 0 := sub_neg.mpr hab
    have hpos : 0 < -(f a - f b) * -(a - b) :=
      mul_pos (neg_pos.mpr hfa) (neg_pos.mpr ha)
    rw [neg_mul_neg] at hpos
    exact hpos.le
  · simp [hab]
  · have hfa : 0 < f a - f b := sub_pos.mpr (hf hab)
    have ha : 0 < a - b := sub_pos.mpr hab
    exact (mul_pos hfa ha).le

lemma continuous_covIntegrand {f w : ℝ → ℝ} (hf : Continuous f) (hw : Continuous w) (xbar : ℝ) :
    Continuous (covIntegrand f w xbar) := by
  unfold covIntegrand
  exact ((hf.sub continuous_const).mul (continuous_id.sub continuous_const)).mul hw

lemma covIntegrand_nonneg {f w : ℝ → ℝ} (hf : StrictMono f) (hw : ∀ x, 0 < w x)
    (xbar x : ℝ) : 0 ≤ covIntegrand f w xbar x := by
  unfold covIntegrand
  exact mul_nonneg (mul_sub_nonneg_of_strictMono hf x xbar) (hw x).le

lemma covIntegrand_pos_add_one {f w : ℝ → ℝ} (hf : StrictMono f) (hw : ∀ x, 0 < w x)
    (xbar : ℝ) : 0 < covIntegrand f w xbar (xbar + 1) := by
  unfold covIntegrand
  have hx : xbar < xbar + 1 := lt_add_one xbar
  have hfx : 0 < f (xbar + 1) - f xbar := sub_pos.mpr (hf hx)
  have hdx : 0 < xbar + 1 - xbar := by
    rw [add_sub_cancel_left]
    exact zero_lt_one
  exact mul_pos (mul_pos hfx hdx) (hw (xbar + 1))

lemma integrable_covIntegrand {f w : ℝ → ℝ} {xbar : ℝ}
    (hw : Integrable w) (hxw : Integrable fun x => x * w x)
    (hfw : Integrable fun x => f x * w x) (hxfw : Integrable fun x => x * f x * w x) :
    Integrable (covIntegrand f w xbar) := by
  have hEq : covIntegrand f w xbar =
      (fun x => x * f x * w x) - (fun x => xbar * (f x * w x)) -
        (fun x => f xbar * (x * w x)) + fun x => (f xbar * xbar) * w x := by
    funext x
    simp only [covIntegrand, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hEq]
  exact ((hxfw.sub (hfw.const_mul xbar)).sub (hxw.const_mul (f xbar))).add
    (hw.const_mul (f xbar * xbar))

/-- A continuous everywhere-positive integrable weight has positive total mass. -/
theorem integral_weight_pos {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (hw : Integrable w) : 0 < ∫ x, w x := by
  have hnn : 0 ≤ w := fun x => (hw_pos x).le
  rw [integral_pos_iff_support_of_nonneg hnn hw]
  refine hw_cont.isOpen_support.measure_pos (volume : Measure ℝ) ⟨0, ?_⟩
  rw [Function.mem_support]
  exact (hw_pos 0).ne'

/-- The covariance integrand is continuous, nonnegative, and not identically zero, so its
integral is strictly positive. The center `xbar` is an arbitrary real; the barycenter is the
case used for the covariance numerator. -/
theorem integral_covIntegrand_pos {f w : ℝ → ℝ} {xbar : ℝ}
    (hf_cont : Continuous f) (hf_mono : StrictMono f)
    (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (hw : Integrable w) (hxw : Integrable fun x => x * w x)
    (hfw : Integrable fun x => f x * w x) (hxfw : Integrable fun x => x * f x * w x) :
    0 < ∫ x, covIntegrand f w xbar x := by
  have hnn : 0 ≤ covIntegrand f w xbar := fun x => covIntegrand_nonneg hf_mono hw_pos xbar x
  have hint := integrable_covIntegrand hw hxw hfw hxfw (xbar := xbar)
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  refine (continuous_covIntegrand hf_cont hw_cont xbar).isOpen_support.measure_pos
    (volume : Measure ℝ) ⟨xbar + 1, ?_⟩
  rw [Function.mem_support]
  exact (covIntegrand_pos_add_one hf_mono hw_pos xbar).ne'

lemma integral_covIntegrand_expand {f w : ℝ → ℝ} {xbar : ℝ}
    (hw : Integrable w) (hxw : Integrable fun x => x * w x)
    (hfw : Integrable fun x => f x * w x) (hxfw : Integrable fun x => x * f x * w x) :
    ∫ x, covIntegrand f w xbar x =
      (∫ x, x * f x * w x) - xbar * (∫ x, f x * w x) -
        f xbar * (∫ x, x * w x) + (f xbar * xbar) * (∫ x, w x) := by
  have h1 : Integrable fun x => x * f x * w x := hxfw
  have h2 : Integrable fun x => xbar * (f x * w x) := hfw.const_mul xbar
  have h3 : Integrable fun x => f xbar * (x * w x) := hxw.const_mul (f xbar)
  have h4 : Integrable fun x => (f xbar * xbar) * w x := hw.const_mul (f xbar * xbar)
  have h12 : Integrable fun x => x * f x * w x - xbar * (f x * w x) := h1.sub h2
  have h123 : Integrable fun x =>
      x * f x * w x - xbar * (f x * w x) - f xbar * (x * w x) := h12.sub h3
  calc
    ∫ x, covIntegrand f w xbar x
        = ∫ x, (x * f x * w x - xbar * (f x * w x) - f xbar * (x * w x)) +
            (f xbar * xbar) * w x := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only [covIntegrand]
          ring
      _ = (∫ x, x * f x * w x - xbar * (f x * w x) - f xbar * (x * w x)) +
            ∫ x, (f xbar * xbar) * w x :=
          integral_add h123 h4
      _ = ((∫ x, x * f x * w x - xbar * (f x * w x)) - ∫ x, f xbar * (x * w x)) +
            ∫ x, (f xbar * xbar) * w x := by
          rw [integral_sub h12 h3]
      _ = (((∫ x, x * f x * w x) - ∫ x, xbar * (f x * w x)) -
            ∫ x, f xbar * (x * w x)) + ∫ x, (f xbar * xbar) * w x := by
          rw [integral_sub h1 h2]
      _ = (((∫ x, x * f x * w x) - xbar * ∫ x, f x * w x) -
            f xbar * ∫ x, x * w x) + (f xbar * xbar) * ∫ x, w x := by
          rw [integral_const_mul xbar fun x => f x * w x,
            integral_const_mul (f xbar) fun x => x * w x,
            integral_const_mul (f xbar * xbar) w]
      _ = (∫ x, x * f x * w x) - xbar * (∫ x, f x * w x) -
            f xbar * (∫ x, x * w x) + (f xbar * xbar) * (∫ x, w x) := by
          ring

/-- Algebraic identification: with `Z = ∫ w` and `x̄ = (∫ x w) / Z`,
`(∫ x f w) Z - (∫ f w) (∫ x w) = Z * ∫ (f x - f x̄) (x - x̄) w x`. -/
theorem covNumerator_eq_mass_mul_integral (f w : ℝ → ℝ) (Z xbar : ℝ)
    (hZ : Z = ∫ x, w x) (hxbar : xbar = (∫ x, x * w x) / Z) (hZne : Z ≠ 0)
    (hw : Integrable w) (hxw : Integrable fun x => x * w x)
    (hfw : Integrable fun x => f x * w x) (hxfw : Integrable fun x => x * f x * w x) :
    (∫ x, x * f x * w x) * Z - (∫ x, f x * w x) * (∫ x, x * w x) =
      Z * ∫ x, covIntegrand f w xbar x := by
  have hInt := integral_covIntegrand_expand hw hxw hfw hxfw (xbar := xbar)
  subst hZ
  have hxz : ∫ x, x * w x = xbar * ∫ x, w x := by
    rw [hxbar]
    exact (div_mul_cancel₀ _ hZne).symm
  rw [hInt, hxz]
  ring

/-- Strict positivity of the covariance numerator. Hypotheses are integrability of the four
moments, continuity, strict monotonicity of `f`, and a strictly positive continuous weight.
The sign is not assumed. -/
theorem covNumerator_pos {f w : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_mono : StrictMono f)
    (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (hw : Integrable w) (hxw : Integrable fun x => x * w x)
    (hfw : Integrable fun x => f x * w x) (hxfw : Integrable fun x => x * f x * w x) :
    0 < (∫ x, x * f x * w x) * (∫ x, w x) - (∫ x, f x * w x) * (∫ x, x * w x) := by
  have hZpos : 0 < ∫ x, w x := integral_weight_pos hw_cont hw_pos hw
  let Z : ℝ := ∫ x, w x
  let xbar : ℝ := (∫ x, x * w x) / Z
  have hnum := covNumerator_eq_mass_mul_integral f w Z xbar rfl rfl hZpos.ne' hw hxw hfw hxfw
  have hint : 0 < ∫ x, covIntegrand f w xbar x :=
    integral_covIntegrand_pos hf_cont hf_mono hw_cont hw_pos hw hxw hfw hxfw
  rw [hnum]
  exact mul_pos hZpos hint

end SimplexFull

#print axioms SimplexFull.integral_weight_pos
#print axioms SimplexFull.integral_covIntegrand_pos
#print axioms SimplexFull.integral_covIntegrand_expand
#print axioms SimplexFull.covNumerator_eq_mass_mul_integral
#print axioms SimplexFull.covNumerator_pos