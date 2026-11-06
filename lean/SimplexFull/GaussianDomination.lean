import SimplexFull.GaussianDensity
import SimplexFull.Decoder
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Lebesgue integrability of Gaussian moments

Polynomial-exponential moments of a centered Gaussian on `EuclideanSpace ℝ (Fin m)`:

`‖x‖^n * exp(λ * maxCoord x) * exp(-c ‖x‖²)`, `c > 0`.

The comparison function is a pure Gaussian. `exp(-c ‖x‖²)` is integrable by
`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`. The coordinate maximum is at
most the Euclidean norm, and `‖x‖^n ≤ n ! exp ‖x‖`, so the product is bounded by
`exp((1+|λ|) ‖x‖ - c ‖x‖²)`. Completing the square absorbs that linear term into
`exp(-(c/2) ‖x‖²)`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace SimplexFull.Covariance

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
/-- `x ↦ exp(-c ‖x‖²)` is Lebesgue-integrable on Euclidean space whenever `c > 0`. -/
theorem integrable_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (-c * ‖x‖ ^ 2)) volume := by
  have hb : 0 < (c : ℂ).re := by simpa using hc
  have hcomplex :
      Integrable (fun v : EuclideanSpace ℝ (Fin m) ↦
        Complex.exp (-(c : ℂ) * ‖v‖ ^ 2 + (0 : ℂ) * ⟪(0 : EuclideanSpace ℝ (Fin m)), v⟫))
        volume :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb (0 : ℂ) 0
  refine hcomplex.norm.congr (ae_of_all _ fun x ↦ ?_)
  dsimp
  rw [inner_zero_left, zero_mul, add_zero, Complex.norm_exp]
  simp [pow_two, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]

omit m [NeZero m] in
/-- Scalar completing-the-square bound, from `(c t - a)² ≥ 0`. -/
lemma linear_sub_sq_le {a c t : ℝ} (hc : 0 < c) :
    a * t - c * t ^ 2 ≤ a ^ 2 / (2 * c) - (c / 2) * t ^ 2 := by
  have h2c : 0 < 2 * c := by positivity
  have hnonneg : 0 ≤ a ^ 2 - c ^ 2 * t ^ 2 - (a * t - c * t ^ 2) * (2 * c) := by
    have heq : a ^ 2 - c ^ 2 * t ^ 2 - (a * t - c * t ^ 2) * (2 * c) =
        (c * t - a) ^ 2 := by ring
    rw [heq]
    exact sq_nonneg _
  have hmul : (a * t - c * t ^ 2) * (2 * c) ≤ a ^ 2 - c ^ 2 * t ^ 2 :=
    sub_nonneg.mp hnonneg
  have hdiv : a * t - c * t ^ 2 ≤ (a ^ 2 - c ^ 2 * t ^ 2) / (2 * c) :=
    (le_div_iff₀ h2c).mpr hmul
  have hid : (a ^ 2 - c ^ 2 * t ^ 2) / (2 * c) =
      a ^ 2 / (2 * c) - (c / 2) * t ^ 2 := by
    field
  linarith

omit m [NeZero m] in
lemma exp_linear_sub_sq_le {a c t : ℝ} (hc : 0 < c) :
    Real.exp (a * t - c * t ^ 2) ≤
      Real.exp (a ^ 2 / (2 * c)) * Real.exp (-(c / 2) * t ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  simpa [sub_eq_add_neg, neg_mul] using linear_sub_sq_le (a := a) (c := c) (t := t) hc

omit [NeZero m] in
lemma norm_pow_le_factorial_mul_exp (x : EuclideanSpace ℝ (Fin m)) (n : ℕ) :
    ‖x‖ ^ n ≤ ((Nat.factorial n) : ℝ) * Real.exp ‖x‖ := by
  have hdiv : ‖x‖ ^ n / ((Nat.factorial n) : ℝ) ≤ Real.exp ‖x‖ :=
    Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) n
  have hmul : ‖x‖ ^ n ≤ Real.exp ‖x‖ * ((Nat.factorial n) : ℝ) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < ((Nat.factorial n) : ℝ))).mp hdiv
  simpa [mul_comm] using hmul

/-- The attained coordinate maximum satisfies `|maxCoord x| ≤ ‖x‖`. -/
lemma abs_maxCoord_le_norm (x : EuclideanSpace ℝ (Fin m)) :
    |SimplexFull.maxCoord x| ≤ ‖x‖ := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
      (H := SimplexFull.univNonempty (m := m)) (fun i ↦ x i)
  have hcoord : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  simpa [SimplexFull.maxCoord, hi] using hcoord

lemma mul_maxCoord_le_abs_mul_norm (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    lam * SimplexFull.maxCoord x ≤ |lam| * ‖x‖ := by
  calc
    lam * SimplexFull.maxCoord x ≤ |lam * SimplexFull.maxCoord x| := le_abs_self _
    _ = |lam| * |SimplexFull.maxCoord x| := abs_mul _ _
    _ ≤ |lam| * ‖x‖ :=
      mul_le_mul_of_nonneg_left (abs_maxCoord_le_norm x) (abs_nonneg _)

/-- Pointwise Gaussian domination of the polynomial-exponential integrand. -/
lemma norm_pow_exp_max_mul_gaussian_le (n : ℕ) (lam : ℝ) {c : ℝ} (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖x‖ ^ n * Real.exp (lam * SimplexFull.maxCoord x) * Real.exp (-c * ‖x‖ ^ 2) ≤
      ((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) ^ 2 / (2 * c)) *
        Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  have hpow : ‖x‖ ^ n ≤ ((Nat.factorial n) : ℝ) * Real.exp ‖x‖ := norm_pow_le_factorial_mul_exp x n
  have hexp : Real.exp (lam * SimplexFull.maxCoord x) ≤ Real.exp (|lam| * ‖x‖) :=
    Real.exp_le_exp.mpr (mul_maxCoord_le_abs_mul_norm lam x)
  have hmul : ‖x‖ ^ n * Real.exp (lam * SimplexFull.maxCoord x) ≤
      (((Nat.factorial n) : ℝ) * Real.exp ‖x‖) * Real.exp (|lam| * ‖x‖) :=
    mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
  have htail :
      ‖x‖ ^ n * Real.exp (lam * SimplexFull.maxCoord x) * Real.exp (-c * ‖x‖ ^ 2) ≤
        (((Nat.factorial n) : ℝ) * Real.exp ‖x‖) * Real.exp (|lam| * ‖x‖) *
          Real.exp (-c * ‖x‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
  have hrewrite :
      (((Nat.factorial n) : ℝ) * Real.exp ‖x‖) * Real.exp (|lam| * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2) =
        ((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) * ‖x‖ - c * ‖x‖ ^ 2) := by
    calc
      (((Nat.factorial n) : ℝ) * Real.exp ‖x‖) * Real.exp (|lam| * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)
          = ((Nat.factorial n) : ℝ) * (Real.exp ‖x‖ * Real.exp (|lam| * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)) := by
            ring
      _ = ((Nat.factorial n) : ℝ) * (Real.exp (‖x‖ + |lam| * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)) := by
            rw [← Real.exp_add]
      _ = ((Nat.factorial n) : ℝ) * Real.exp (‖x‖ + |lam| * ‖x‖ + (-c * ‖x‖ ^ 2)) := by
            rw [← Real.exp_add]
      _ = ((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) * ‖x‖ - c * ‖x‖ ^ 2) := by
            congr 1
            apply congrArg Real.exp
            ring
  have hsq := exp_linear_sub_sq_le (a := 1 + |lam|) hc (t := ‖x‖)
  have hscaled :
      ((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) * ‖x‖ - c * ‖x‖ ^ 2) ≤
        ((Nat.factorial n) : ℝ) *
          (Real.exp ((1 + |lam|) ^ 2 / (2 * c)) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hconst :
      ((Nat.factorial n) : ℝ) *
          (Real.exp ((1 + |lam|) ^ 2 / (2 * c)) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) =
        ((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) ^ 2 / (2 * c)) *
          Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    ring
  exact le_trans (le_trans (le_trans htail (le_of_eq hrewrite)) hscaled) (le_of_eq hconst)

lemma continuous_norm_pow_exp_max_mul_gaussian (n : ℕ) (lam c : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦
      ‖x‖ ^ n * Real.exp (lam * SimplexFull.maxCoord x) * Real.exp (-c * ‖x‖ ^ 2)) := by
  have hnorm : Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦ ‖x‖) := continuous_norm
  have hpow : Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦ ‖x‖ ^ n) := hnorm.pow n
  have hmax : Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦
      Real.exp (lam * SimplexFull.maxCoord x)) :=
    Real.continuous_exp.comp (continuous_const.mul SimplexFull.continuous_maxCoord)
  have hgauss : Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (-c * ‖x‖ ^ 2)) :=
    Real.continuous_exp.comp
      (show Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦ (-c) * ‖x‖ ^ 2) from
        continuous_const.mul (hnorm.pow 2))
  exact (hpow.mul hmax).mul hgauss

/-- `‖x‖^n exp(λ maxCoord x) exp(-c ‖x‖²)` is Lebesgue-integrable for every `c > 0`. -/
theorem integrable_norm_pow_exp_max_mul_gaussian (n : ℕ) (lam : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
      ‖x‖ ^ n * Real.exp (lam * SimplexFull.maxCoord x) *
        Real.exp (-c * ‖x‖ ^ 2)) volume := by
  have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦
      ((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) ^ 2 / (2 * c)) *
        Real.exp (-(c / 2) * ‖x‖ ^ 2)) volume := by
    simpa [mul_assoc] using
      (integrable_exp_neg_mul_sq_norm (half_pos hc)).const_mul
        (((Nat.factorial n) : ℝ) * Real.exp ((1 + |lam|) ^ 2 / (2 * c)))
  refine hdom.mono' (continuous_norm_pow_exp_max_mul_gaussian n lam c).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
  have hnn : 0 ≤ ‖x‖ ^ n * Real.exp (lam * SimplexFull.maxCoord x) *
      Real.exp (-c * ‖x‖ ^ 2) := by positivity
  rw [Real.norm_of_nonneg hnn]
  exact norm_pow_exp_max_mul_gaussian_le n lam hc x

#print axioms integrable_exp_neg_mul_sq_norm
#print axioms integrable_norm_pow_exp_max_mul_gaussian

end SimplexFull.Covariance
