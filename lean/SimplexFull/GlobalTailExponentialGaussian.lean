import SimplexFull.GlobalTailExponential
import SimplexFull.Decoder
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SimplexFull.GlobalTail

/-- Exact exponential window weight appearing in the global decoder constants. -/
def expWindowWeight (m : Nat) (a : Real) : Real :=
  Real.exp (-(a^2)/2)*(Real.exp a-1)/(m:Real)

theorem expWindowWeight_pos {m : Nat} (hm : 0<m) {a : Real} (ha : 0<a) :
    0<expWindowWeight m a := by
  unfold expWindowWeight
  exact div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.one_lt_exp_iff.mpr ha)))
    (by exact_mod_cast hm)

variable {m : Nat} [NeZero m]

theorem gaussian_exp_gap_ge_of_cdf (R S : Matrix (Fin m) (Fin m) Real)
    (hR : R.PosSemidef) (hS : S.PosSemidef) {a : Real} (ha : 0<a)
    (hdom : ∀ t, (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) S).real
      {x | maxCoord x ≤ t} ≤ (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) R).real
      {x | maxCoord x ≤ t}) {A : Real}
    (hl : ∀ t ∈ Icc (0:Real) 1, A ≤
      (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) R).real {x | maxCoord x ≤ t} -
      (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) S).real {x | maxCoord x ≤ t}) :
    A*(Real.exp a-1) ≤
      (∫ x, Real.exp (a*maxCoord x) ∂multivariateGaussian (0 : EuclideanSpace Real (Fin m)) S) -
      (∫ x, Real.exp (a*maxCoord x) ∂multivariateGaussian (0 : EuclideanSpace Real (Fin m)) R) :=
  exp_integral_difference_ge_of_cdf_gap measurable_maxCoord ha
    (integrable_exp_mul_maxCoord R hR a) (integrable_exp_mul_maxCoord S hS a) hdom hl

theorem decodingSuccess_gap_ge_of_cdf (R S : Matrix (Fin m) (Fin m) Real)
    (hR : R.PosSemidef) (hS : S.PosSemidef) {a : Real} (ha : 0<a)
    (hdom : ∀ t, (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) S).real
      {x | maxCoord x ≤ t} ≤ (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) R).real
      {x | maxCoord x ≤ t}) {A : Real}
    (hl : ∀ t ∈ Icc (0:Real) 1, A ≤
      (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) R).real {x | maxCoord x ≤ t} -
      (multivariateGaussian (0 : EuclideanSpace Real (Fin m)) S).real {x | maxCoord x ≤ t}) :
    expWindowWeight m a*A ≤ decodingSuccess S a-decodingSuccess R a := by
  have hh := gaussian_exp_gap_ge_of_cdf R S hR hS ha hdom hl
  have hmul := mul_le_mul_of_nonneg_left hh
    (div_nonneg (Real.exp_pos (-(a^2)/2)).le (Nat.cast_nonneg m))
  unfold expWindowWeight decodingSuccess
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith only [hmul]

#print axioms gaussian_exp_gap_ge_of_cdf
#print axioms decodingSuccess_gap_ge_of_cdf
end SimplexFull.GlobalTail
