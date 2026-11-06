import SimplexFull.GlobalBivariateInterior
import SimplexFull.GlobalBivariateEndpoint
import SimplexFull.GlobalRectangleAssembly

noncomputable section
open MeasureTheory Set Real Filter ProbabilityTheory WeakSimplex
open scoped Topology Interval ENNReal
namespace SimplexFull.GlobalBivariate

/-- The original explicit pair rate, for every PSD unit-diagonal covariance,
including both singular correlation endpoints. -/
theorem pair_rectangle_gap
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.PosSemidef)
    (hdiag : ∀ i,R i i=1) (r : Fin 2→ℝ) {ell T : ℝ}
    (hell : 0<ell) (hrlo : ∀ i,ell≤r i) (hrhi : ∀ i,r i≤T) :
    ell^2/(4*Real.pi)*Real.exp (-4*T^2/3)*(R 0 1)^2 ≤
      (multivariateGaussian (0 : Coord 2) R (symmetricRectangle r)).toReal -
        (gaussianReal 0 1 (Icc (-r 0) (r 0))*
         gaussianReal 0 1 (Icc (-r 1) (r 1))).toReal := by
  rcases (pair_correlation_abs_le_one hR hdiag).lt_or_eq with hlt | heq
  · exact pair_rectangle_gap_interior hR hdiag r hell hrlo hrhi hlt
  · have hr0 (i : Fin 2) : 0≤r i := hell.le.trans (hrlo i)
    have hs : (R 0 1)^2=1 := by
      nlinarith [sq_abs (R 0 1)]
    rw [hs,mul_one,pair_endpoint_mass hR hdiag r hr0 heq,
      ←rectangleIntegral_zero_eq_product (hr0 0) (hr0 1)]
    have hsmall := rectangleIntegral_small_gap (r := (1:ℝ)/2) (by norm_num) (by norm_num)
      hell (hrlo 0) (hrlo 1) (hrhi 0) (hrhi 1)
    calc
      ell^2/(4*Real.pi)*Real.exp (-4*T^2/3) =
        ell^2/Real.pi*Real.exp (-4*T^2/3)*((1:ℝ)/2)^2 := by ring
      _ ≤ rectangleIntegral (1/2) (r 0) (r 1)-rectangleIntegral 0 (r 0) (r 1) := hsmall
      _ ≤ _ := sub_le_sub_right (rectangleIntegral_half_le_min_slab r hr0) _

#print axioms pair_rectangle_gap
end SimplexFull.GlobalBivariate

namespace SimplexFull.GlobalRectangle

/-- The paper's exact rectangle coefficient; the slab factor is the actual
standard normal probability b(ell)=2 Phi(ell)-1. -/
def rectangleK (m : ℕ) (ell T : ℝ) : ℝ :=
  ell^2 * Real.exp (-4*T^2/3) * (2*Phi ell-1)^(m-2) /
    (4*Real.pi*(m:ℝ)*((m:ℝ)-1))

/-- Original quantitative rectangle lemma with no analytic or nonsingularity
assumptions: only PSD, unit diagonal, and the stated uniform positive radii. -/
theorem symmetricRectangle_gap {m : ℕ} (hm : 2≤m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) (hdiag : ∀ i,R i i=1)
    (r : Fin m→ℝ) {ell T : ℝ} (hell : 0<ell)
    (hrlo : ∀ i,ell≤r i) (hrhi : ∀ i,r i≤T) :
    rectangleK m ell T * (∑ k,∑ l,((R-1) k l)^2) ≤
    (multivariateGaussian (0 : Coord m) R (symmetricRectangle r)).toReal -
      (∏ i,gaussianReal 0 1 (Icc (-r i) (r i))).toReal := by
  have hh := rectangle_bound_of_pair_bound hm R hR hdiag r hell hrlo hrhi
    (show 0≤ell^2/(4*Real.pi)*Real.exp (-4*T^2/3) by positivity)
    (fun S hS hd s hlo hhi => GlobalBivariate.pair_rectangle_gap hS hd s hell hlo hhi)
  rw [GlobalBivariate.slab_toReal_eq hell.le] at hh
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hn0 : (m:ℝ)≠0 := by linarith
  have hn1 : (m:ℝ)-1≠0 := by linarith
  convert! hh using 1
  unfold rectangleK
  field_simp [Real.pi_ne_zero,hn0,hn1] <;> ring

#print axioms symmetricRectangle_gap
end SimplexFull.GlobalRectangle

namespace SimplexFull.GlobalRectangle

theorem rectangleK_pos {m : ℕ} (hm : 2≤m) {ell T : ℝ} (hell : 0<ell) :
    0<rectangleK m ell T := by
  have hmono : StrictMono Phi := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hasDerivAt_Phi x).deriv]
    exact phi_pos x
  have hp := hmono hell
  have hz := Phi_add_Phi_neg 0
  simp only [neg_zero] at hz
  have hslab : 0<2*Phi ell-1 := by linarith
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith
  unfold rectangleK
  positivity

#print axioms rectangleK_pos
end SimplexFull.GlobalRectangle
