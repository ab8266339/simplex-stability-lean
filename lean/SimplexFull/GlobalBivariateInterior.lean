import SimplexFull.GlobalBivariateProbability
import SimplexFull.GlobalBivariateEstimate
import SimplexFull.Benchmark

noncomputable section
open MeasureTheory Set Real Filter ProbabilityTheory WeakSimplex
open scoped Topology Interval ENNReal
namespace SimplexFull.GlobalBivariate

theorem pair_correlation_abs_le_one
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.PosSemidef)
    (hdiag : ∀ i,R i i=1) : |R 0 1|≤1 := by
  have hv := variance_nonneg (fun x : Coord 2 => x 0-R 0 1*x 1)
    (multivariateGaussian (0 : Coord 2) R)
  rw [GlobalRectangle.variance_pair_residual hR hdiag] at hv
  nlinarith [sq_abs (R 0 1),abs_nonneg (R 0 1)]

theorem slab_toReal_eq {ell : ℝ} (hell : 0≤ell) :
    (gaussianReal 0 1 (Icc (-ell) ell)).toReal = 2*Phi ell-1 := by
  rw [gaussianReal_Icc_eq_Phi (-ell) ell (by linarith),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (Phi_monotone (by linarith : -ell≤ell)))]
  linarith [Phi_add_Phi_neg ell]

theorem pair_rectangle_gap_interior
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.PosSemidef)
    (hdiag : ∀ i,R i i=1) (r : Fin 2→ℝ) {ell T : ℝ}
    (hell : 0<ell) (hrlo : ∀ i,ell≤r i) (hrhi : ∀ i,r i≤T)
    (hcorr : |R 0 1|<1) :
    ell^2/(4*Real.pi)*Real.exp (-4*T^2/3)*(R 0 1)^2 ≤
      (multivariateGaussian (0 : Coord 2) R (symmetricRectangle r)).toReal -
        (gaussianReal 0 1 (Icc (-r 0) (r 0))*
         gaussianReal 0 1 (Icc (-r 1) (r 1))).toReal := by
  rw [pair_probability_eq_rectangleIntegral hR hdiag r
    (fun i => hell.le.trans (hrlo i)) hcorr,
    ←rectangleIntegral_zero_eq_product (hell.le.trans (hrlo 0)) (hell.le.trans (hrlo 1))]
  exact rectangleIntegral_gap hcorr hell (hrlo 0) (hrlo 1) (hrhi 0) (hrhi 1)

#print axioms pair_correlation_abs_le_one
#print axioms slab_toReal_eq
#print axioms pair_rectangle_gap_interior
end SimplexFull.GlobalBivariate
