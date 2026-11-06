import SimplexFull.GlobalComparisonWitness
import SimplexFull.GlobalComparisonTilt
import SimplexFull.GlobalComparisonConstants
noncomputable section
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators
namespace SimplexFull.GlobalComparison

def witnessMass {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) : ℝ :=
  Real.exp (GlobalScalar.psiPull (w.s i))
def witnessFactor {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) : ℝ → ℝ :=
  normalizedTilt (w.a i) (h (w.s i)) (witnessMass w i)
def witnessQ0 {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : ℝ :=
  ∫ x, ∏ i, witnessFactor w i (x i) ∂multivariateGaussian (0 : Coord m) R
def witnessQ1 {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : ℝ :=
  ∫ x, ∏ i, normalizedSelfConvolution (witnessFactor w i) (x i)
    ∂multivariateGaussian (0 : Coord m) R

theorem witnessMass_pos {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) : 0 < witnessMass w i := Real.exp_pos _
theorem witnessMass_le_one {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) : witnessMass w i ≤ 1 :=
  Real.exp_le_one_iff.mpr (GlobalScalar.psiPull_neg _).le

theorem integral_witness_tilt {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) (i : Fin m) :
    (∫ x, tiltedHalfLine (w.a i) (h (w.s i)) x ∂gaussianReal 0 1) = witnessMass w i := by
  rw [w.a_eq_r]
  change (∫ x, centeredTiltedHalfLine (w.s i) x ∂gaussianReal 0 1) = _
  rw [integral_centeredTiltedHalfLine]
  dsimp [witnessMass, GlobalScalar.psiPull]
  rw [Real.exp_add, Real.exp_log (Phi_pos _), GlobalFoundation.millsRatio_eq_q, GlobalFoundation.normalCDF_eq_Phi]
  ring

theorem witnessQ1_ge_one {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (hR : IsCorrelation R) (w : AdaptiveWitnesses R c) : 1 ≤ witnessQ1 w := by
  have hc (i : Fin m) :
      (∫ x, x*tiltedHalfLine (w.a i) (h (w.s i)) x ∂gaussianReal 0 1)=0 := by
    rw [w.a_eq_r]
    exact integral_mul_centeredTiltedHalfLine (w.s i)
  have hh := normalizedSelfConvolution_product_ge_one R hR
    (fun i => w.a i) (fun i => h (w.s i)) w.a_pos hc
  dsimp only at hh
  simp only [integral_witness_tilt w] at hh
  exact hh

theorem witnessQ0_nonneg {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : 0 ≤ witnessQ0 w :=
  integral_nonneg fun x => Finset.prod_nonneg fun i _ =>
    normalizedTilt_nonneg (witnessMass_pos w i) _

theorem orthantMass_eq_witness {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (hR : R.PosSemidef) (w : AdaptiveWitnesses R c) :
    orthantMass R c = Real.exp (witnessValue w) * witnessQ0 w := by
  classical
  have hf (i : Fin m) (x : ℝ) :
      centeredTiltedHalfLine (w.s i) x = witnessMass w i * witnessFactor w i x := by
    dsimp [witnessFactor,normalizedTilt]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (witnessMass_pos w i)), one_mul, w.a_eq_r]
    rfl
  have hi :
      (∫ x, ∏ i, centeredTiltedHalfLine (w.s i) (x i)
        ∂multivariateGaussian (0 : Coord m) R) =
      Real.exp (∑ i, GlobalScalar.psiPull (w.s i))*witnessQ0 w := by
    simp_rw [hf, Finset.prod_mul_distrib]
    rw [integral_const_mul]
    congr 1
    exact (Real.exp_sum Finset.univ (fun i => GlobalScalar.psiPull (w.s i))).symm
  rw [orthantMass, GlobalWitness.orthant_mass_eq_tilted_product hR w, hi, ← mul_assoc,
    ← Real.exp_add]
  congr 1
  congr 1
  dsimp [witnessValue]
  ring

theorem witnessValue_exp_lower {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : AdaptiveWitnesses R c) : (Phi c)^m ≤ Real.exp (witnessValue w) := by
  have hh := Real.exp_le_exp.mpr (witnessValue_lower w)
  simpa only [logFloor, Real.exp_nat_mul, Real.exp_log (Phi_pos c)] using hh

theorem witness_doubling_lower {m : ℕ} (hm : 2 ≤ m)
    {R : Matrix (Fin m) (Fin m) ℝ} {c u v : ℝ}
    (hR : IsCorrelation R) (hne : R ≠ 1) (w : AdaptiveWitnesses R c)
    (huc : u ≤ c) (hcv : c ≤ v) :
    paperK m u v * covarianceDefect R ≤ witnessQ0 w^2 - witnessQ1 w := by
  rw [paperK_factorization hm]
  exact tilt_doubling_lower hm R hR hne (fun i => w.a i)
    (fun i => h (w.s i)) (witnessMass w) (fun i => (w.a_pos i).le)
    (witness_a_le (by omega) hR.1 w huc) (witnessMass_pos w) (witnessMass_le_one w)
    (beta_pos m u) (witness_beta_le (by omega) hR.1 w huc)
    (witness_threshold_le (by omega) hR w huc hcv)

#print axioms witnessQ1_ge_one
#print axioms orthantMass_eq_witness
#print axioms witness_doubling_lower
end SimplexFull.GlobalComparison
