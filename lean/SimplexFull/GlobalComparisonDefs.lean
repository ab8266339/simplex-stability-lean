import SimplexFull.GlobalScalarBounds
import SimplexFull.GlobalCentroidMatrix
import SimplexFull.GlobalWitnessOrthantBound
import SimplexFull.GeometryBase

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
namespace SimplexFull.GlobalComparison

def logFloor (m : ℕ) (u : ℝ) : ℝ := (m : ℝ) * Real.log (Phi u)
def beta (m : ℕ) (u : ℝ) : ℝ := GlobalScalar.psiInv (logFloor m u)
def capA (m : ℕ) (u : ℝ) : ℝ := deriv GlobalScalar.Psi (beta m u)
def capB (m : ℕ) (u v : ℝ) : ℝ :=
  v + Real.sqrt (-2 * logFloor m u / m) +
    Real.sqrt (-2 * (((m : ℝ)-1)/m) * logFloor m u)
def ell (m : ℕ) (u : ℝ) : ℝ := beta m u / Real.sqrt 2
def radiusT (m : ℕ) (u v : ℝ) : ℝ :=
  Real.sqrt 2 * capB m u v + ell m u
def centralMass (t : ℝ) : ℝ := 2 * Phi t - 1
def paperK (m : ℕ) (u v : ℝ) : ℝ :=
  Real.exp (-(m : ℝ) * capA m u * beta m u) *
  (ell m u)^2 * Real.exp (-4*(radiusT m u v)^2/3) *
  (centralMass (ell m u))^(2*m-2) /
  (4*Real.pi*(m : ℝ)*((m : ℝ)-1))
def paperKappa (m : ℕ) (u v : ℝ) : ℝ :=
  (Phi u)^m * paperK m u v /
    (1 + Real.sqrt (1 + paperK m u v * (m : ℝ)*((m : ℝ)-1)))
def orthantMass {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) : ℝ :=
  (multivariateGaussian (0 : WeakSimplex.Coord m) R (WeakSimplex.lowerOrthant c)).toReal
def covarianceDefect {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, ((R-1) i j)^2
def witnessValue {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {c : ℝ}
    (w : WeakSimplex.AdaptiveWitnesses R c) : ℝ :=
  (∑ i, GlobalScalar.psiPull (w.s i)) - WeakSimplex.qform R w.a / 2

theorem logFloor_neg {m : ℕ} (hm : 0 < m) (u : ℝ) : logFloor m u < 0 := by
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hm)
    (Real.log_neg (Phi_pos u) (Phi_lt_one u))

theorem beta_pos (m : ℕ) (u : ℝ) : 0 < beta m u :=
  GlobalScalar.psiInv_pos _
theorem capA_pos (m : ℕ) (u : ℝ) : 0 < capA m u :=
  GlobalScalar.deriv_Psi_pos (beta_pos m u)
theorem capB_pos {m : ℕ} (hm : 0 < m) {u v : ℝ} (huv : u ≤ v) :
    0 < capB m u v :=
  GlobalScalar.threshold_envelope_pos (by exact_mod_cast hm) huv
theorem ell_pos (m : ℕ) (u : ℝ) : 0 < ell m u :=
  div_pos (beta_pos m u) (Real.sqrt_pos.2 (by norm_num))

#print axioms logFloor_neg
#print axioms capB_pos
end SimplexFull.GlobalComparison
