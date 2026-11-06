import WeakSimplexConjectureLean.Normal.TiltFunctions
import WeakSimplexConjectureLean.Coding.RegularSimplex
import SimplexFull.GaussianBase
import SimplexFull.Decoder

/-!
Definition bridges to the separately verified weak-simplex library, and its
actual Gaussian decoding comparison. These are qualitative consequences only;
they do not assert the new quantitative global constants.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SimplexFull.GlobalFoundation

theorem normalPDF_eq_phi : WeakSimplex.normalPDF = SimplexFull.phi := rfl
theorem normalCDF_eq_Phi : WeakSimplex.normalCDF = SimplexFull.Phi := rfl
theorem millsRatio_eq_q : WeakSimplex.r = SimplexFull.q := rfl
theorem tiltedMean_eq_h : WeakSimplex.H = SimplexFull.h := rfl
theorem localLogMass_eq_pullback (s : ℝ) :
    WeakSimplex.localLogMass s = Real.log (SimplexFull.Phi s) + SimplexFull.q s ^ 2 / 2 := rfl

theorem coordinateMax_eq_maxCoord {m : ℕ} [NeZero m] (hm : 0 < m) :
    WeakSimplex.coordinateMax hm = (SimplexFull.maxCoord : EuclideanSpace ℝ (Fin m) → ℝ) := rfl

theorem decodingSuccess_eq_weak_mgf {m : ℕ} [NeZero m] (hm : 0 < m)
    (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ) :
    SimplexFull.decodingSuccess G lam =
      Real.exp (-(lam ^ 2)/2)/(m : ℝ) *
        mgf (WeakSimplex.coordinateMax hm) (multivariateGaussian 0 G) lam := rfl

theorem regularSimplexGram_eq_simplexGram (m : ℕ) :
    WeakSimplex.regularSimplexGram m = Geometry.simplexGram m := by
  simp only [WeakSimplex.regularSimplexGram, Geometry.simplexGram,
    Geometry.alpha, Geometry.centering, WeakSimplex.allOnesMatrix,
    Geometry.onesMatrix, inv_div, one_div]
  rfl

theorem gram_isCorrelation {m d : ℕ} (X : Geometry.Config m d)
    (hX : Geometry.UnitConfig X) : WeakSimplex.IsCorrelation (Geometry.gram X) :=
  ⟨Geometry.gram_posSemidef X, Geometry.gram_diagonal_unit X hX⟩

/-- Actual multivariate-Gaussian decoding objective is maximized at the simplex
for every correlation Gram and nonnegative signal parameter. -/
theorem decodingSuccess_le_simplex_of_isCorrelation {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : WeakSimplex.IsCorrelation G) (lam : ℝ) (hlam : 0 ≤ lam) :
    SimplexFull.decodingSuccess G lam ≤
      SimplexFull.decodingSuccess (Geometry.simplexGram m) lam := by
  have hm1 : 1 < m := by omega
  have hcmp := WeakSimplex.gramGaussianMax_mgf_le_regularSimplex hm1 G hG lam hlam
  rw [regularSimplexGram_eq_simplexGram] at hcmp
  rw [decodingSuccess_eq_weak_mgf (Nat.zero_lt_of_lt hm1),
    decodingSuccess_eq_weak_mgf (Nat.zero_lt_of_lt hm1)]
  exact mul_le_mul_of_nonneg_left hcmp
    (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg m))

/-- Qualitative weak-simplex bound for every unit configuration, including
arbitrary ambient dimension and singular Grams. -/
theorem decodingSuccess_gram_le_simplex {m d : ℕ} [NeZero m]
    (hm : 2 ≤ m) (X : Geometry.Config m d) (hX : Geometry.UnitConfig X)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    SimplexFull.decodingSuccess (Geometry.gram X) lam ≤
      SimplexFull.decodingSuccess (Geometry.simplexGram m) lam :=
  decodingSuccess_le_simplex_of_isCorrelation hm _ (gram_isCorrelation X hX) lam hlam

#print axioms normalPDF_eq_phi
#print axioms normalCDF_eq_Phi
#print axioms millsRatio_eq_q
#print axioms tiltedMean_eq_h
#print axioms localLogMass_eq_pullback
#print axioms coordinateMax_eq_maxCoord
#print axioms decodingSuccess_eq_weak_mgf
#print axioms regularSimplexGram_eq_simplexGram
#print axioms gram_isCorrelation
#print axioms decodingSuccess_le_simplex_of_isCorrelation
#print axioms decodingSuccess_gram_le_simplex
end SimplexFull.GlobalFoundation
