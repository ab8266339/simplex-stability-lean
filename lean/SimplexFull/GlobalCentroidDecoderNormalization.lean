import SimplexFull.GlobalCentroidConstants
import SimplexFull.GlobalGaussianNormalization
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SimplexFull.GlobalTail
variable {m : Nat} [NeZero m]

theorem normalizedCovariance_simplexGram (hm : 2≤m) :
    normalizedCovariance (Geometry.simplexGram m) =
      (1 : Matrix (Fin m) (Fin m) Real) := by
  unfold normalizedCovariance Geometry.simplexGram
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (GlobalCentroid.alpha_pos hm)), one_smul]
  exact sub_add_cancel _ _

theorem simplexGram_isCorrelation (hm : 2≤m) :
    WeakSimplex.IsCorrelation (Geometry.simplexGram m) :=
  ⟨simplexGram_posSemidef, Geometry.simplexGram_diagonal m (by omega)⟩

theorem decodingSuccess_normalizedCovariance (hm : 2≤m)
    (G : Matrix (Fin m) (Fin m) Real) (hG : WeakSimplex.IsCorrelation G) (lam : Real) :
    decodingSuccess G lam = decodingSuccess (normalizedCovariance G)
      (lam/Real.sqrt (Geometry.alpha m)) := by
  have hh := WeakSimplex.gramMgf_normalization_identity (show 1<m by omega) G hG lam
  have he := congrArg (fun z : Real => z/(m:Real)) hh
  simpa only [decodingSuccess, mgf, GlobalFoundation.coordinateMax_eq_maxCoord,
    normalizedCovariance, Geometry.alpha, one_div,
    show WeakSimplex.allOnesMatrix m = Geometry.onesMatrix m from rfl,
    div_mul_eq_mul_div] using he

theorem decodingSuccess_simplex_normalized (hm : 2≤m) (lam : Real) :
    decodingSuccess (Geometry.simplexGram m) lam =
      decodingSuccess (1 : Matrix (Fin m) (Fin m) Real)
        (lam/Real.sqrt (Geometry.alpha m)) := by
  rw [decodingSuccess_normalizedCovariance hm _ (simplexGram_isCorrelation hm),
    normalizedCovariance_simplexGram hm]

#print axioms normalizedCovariance_simplexGram
#print axioms decodingSuccess_normalizedCovariance
end SimplexFull.GlobalTail
