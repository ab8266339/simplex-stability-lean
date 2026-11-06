import SimplexFull.GlobalApplicationsCore
import SimplexFull.GlobalMeanWidth
noncomputable section
open scoped BigOperators
namespace SimplexFull.GlobalApplication
variable {m : Nat} [NeZero m]

/-- Complete Gaussian support-function bounds for arbitrary unit-ball configurations. -/
theorem ball_gaussian_max_bounds {d : Nat} (hm : 2≤m)
    (X V : Geometry.Config m d) (hX : Geometry.BallConfig X)
    (hV : Geometry.gram V = Geometry.simplexGram m) :
    meanGramConstant m * Geometry.frobSq
      (Geometry.gram (Geometry.orthogonalUnitLift X)-Geometry.simplexGram m) ≤
        Geometry.configGaussianMax V-Geometry.configGaussianMax X ∧
    GlobalTail.centroidMeanConstant m *
      (‖∑ i, X i‖^2 + ∑ i, Geometry.energyDeficit X i) ≤
        Geometry.configGaussianMax V-Geometry.configGaussianMax X :=
  Geometry.ball_gaussian_max_bounds_of_unit (unitGaussianMaxBounds hm) X V hX hV

/-- Full original mean-width application with all unit-comparison inputs discharged. -/
theorem ball_mean_width {d : Nat} (hm : 2≤m) (hd : m-1≤d)
    (X V : Geometry.Config m d) (hX : Geometry.BallConfig X)
    (hV : Geometry.gram V = Geometry.simplexGram m) :
    (2/Geometry.gaussianRadiusMean d) *
      (Geometry.alpha m/meanGramConstant m + 1/GlobalTail.centroidMeanConstant m)⁻¹ *
        Geometry.procrustesSq X V ≤
          Geometry.normalizedGaussianWidth V-Geometry.normalizedGaussianWidth X ∧
    (2/Geometry.gaussianRadiusMean d) * GlobalTail.centroidMeanConstant m *
      (∑ i, (1-‖X i‖^2)) ≤
        Geometry.normalizedGaussianWidth V-Geometry.normalizedGaussianWidth X :=
  Geometry.ball_mean_width_of_unit_bounds hm hd (meanGramConstant_pos hm)
    (GlobalTail.centroidMeanConstant_pos hm) (unitGaussianMaxBounds hm) X V hX hV

#print axioms ball_gaussian_max_bounds
#print axioms ball_mean_width
end SimplexFull.GlobalApplication
