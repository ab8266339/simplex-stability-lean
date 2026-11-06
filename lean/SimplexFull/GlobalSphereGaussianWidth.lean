import SimplexFull.GlobalSphereGaussian
import SimplexFull.GlobalFiniteHullSupport
import SimplexFull.GlobalApplicationsMeanWidth
import SimplexFull.GaussianShift
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SimplexFull.SphereGaussian

/-- Standard mean width defined directly by the normalized sphere support integral. -/
def meanWidth {d : Nat} (K : Set (Space d)) : Real :=
  2 * ∫ u : Sphere d, Geometry.realSupport K u.val ∂normalizedSphereMeasure d

variable {m d : Nat} [NeZero m]

theorem integrable_finiteHullSupport_sphere [NeZero d] (X : Geometry.Config m d) :
    Integrable (fun u : Sphere d => Geometry.realSupport (convexHull Real (range X)) u.val)
      (normalizedSphereMeasure d) := by
  have hc : Continuous (fun u : Sphere d => Geometry.realSupport (convexHull Real (range X)) u.val) :=
    (Geometry.continuous_realSupport_convexHull_range X).comp continuous_subtype_val
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem finiteHullSupport_homogeneous (X : Geometry.Config m d)
    (r : Real) (hr : 0≤r) (g : Space d) :
    Geometry.realSupport (convexHull Real (range X)) (r • g) =
      r * Geometry.realSupport (convexHull Real (range X)) g := by
  rw [Geometry.realSupport_convexHull_range, Geometry.realSupport_convexHull_range,
    map_smul, maxCoord_smul_nonneg hr]

theorem meanWidth_convexHull_eq_normalizedGaussianWidth [NeZero d]
    (X : Geometry.Config m d) :
    meanWidth (convexHull Real (range X)) = Geometry.normalizedGaussianWidth X := by
  rw [meanWidth, sphere_integral_eq_gaussian_ratio _ (finiteHullSupport_homogeneous X),
    Geometry.integral_realSupport_convexHull_range]
  unfold Geometry.normalizedGaussianWidth
  ring

/-- The original mean-width stability statement for the actual normalized sphere measure. -/
theorem ball_mean_width (hm : 2≤m) (hd : m-1≤d)
    (X V : Geometry.Config m d) (hX : Geometry.BallConfig X)
    (hV : Geometry.gram V = Geometry.simplexGram m) :
    (2/Geometry.gaussianRadiusMean d) *
      (Geometry.alpha m/GlobalApplication.meanGramConstant m + 1/GlobalTail.centroidMeanConstant m)⁻¹ *
        Geometry.procrustesSq X V ≤
          meanWidth (convexHull Real (range V))-meanWidth (convexHull Real (range X)) ∧
    (2/Geometry.gaussianRadiusMean d) * GlobalTail.centroidMeanConstant m *
      (∑ i, (1-‖X i‖^2)) ≤
        meanWidth (convexHull Real (range V))-meanWidth (convexHull Real (range X)) := by
  letI : NeZero d := ⟨by omega⟩
  rw [meanWidth_convexHull_eq_normalizedGaussianWidth,
    meanWidth_convexHull_eq_normalizedGaussianWidth]
  exact GlobalApplication.ball_mean_width hm hd X V hX hV

#print axioms integrable_finiteHullSupport_sphere
#print axioms meanWidth_convexHull_eq_normalizedGaussianWidth
#print axioms ball_mean_width
end SimplexFull.SphereGaussian
