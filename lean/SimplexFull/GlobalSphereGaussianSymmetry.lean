import SimplexFull.GlobalSphereGaussianWidth
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SimplexFull.SphereGaussian
variable {d : Nat} [NeZero d]

theorem gaussian_integral_neg_eq (f : Space d → Real) (hf : Continuous f) :
    (∫ x, f (-x) ∂stdGaussian (Space d)) = ∫ x, f x ∂stdGaussian (Space d) := by
  have hmap : (stdGaussian (Space d)).map (fun x : Space d => -x) = stdGaussian (Space d) := by
    simpa only [LinearIsometryEquiv.coe_neg] using
      stdGaussian_map (LinearIsometryEquiv.neg Real : Space d ≃ₗᵢ[Real] Space d)
  calc
    _ = ∫ x, f x ∂(stdGaussian (Space d)).map (fun x : Space d => -x) := by
      rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = _ := by rw [hmap]

variable {m : Nat} [NeZero m]

theorem sphere_support_neg_integral (X : Geometry.Config m d) :
    (∫ u : Sphere d, Geometry.realSupport (convexHull Real (range X)) (-u.val)
      ∂normalizedSphereMeasure d) =
    ∫ u : Sphere d, Geometry.realSupport (convexHull Real (range X)) u.val
      ∂normalizedSphereMeasure d := by
  have hhom : ∀ r : Real, 0≤r → ∀ x : Space d,
      Geometry.realSupport (convexHull Real (range X)) (-(r • x)) =
        r * Geometry.realSupport (convexHull Real (range X)) (-x) := by
    intro r hr x
    rw [← smul_neg, finiteHullSupport_homogeneous X r hr]
  rw [sphere_integral_eq_gaussian_ratio
    (fun x : Space d => Geometry.realSupport (convexHull Real (range X)) (-x)) hhom,
    sphere_integral_eq_gaussian_ratio _ (finiteHullSupport_homogeneous X),
    gaussian_integral_neg_eq _ (Geometry.continuous_realSupport_convexHull_range X)]

/-- Mean width in the conventional direction-width form hK(u)+hK(-u). -/
def widthIntegral {d : Nat} (K : Set (Space d)) : Real :=
  ∫ u : Sphere d, (Geometry.realSupport K u.val + Geometry.realSupport K (-u.val))
    ∂normalizedSphereMeasure d

theorem widthIntegral_convexHull_eq_meanWidth (X : Geometry.Config m d) :
    widthIntegral (convexHull Real (range X)) = meanWidth (convexHull Real (range X)) := by
  have hneg : Integrable
      (fun u : Sphere d => Geometry.realSupport (convexHull Real (range X)) (-u.val))
      (normalizedSphereMeasure d) := by
    have hc : Continuous
        (fun u : Sphere d => Geometry.realSupport (convexHull Real (range X)) (-u.val)) :=
      (Geometry.continuous_realSupport_convexHull_range X).comp continuous_subtype_val.neg
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [widthIntegral, integral_add (integrable_finiteHullSupport_sphere X) hneg,
    sphere_support_neg_integral, meanWidth]
  ring

#print axioms gaussian_integral_neg_eq
#print axioms sphere_support_neg_integral
#print axioms widthIntegral_convexHull_eq_meanWidth
end SimplexFull.SphereGaussian
