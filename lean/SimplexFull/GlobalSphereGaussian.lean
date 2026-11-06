import SimplexFull.GlobalSphereGaussianPolar
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace SimplexFull.SphereGaussian
variable {d : Nat} [NeZero d]

def sphereMass (d : Nat) : Real :=
  (volume : Measure (Space d)).toSphere.real univ

/-- The genuine probability-normalized surface measure, not a Gaussian-ratio definition. -/
def normalizedSphereMeasure (d : Nat) : Measure (Sphere d) :=
  ((volume : Measure (Space d)).toSphere univ)⁻¹ •
    (volume : Measure (Space d)).toSphere

theorem sphere_mass_ne_zero :
    (volume : Measure (Space d)).toSphere univ ≠ 0 :=
  by simpa only [ne_eq, Measure.measure_univ_eq_zero] using
    (Measure.toSphere_ne_zero (volume : Measure (Space d)))

theorem sphereMass_pos : 0<sphereMass d :=
  ENNReal.toReal_pos sphere_mass_ne_zero (measure_ne_top _ _)

instance normalizedSphereMeasure_isProbability :
    IsProbabilityMeasure (normalizedSphereMeasure d) where
  measure_univ := by
    unfold normalizedSphereMeasure
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel sphere_mass_ne_zero (measure_ne_top _ _)

theorem gaussianRadiusMean_eq_sphere_mass_mul_radial :
    Geometry.gaussianRadiusMean d = sphereMass d*radialFirstMoment d := by
  have hh := gaussian_integral_homogeneous (d:=d) (fun x => ‖x‖) (by
    intro r hr x
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr])
  have hs : (fun u : Sphere d => ‖u.val‖) = (fun _ => (1:Real)) := by
    funext u
    exact mem_sphere_zero_iff_norm.mp u.property
  rw [hs, integral_const] at hh
  simpa only [smul_eq_mul, mul_one, Geometry.gaussianRadiusMean, sphereMass] using hh

/-- Actual normalized surface average equals the Gaussian average divided by mean radius. -/
theorem sphere_integral_eq_gaussian_ratio (f : Space d → Real)
    (hhom : ∀ r : Real, 0≤r → ∀ x, f (r • x)=r*f x) :
    (∫ u : Sphere d, f u.val ∂normalizedSphereMeasure d) =
      (∫ x, f x ∂stdGaussian (Space d))/Geometry.gaussianRadiusMean d := by
  rw [normalizedSphereMeasure, integral_smul_measure, ENNReal.toReal_inv]
  change (sphereMass d)⁻¹*(∫ u : Sphere d, f u.val ∂(volume : Measure (Space d)).toSphere)=_
  apply (eq_div_iff (Geometry.gaussianRadiusMean_pos (show 1≤d by have := NeZero.pos d; omega)).ne').mpr
  rw [gaussianRadiusMean_eq_sphere_mass_mul_radial, gaussian_integral_homogeneous f hhom]
  field_simp [ne_of_gt (sphereMass_pos (d:=d))]

#print axioms normalizedSphereMeasure_isProbability
#print axioms sphere_integral_eq_gaussian_ratio
end SimplexFull.SphereGaussian
