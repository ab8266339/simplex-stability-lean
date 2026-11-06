import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average
import SimplexFull.GaussianDensityIntegrals
import SimplexFull.GlobalMeanWidthBase
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace SimplexFull.SphereGaussian
abbrev Space (d : Nat) := EuclideanSpace Real (Fin d)
abbrev Sphere (d : Nat) := Metric.sphere (0 : Space d) 1
variable {d : Nat} [NeZero d]

/-- Actual polar change of variables for ambient Euclidean volume. -/
theorem integral_polar (f : Space d → Real) :
    (∫ x, f x) = ∫ p : Sphere d × Ioi (0:Real), f (p.2.val • p.1.val)
      ∂(volume : Measure (Space d)).toSphere.prod (Measure.volumeIoiPow (d-1)) := by
  let H := homeomorphUnitSphereProd (Space d)
  calc
    (∫ x, f x) = ∫ x : ({(0 : Space d)}ᶜ : Set (Space d)), f x.val
        ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton]
    _ = ∫ p : Sphere d × Ioi (0:Real), f ((H.symm p).val)
        ∂(volume : Measure (Space d)).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank Real (Space d)-1)) := by
      simpa only [H, Function.comp_def, Homeomorph.symm_apply_apply] using
        (volume : Measure (Space d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ H.symm)
    _ = _ := by
      simp [H, homeomorphUnitSphereProd_symm_apply_coe, Space]

def radialDensity (d : Nat) (r : Real) : Real :=
  (Real.sqrt ((2*Real.pi)^d))⁻¹ * Real.exp (-(r^2)/2)

def radialFirstMoment (d : Nat) : Real :=
  ∫ r : Ioi (0:Real), radialDensity d r.val*r.val ∂Measure.volumeIoiPow (d-1)

theorem rho_one_radial (x : Space d) :
    Covariance.rho (1 : Matrix (Fin d) (Fin d) Real) x = radialDensity d ‖x‖ := by
  simp [Covariance.rho, Covariance.matrix_inv_one, Covariance.quad_one, radialDensity]


/-- Angular-radial separation for every positively one-homogeneous function. -/
theorem gaussian_integral_homogeneous (f : Space d → Real)
    (hhom : ∀ r : Real, 0≤r → ∀ x, f (r • x)=r*f x) :
    (∫ x, f x ∂stdGaussian (Space d)) =
      (∫ u : Sphere d, f u.val ∂(volume : Measure (Space d)).toSphere)*radialFirstMoment d := by
  rw [Covariance.integral_stdGaussian_eq_rho_one, integral_polar]
  have hp : (fun p : Sphere d × Ioi (0:Real) =>
      Covariance.rho (1 : Matrix (Fin d) (Fin d) Real) (p.2.val • p.1.val)*f (p.2.val • p.1.val)) =
      (fun p : Sphere d × Ioi (0:Real) => f p.1.val*(radialDensity d p.2.val*p.2.val)) := by
    funext p
    have hu : ‖p.1.val‖=1 := mem_sphere_zero_iff_norm.mp p.1.property
    have hr : 0<p.2.val := p.2.property
    rw [rho_one_radial, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one,
      hhom _ hr.le]
    ring
  rw [hp]
  simpa only [radialFirstMoment] using
    (integral_prod_mul (μ := (volume : Measure (Space d)).toSphere)
      (ν := Measure.volumeIoiPow (d-1)) (fun u : Sphere d => f u.val)
      (fun r : Ioi (0:Real) => radialDensity d r.val*r.val))

#print axioms integral_polar
#print axioms gaussian_integral_homogeneous
end SimplexFull.SphereGaussian
