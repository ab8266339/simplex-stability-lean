import SimplexFull.Orthant
import SimplexFull.LayerCake
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthant product moments

Actual integrals of coordinate products against `rho 1` on
`{x : EuclideanSpace ℝ (Fin m) | ∀ i, x i ≤ c}`.

`EuclideanSpace.equiv` pushes Lebesgue measure onto the coordinate product.
A product of integrable one-dimensional factors therefore integrates as a product,
and `rho 1` times a coordinate monomial is the case `t ↦ t^n φ(t)`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace SimplexFull.Covariance

open SimplexFull

variable {m : ℕ}

/-- Coordinate monomial `∏ i, (x i) ^ (α i)`. -/
def coordMonomial (α : Fin m → ℕ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∏ i, (x i) ^ α i

/-- Closed orthant `{x | ∀ i, x i ≤ c}`. -/
def orthantIic (c : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∀ i, x i ≤ c}

/-- Truncated one-dimensional moment `∫_{(-∞, c]} t^n φ(t) dt`. -/
def moment1D (n : ℕ) (c : ℝ) : ℝ :=
  ∫ t in Iic c, t ^ n * phi t

lemma eucEquiv_apply (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    EuclideanSpace.equiv (Fin m) ℝ x i = x i := by
  rw [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]

lemma orthantIic_eq_preimage (c : ℝ) :
    orthantIic c =
      EuclideanSpace.equiv (Fin m) ℝ ⁻¹' (Set.univ.pi fun _ : Fin m => Iic c) := by
  ext x
  simp only [orthantIic, mem_preimage, mem_univ_pi, mem_Iic, eucEquiv_apply, mem_setOf]

theorem orthantIic_eq_maxCoord_le [NeZero m] (c : ℝ) :
    orthantIic (m := m) c = {x | maxCoord x ≤ c} := by
  ext x
  simp [orthantIic, maxCoord_le_iff]

/-- `EuclideanSpace.equiv` preserves Lebesgue volume onto the coordinate product. -/
theorem measurePreserving_eucEquiv :
    MeasurePreserving (EuclideanSpace.equiv (Fin m) ℝ) :=
  EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)

lemma rho_mul_coordMonomial_comp (α : Fin m → ℕ) :
    (fun x : EuclideanSpace ℝ (Fin m) =>
        rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x) =
      (fun y : Fin m → ℝ => ∏ i, (y i) ^ α i * phi (y i)) ∘
        EuclideanSpace.equiv (Fin m) ℝ := by
  funext x
  calc
    rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x
        = (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)) * (∏ i, (x i) ^ α i) := by
          rw [coordMonomial, rho_one_eq_prod_gaussianPDFReal]
    _ = (∏ i, (x i) ^ α i) * (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)) := mul_comm _ _
    _ = ∏ i, (x i) ^ α i * ProbabilityTheory.gaussianPDFReal 0 1 (x i) := by
          rw [← Finset.prod_mul_distrib]
    _ = ∏ i, (x i) ^ α i * phi (x i) := by
          simp_rw [phi]
    _ = ∏ i, (EuclideanSpace.equiv (Fin m) ℝ x i) ^ α i *
          phi (EuclideanSpace.equiv (Fin m) ℝ x i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [eucEquiv_apply]

/-- Product of integrable one-dimensional factors, integrated on the coordinate orthant. -/
theorem integrableOn_orthant_prod (f : Fin m → ℝ → ℝ) (c : ℝ)
    (hf : ∀ i, IntegrableOn (f i) (Iic c)) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin m) => ∏ i, f i (x i)) (orthantIic c) := by
  have hμ : MeasurePreserving (EuclideanSpace.equiv (Fin m) ℝ) := measurePreserving_eucEquiv
  have hem : MeasurableEmbedding (EuclideanSpace.equiv (Fin m) ℝ) :=
    (MeasurableEquiv.toLp 2 ((Fin m) → ℝ)).symm.measurableEmbedding
  have hg : IntegrableOn (fun y : Fin m → ℝ => ∏ i, f i (y i))
      (Set.univ.pi fun _ : Fin m => Iic c) := by
    rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod hf
  have hint :=
    (hμ.integrableOn_comp_preimage hem (s := Set.univ.pi fun _ : Fin m => Iic c)).2 hg
  rw [orthantIic_eq_preimage]
  refine hint.congr ?_
  exact ae_of_all _ fun x => by simp [Function.comp_apply]

/-- The orthant integral of a coordinate product is the product of the one-dimensional integrals. -/
theorem integral_orthant_prod (f : Fin m → ℝ → ℝ) (c : ℝ)
    (hf : ∀ i, IntegrableOn (f i) (Iic c)) :
    ∫ x in orthantIic c, ∏ i, f i (x i) = ∏ i, ∫ t in Iic c, f i t := by
  have _int := integrableOn_orthant_prod f c hf
  have hμ : MeasurePreserving (EuclideanSpace.equiv (Fin m) ℝ) := measurePreserving_eucEquiv
  have hem : MeasurableEmbedding (EuclideanSpace.equiv (Fin m) ℝ) :=
    (MeasurableEquiv.toLp 2 ((Fin m) → ℝ)).symm.measurableEmbedding
  have hpt : ∀ x, (∏ i, f i (x i)) =
      ∏ i, f i (EuclideanSpace.equiv (Fin m) ℝ x i) := by
    intro x
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [eucEquiv_apply]
  rw [orthantIic_eq_preimage]
  simp_rw [hpt]
  rw [hμ.setIntegral_preimage_emb hem (fun y => ∏ i, f i (y i))
      (Set.univ.pi fun _ : Fin m => Iic c)]
  have hrest :
      (volume : Measure (Fin m → ℝ)).restrict (Set.univ.pi fun _ : Fin m => Iic c) =
        Measure.pi fun _ : Fin m => (volume : Measure ℝ).restrict (Iic c) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  change ∫ y, ∏ i, f i (y i)
      ∂((volume : Measure (Fin m → ℝ)).restrict (Set.univ.pi fun _ : Fin m => Iic c)) = _
  rw [hrest]
  exact integral_fintype_prod_eq_prod f

/-- `rho 1` times every coordinate monomial is integrable on Euclidean space. -/
theorem integrable_coordMonomial (α : Fin m → ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) =>
      rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x) := by
  rw [rho_mul_coordMonomial_comp]
  have hem : MeasurableEmbedding (EuclideanSpace.equiv (Fin m) ℝ) :=
    (MeasurableEquiv.toLp 2 ((Fin m) → ℝ)).symm.measurableEmbedding
  rw [measurePreserving_eucEquiv.integrable_comp_emb hem, volume_pi]
  exact Integrable.fintype_prod (fun i => integrable_pow_mul_phi (α i))

theorem integrableOn_orthant_coordMonomial (α : Fin m → ℕ) (c : ℝ) :
    IntegrableOn (fun x => rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x)
      (orthantIic c) :=
  (integrable_coordMonomial α).integrableOn

/-- Orthant moment of a coordinate monomial, factored into truncated one-dimensional moments. -/
theorem integral_orthant_coordMonomial (α : Fin m → ℕ) (c : ℝ) :
    ∫ x in orthantIic c, rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x =
      ∏ i, moment1D (α i) c := by
  have hfun : ∀ x, rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x =
      ∏ i, (fun t : ℝ => t ^ α i * phi t) (x i) := by
    intro x
    simpa [Function.comp_apply, eucEquiv_apply] using congrFun (rho_mul_coordMonomial_comp α) x
  simp_rw [hfun]
  rw [integral_orthant_prod (fun i t => t ^ α i * phi t) c
      (fun i => (integrable_pow_mul_phi (α i)).integrableOn)]
  simp_rw [moment1D]

/-- Full-space moment, the product of the untruncated one-dimensional moments. -/
theorem integral_coordMonomial_eq_prod (α : Fin m → ℕ) :
    ∫ x, rho (1 : Matrix (Fin m) (Fin m) ℝ) x * coordMonomial α x =
      ∏ i, ∫ t, t ^ α i * phi t := by
  rw [rho_mul_coordMonomial_comp]
  convert ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).integral_comp'
        (fun y : Fin m → ℝ => ∏ i, (y i) ^ α i * phi (y i))).trans
      (integral_fintype_prod_volume_eq_prod (fun i (t : ℝ) => t ^ α i * phi t)) using 1 <;> rfl
theorem moment1D_zero (c : ℝ) : moment1D 0 c = Phi c := by
  simp [moment1D, pow_zero, Phi]

theorem moment1D_one (c : ℝ) : moment1D 1 c = -phi c := by
  simpa [moment1D, pow_one] using integral_Iic_id_mul_phi c

theorem moment1D_two (c : ℝ) : moment1D 2 c = Phi c - c * phi c :=
  integral_Iic_sq_mul_phi c

/-- Gaussian mass of the orthant is `Φ(c)^m`. -/
theorem integral_orthant_rho (c : ℝ) :
    ∫ x in orthantIic c, rho (1 : Matrix (Fin m) (Fin m) ℝ) x = Phi c ^ m := by
  have h := integral_orthant_coordMonomial (fun _ : Fin m => 0) c
  simpa [coordMonomial, pow_zero, Finset.prod_const_one, moment1D_zero, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using h

#print axioms measurePreserving_eucEquiv
#print axioms integrableOn_orthant_prod
#print axioms integral_orthant_prod
#print axioms integrable_coordMonomial
#print axioms integrableOn_orthant_coordMonomial
#print axioms integral_orthant_coordMonomial
#print axioms integral_coordMonomial_eq_prod
#print axioms integral_orthant_rho
#print axioms moment1D_zero
#print axioms moment1D_one
#print axioms moment1D_two

end SimplexFull.Covariance
