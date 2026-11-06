import SimplexFull.Tilted
import SimplexFull.Covariance1D
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace SimplexFull

/-- Un-normalized tilted moment `∫ f(c) w_{m,μ}(c) dc`. -/
def rawMoment (m : ℕ) (mu : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ c, f c * tiltWeight m mu c

theorem tiltedMoment_eq_rawMoment (m : ℕ) (mu : ℝ) (f : ℝ → ℝ) :
    tiltedMoment m mu f = rawMoment m mu f / normalizer m mu := by
  rfl

/-- Derivative of the raw moment in the tilt. The derivative integrand is dominated on
`(μ - 1, μ + 1)` by `|c| |f c| (w_{μ-1}(c) + w_{μ+1}(c))`. -/
theorem hasDerivAt_rawMoment (m : ℕ) (mu : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) (C : ℝ) (n : ℕ)
    (hbound : ∀ c, |f c| ≤ C * (1 + |c| ^ n)) :
    HasDerivAt (fun t => rawMoment m t f) (∫ c, c * f c * tiltWeight m mu c) mu := by
  have hs : Ioo (mu - 1) (mu + 1) ∈ 𝓝 mu :=
    Ioo_mem_nhds (sub_lt_self mu one_pos) (lt_add_of_pos_right mu one_pos)
  have hF_meas : ∀ᶠ t in 𝓝 mu,
      AEStronglyMeasurable (fun c => f c * tiltWeight m t c) volume :=
    Eventually.of_forall fun t => hf.mul (continuous_tiltWeight m t).aestronglyMeasurable
  have hF_int : Integrable (fun c => f c * tiltWeight m mu c) :=
    integrable_polynomial_bound_tiltWeight m mu f hf C n hbound
  have hF'_meas : AEStronglyMeasurable (fun c => c * f c * tiltWeight m mu c) volume := by
    have hpow :=
      (integrable_pow_mul_polynomial_bound_tiltWeight m 1 mu f hf C n hbound).aestronglyMeasurable
    simp_rw [pow_one] at hpow
    exact hpow
  have h_bound : ∀ᵐ c ∂volume, ∀ x ∈ Ioo (mu - 1) (mu + 1),
      ‖c * f c * tiltWeight m x c‖ ≤
        |c| * |f c| * (tiltWeight m (mu - 1) c + tiltWeight m (mu + 1) c) :=
    ae_of_all _ fun c x hx => by
      have hxI : mu - 1 ≤ x ∧ x ≤ mu + 1 := ⟨(mem_Ioo.mp hx).1.le, (mem_Ioo.mp hx).2.le⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (tiltWeight_pos m x c)]
      exact mul_le_mul_of_nonneg_left (tiltWeight_le_endpoints m mu x c hxI)
        (mul_nonneg (abs_nonneg c) (abs_nonneg (f c)))
  have hB : Integrable fun c =>
      |c| * |f c| * (tiltWeight m (mu - 1) c + tiltWeight m (mu + 1) c) := by
    have hL :=
      (integrable_pow_mul_polynomial_bound_tiltWeight m 1 (mu - 1) f hf C n hbound).abs
    have hR :=
      (integrable_pow_mul_polynomial_bound_tiltWeight m 1 (mu + 1) f hf C n hbound).abs
    have hL' : Integrable fun c => |c| * |f c| * tiltWeight m (mu - 1) c :=
      hL.congr <| ae_of_all _ fun c => by
        simp only [pow_one, abs_mul, abs_of_pos (tiltWeight_pos m (mu - 1) c)]
    have hR' : Integrable fun c => |c| * |f c| * tiltWeight m (mu + 1) c :=
      hR.congr <| ae_of_all _ fun c => by
        simp only [pow_one, abs_mul, abs_of_pos (tiltWeight_pos m (mu + 1) c)]
    exact (hL'.add hR').congr <| ae_of_all _ fun c => by
      simp only [Pi.add_apply]
      ring
  have h_diff : ∀ᵐ c ∂volume, ∀ x ∈ Ioo (mu - 1) (mu + 1),
      HasDerivAt (fun t => f c * tiltWeight m t c) (c * f c * tiltWeight m x c) x :=
    ae_of_all _ fun c x _hx => by
      have hmul := (hasDerivAt_tiltWeight_mu m x c).const_mul (f c)
      rwa [show f c * (c * tiltWeight m x c) = c * f c * tiltWeight m x c by ring] at hmul
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t c => f c * tiltWeight m t c)
    (F' := fun t c => c * f c * tiltWeight m t c)
    (bound := fun c => |c| * |f c| * (tiltWeight m (mu - 1) c + tiltWeight m (mu + 1) c))
    (s := Ioo (mu - 1) (mu + 1)) (x₀ := mu)
    hs hF_meas hF_int hF'_meas h_bound hB h_diff
  simpa [rawMoment] using hkey.2

theorem hasDerivAt_normalizer (m : ℕ) (mu : ℝ) :
    HasDerivAt (normalizer m) (∫ c, c * tiltWeight m mu c) mu := by
  have hbound : ∀ c, |(1 : ℝ)| ≤ (1 : ℝ) * (1 + |c| ^ (0 : ℕ)) := by
    intro c
    rw [abs_one, one_mul, pow_zero]
    exact le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)
  have h := hasDerivAt_rawMoment m mu (fun _ => (1 : ℝ)) aestronglyMeasurable_const 1 0 hbound
  have hder : (∫ c, c * (fun _ : ℝ => (1 : ℝ)) c * tiltWeight m mu c) =
      ∫ c, c * tiltWeight m mu c := by
    simp [mul_one]
  have hfun : (fun t => rawMoment m t (fun _ : ℝ => 1)) = normalizer m := by
    ext t
    simp [rawMoment, normalizer, one_mul]
  rw [← hfun, ← hder]
  exact h

/-- Quotient rule: the tilt derivative of `𝔼_{m,μ}[f]` is the covariance numerator over `Z^2`. -/
theorem hasDerivAt_tiltedMoment (m : ℕ) (mu : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) (C : ℝ) (n : ℕ)
    (hbound : ∀ c, |f c| ≤ C * (1 + |c| ^ n)) :
    HasDerivAt (fun t => tiltedMoment m t f)
      (((∫ c, c * f c * tiltWeight m mu c) * normalizer m mu -
          (∫ c, f c * tiltWeight m mu c) * (∫ c, c * tiltWeight m mu c)) /
        normalizer m mu ^ 2) mu := by
  have hu := hasDerivAt_rawMoment m mu f hf C n hbound
  have hv := hasDerivAt_normalizer m mu
  exact hu.div hv (normalizer_pos m mu).ne'

theorem tiltedMoment_deriv_pos (m : ℕ) (mu : ℝ) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_mono : StrictMono f) (C : ℝ) (n : ℕ)
    (hbound : ∀ c, |f c| ≤ C * (1 + |c| ^ n)) :
    0 < ((∫ c, c * f c * tiltWeight m mu c) * normalizer m mu -
        (∫ c, f c * tiltWeight m mu c) * (∫ c, c * tiltWeight m mu c)) /
      normalizer m mu ^ 2 := by
  have hf : AEStronglyMeasurable f volume := hf_cont.aestronglyMeasurable
  have hfw := integrable_polynomial_bound_tiltWeight m mu f hf C n hbound
  have hxfw : Integrable fun c => c * f c * tiltWeight m mu c := by
    have hpow := integrable_pow_mul_polynomial_bound_tiltWeight m 1 mu f hf C n hbound
    simp_rw [pow_one] at hpow
    exact hpow
  have hnum : 0 < (∫ c, c * f c * tiltWeight m mu c) * normalizer m mu -
      (∫ c, f c * tiltWeight m mu c) * (∫ c, c * tiltWeight m mu c) := by
    unfold normalizer
    exact covNumerator_pos hf_cont hf_mono (continuous_tiltWeight m mu) (tiltWeight_pos m mu)
      (integrable_tiltWeight m mu) (integrable_mul_tiltWeight m mu) hfw hxfw
  exact div_pos hnum (sq_pos_of_pos (normalizer_pos m mu))

/-- A continuous strictly monotone observable of polynomial growth has a strictly increasing
tilted expectation. The sign is the covariance numerator, not an assumption. -/
theorem strictMono_tiltedMoment (m : ℕ) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_mono : StrictMono f) (C : ℝ) (n : ℕ)
    (hbound : ∀ c, |f c| ≤ C * (1 + |c| ^ n)) :
    StrictMono fun mu => tiltedMoment m mu f := by
  let g : ℝ → ℝ := fun mu => tiltedMoment m mu f
  let g' : ℝ → ℝ := fun mu =>
    ((∫ c, c * f c * tiltWeight m mu c) * normalizer m mu -
      (∫ c, f c * tiltWeight m mu c) * (∫ c, c * tiltWeight m mu c)) /
    normalizer m mu ^ 2
  have hg : ∀ mu, HasDerivAt g (g' mu) mu := fun mu =>
    hasDerivAt_tiltedMoment m mu f hf_cont.aestronglyMeasurable C n hbound
  have hg' : ∀ mu, 0 < g' mu := fun mu =>
    tiltedMoment_deriv_pos m mu hf_cont hf_mono C n hbound
  have hcont : Continuous g :=
    continuous_iff_continuousAt.mpr fun mu => (hg mu).continuousAt
  have hmono : StrictMonoOn g univ := by
    refine strictMonoOn_of_deriv_pos convex_univ (hcont.continuousOn : ContinuousOn g univ) ?_
    intro mu _hmu
    rw [(hg mu).deriv]
    exact hg' mu
  exact fun a b hab => hmono (mem_univ a) (mem_univ b) hab

#print axioms tiltedMoment_eq_rawMoment
#print axioms hasDerivAt_rawMoment
#print axioms hasDerivAt_normalizer
#print axioms hasDerivAt_tiltedMoment
#print axioms tiltedMoment_deriv_pos
#print axioms strictMono_tiltedMoment

end SimplexFull
