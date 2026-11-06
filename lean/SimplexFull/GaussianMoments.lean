import SimplexFull.Moments
import SimplexFull.Mills

noncomputable section

open MeasureTheory Set

namespace SimplexFull

/-- `|σ(c)| ≤ 1 · (1 + |c| ^ 0)`. -/
theorem gm_sigma_poly (c : ℝ) : |sigma c| ≤ (1 : ℝ) * (1 + |c| ^ (0 : ℕ)) := by
  rw [abs_of_pos (sigma_pos c), one_mul, pow_zero]
  exact (sigma_lt_one c).le.trans (le_add_of_nonneg_right zero_le_one)

theorem gm_integrable_sigma (m : ℕ) (mu : ℝ) :
    Integrable (fun c => sigma c * tiltWeight m mu c) :=
  integrable_polynomial_bound_tiltWeight m mu sigma
    (continuous_sigma.aestronglyMeasurable (μ := volume)) 1 0 gm_sigma_poly

/-- `|h(c)| ≤ (|c| + h 0) ≤ (1 + h 0) (1 + |c|)`. -/
theorem gm_h_poly (c : ℝ) : |h c| ≤ (1 + h 0) * (1 + |c| ^ 1) := by
  have h0pos : 0 < h 0 := h_pos 0
  have hstep : |c| + h 0 ≤ (1 + h 0) * (1 + |c|) := by
    have hB : 0 ≤ 1 + h 0 * |c| :=
      add_nonneg zero_le_one (mul_nonneg h0pos.le (abs_nonneg c))
    calc
      |c| + h 0 ≤ |c| + h 0 + (1 + h 0 * |c|) := le_add_of_nonneg_right hB
      _ = (1 + h 0) * (1 + |c|) := by ring
  calc
    |h c| ≤ |c| + h 0 := abs_h_le_abs_add c
    _ ≤ (1 + h 0) * (1 + |c|) := hstep
    _ = (1 + h 0) * (1 + |c| ^ 1) := by simp [pow_one]

theorem gm_two_sq (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have hEq : 2 * (x ^ 2 + y ^ 2) - (x + y) ^ 2 = (x - y) ^ 2 := by ring
  exact sub_nonneg.mp (by rw [hEq]; exact sq_nonneg (x - y))

/-- `|h(c)²| ≤ (2 + 2 h(0)²) (1 + |c|²)`, from `(|c| + h 0)² ≤ 2 (|c|² + h(0)²)`. -/
theorem gm_hsq_poly (c : ℝ) :
    |h c ^ 2| ≤ (2 + 2 * (h 0) ^ 2) * (1 + |c| ^ 2) := by
  have hsq : (h c) ^ 2 ≤ (|c| + h 0) ^ 2 := by
    have hle : h c ≤ |c| + h 0 := h_le_abs_add c
    have hEq : (|c| + h 0) ^ 2 - (h c) ^ 2 =
        (|c| + h 0 - h c) * (|c| + h 0 + h c) := by ring
    have hnn : 0 ≤ (|c| + h 0 - h c) * (|c| + h 0 + h c) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (add_nonneg (add_nonneg (abs_nonneg c) (h_pos 0).le) (h_pos c).le)
    exact sub_nonneg.mp (by rw [hEq]; exact hnn)
  have htwo : (|c| + h 0) ^ 2 ≤ 2 * (|c| ^ 2 + (h 0) ^ 2) := gm_two_sq |c| (h 0)
  have hC : 2 * (|c| ^ 2 + (h 0) ^ 2) ≤ (2 + 2 * (h 0) ^ 2) * (1 + |c| ^ 2) := by
    have hEq : (2 + 2 * (h 0) ^ 2) * (1 + |c| ^ 2) - 2 * (|c| ^ 2 + (h 0) ^ 2) =
        2 + 2 * (h 0) ^ 2 * |c| ^ 2 := by ring
    have hnn : 0 ≤ 2 + 2 * (h 0) ^ 2 * |c| ^ 2 :=
      add_nonneg zero_le_two
        (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg (h 0))) (sq_nonneg |c|))
    exact sub_nonneg.mp (by rw [hEq]; exact hnn)
  calc
    |h c ^ 2| = (h c) ^ 2 := abs_of_nonneg (sq_nonneg _)
    _ ≤ (|c| + h 0) ^ 2 := hsq
    _ ≤ 2 * (|c| ^ 2 + (h 0) ^ 2) := htwo
    _ ≤ (2 + 2 * (h 0) ^ 2) * (1 + |c| ^ 2) := hC

theorem gm_integrable_h (m : ℕ) (mu : ℝ) :
    Integrable (fun c => h c * tiltWeight m mu c) :=
  integrable_polynomial_bound_tiltWeight m mu h
    (continuous_h.aestronglyMeasurable (μ := volume)) (1 + h 0) 1 gm_h_poly

theorem gm_integrable_hsq (m : ℕ) (mu : ℝ) :
    Integrable (fun c => h c ^ 2 * tiltWeight m mu c) :=
  integrable_polynomial_bound_tiltWeight m mu (fun c => h c ^ 2)
    ((continuous_h.pow 2).aestronglyMeasurable (μ := volume)) (2 + 2 * (h 0) ^ 2) 2 gm_hsq_poly

theorem gm_integral_pos_mul {m : ℕ} {mu : ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_pos : ∀ c, 0 < f c)
    (hf_int : Integrable fun c => f c * tiltWeight m mu c) :
    0 < ∫ c, f c * tiltWeight m mu c :=
  integral_weight_pos (hf_cont.mul (continuous_tiltWeight m mu))
    (fun c => mul_pos (hf_pos c) (tiltWeight_pos m mu c)) hf_int

theorem H_pos (m : ℕ) (mu : ℝ) : 0 < H m mu := by
  unfold H
  rw [tiltedMoment_eq_rawMoment, rawMoment]
  exact div_pos (gm_integral_pos_mul continuous_h h_pos (gm_integrable_h m mu))
    (normalizer_pos m mu)

theorem a_pos (m : ℕ) (mu : ℝ) : 0 < a m mu := by
  unfold a
  rw [tiltedMoment_eq_rawMoment, rawMoment]
  exact div_pos
    (gm_integral_pos_mul (continuous_h.pow 2) (fun c => sq_pos_of_pos (h_pos c))
      (gm_integrable_hsq m mu))
    (normalizer_pos m mu)

theorem b_pos (m : ℕ) (mu : ℝ) : 0 < b m mu := by
  unfold b
  rw [tiltedMoment_eq_rawMoment, rawMoment]
  exact div_pos (gm_integral_pos_mul continuous_sigma sigma_pos (gm_integrable_sigma m mu))
    (normalizer_pos m mu)

theorem b_lt_one (m : ℕ) (mu : ℝ) : b m mu < 1 := by
  have hint : Integrable fun c => (1 - sigma c) * tiltWeight m mu c := by
    exact ((integrable_tiltWeight m mu).sub (gm_integrable_sigma m mu)).congr
      (ae_of_all _ fun c => by
        simp only [Pi.sub_apply]
        ring)
  have hpos : 0 < ∫ c, (1 - sigma c) * tiltWeight m mu c :=
    integral_weight_pos
      ((continuous_const.sub continuous_sigma).mul (continuous_tiltWeight m mu))
      (fun c => mul_pos (sub_pos.mpr (sigma_lt_one c)) (tiltWeight_pos m mu c)) hint
  have hdiff : (∫ c, tiltWeight m mu c) - (∫ c, sigma c * tiltWeight m mu c) =
      ∫ c, (1 - sigma c) * tiltWeight m mu c := by
    rw [← integral_sub (integrable_tiltWeight m mu) (gm_integrable_sigma m mu)]
    exact integral_congr_ae (ae_of_all _ fun c => by ring)
  unfold b
  rw [tiltedMoment_eq_rawMoment, div_lt_one (normalizer_pos m mu), rawMoment, normalizer, ← sub_pos,
    hdiff]
  exact hpos

theorem gm_strictMono_hsq : StrictMono fun c => h c ^ 2 := by
  intro x y hxy
  exact (sq_lt_sq₀ (h_pos x).le (h_pos y).le).mpr (strictMono_h hxy)

theorem continuous_H (m : ℕ) : Continuous (H m) :=
  continuous_iff_continuousAt.mpr fun mu =>
    (hasDerivAt_tiltedMoment m mu h (continuous_h.aestronglyMeasurable (μ := volume))
      (1 + h 0) 1 gm_h_poly).continuousAt

theorem strictMono_H (m : ℕ) : StrictMono (H m) :=
  strictMono_tiltedMoment m continuous_h strictMono_h (1 + h 0) 1 gm_h_poly

theorem continuous_b (m : ℕ) : Continuous (b m) :=
  continuous_iff_continuousAt.mpr fun mu =>
    (hasDerivAt_tiltedMoment m mu sigma (continuous_sigma.aestronglyMeasurable (μ := volume))
      1 0 gm_sigma_poly).continuousAt

theorem strictMono_b (m : ℕ) : StrictMono (b m) :=
  strictMono_tiltedMoment m continuous_sigma strictMono_sigma 1 0 gm_sigma_poly

theorem continuous_a (m : ℕ) : Continuous (a m) :=
  continuous_iff_continuousAt.mpr fun mu =>
    (hasDerivAt_tiltedMoment m mu (fun c => h c ^ 2)
      ((continuous_h.pow 2).aestronglyMeasurable (μ := volume))
      (2 + 2 * (h 0) ^ 2) 2 gm_hsq_poly).continuousAt

theorem strictMono_a (m : ℕ) : StrictMono (a m) :=
  strictMono_tiltedMoment m (continuous_h.pow 2) gm_strictMono_hsq
    (2 + 2 * (h 0) ^ 2) 2 gm_hsq_poly

lemma gm_integrable_mul_sigma (m : ℕ) (mu : ℝ) :
    Integrable fun c => c * sigma c * tiltWeight m mu c := by
  have h := integrable_pow_mul_polynomial_bound_tiltWeight m 1 mu sigma
    (continuous_sigma.aestronglyMeasurable (μ := volume)) 1 0 gm_sigma_poly
  simp_rw [pow_one] at h
  exact h

lemma gm_integrable_mul_hsq (m : ℕ) (mu : ℝ) :
    Integrable fun c => c * h c ^ 2 * tiltWeight m mu c := by
  have h := integrable_pow_mul_polynomial_bound_tiltWeight m 1 mu (fun c => h c ^ 2)
    ((continuous_h.pow 2).aestronglyMeasurable (μ := volume)) (2 + 2 * (h 0) ^ 2) 2 gm_hsq_poly
  simp_rw [pow_one] at h
  exact h

lemma gm_raw_sigma_pos (m : ℕ) (mu : ℝ) : 0 < rawMoment m mu sigma := by
  unfold rawMoment
  exact gm_integral_pos_mul continuous_sigma sigma_pos (gm_integrable_sigma m mu)

lemma gm_hsq_mul_cancel (m : ℕ) (mu c : ℝ) :
    (h c ^ 2 / sigma c) * (sigma c * tiltWeight m mu c) = h c ^ 2 * tiltWeight m mu c := by
  rw [← mul_assoc, div_mul_cancel₀ _ (sigma_pos c).ne']

lemma gm_mul_hsq_cancel (m : ℕ) (mu c : ℝ) :
    c * (h c ^ 2 / sigma c) * (sigma c * tiltWeight m mu c) =
      c * h c ^ 2 * tiltWeight m mu c := by
  rw [mul_assoc, gm_hsq_mul_cancel, ← mul_assoc]

/-- `a/b = (∫ h² w) / (∫ σ w)` after cancelling the positive normalizer. -/
theorem gm_a_div_b_eq (m : ℕ) (mu : ℝ) :
    a m mu / b m mu =
      rawMoment m mu (fun c => h c ^ 2) / rawMoment m mu sigma := by
  unfold a b
  rw [tiltedMoment_eq_rawMoment, tiltedMoment_eq_rawMoment]
  field_simp [(normalizer_pos m mu).ne', (gm_raw_sigma_pos m mu).ne']

lemma gm_ab_num_pos (m : ℕ) (mu : ℝ) :
    0 < (∫ c, c * h c ^ 2 * tiltWeight m mu c) * rawMoment m mu sigma -
      rawMoment m mu (fun c => h c ^ 2) * (∫ c, c * sigma c * tiltWeight m mu c) := by
  let f : ℝ → ℝ := fun c => h c ^ 2 / sigma c
  let w : ℝ → ℝ := fun c => sigma c * tiltWeight m mu c
  have hxw : Integrable fun c => c * w c :=
    (gm_integrable_mul_sigma m mu).congr
      (ae_of_all _ fun c => mul_assoc c (sigma c) (tiltWeight m mu c))
  have hfw : Integrable fun c => f c * w c :=
    (gm_integrable_hsq m mu).congr
      (ae_of_all _ fun c => (gm_hsq_mul_cancel m mu c).symm)
  have hxfw : Integrable fun c => c * f c * w c :=
    (gm_integrable_mul_hsq m mu).congr
      (ae_of_all _ fun c => (gm_mul_hsq_cancel m mu c).symm)
  have hcov := covNumerator_pos (f := f) (w := w) continuous_hsq_div_sigma
    strictMono_hsq_div_sigma (continuous_sigma.mul (continuous_tiltWeight m mu))
    (fun c => mul_pos (sigma_pos c) (tiltWeight_pos m mu c)) (gm_integrable_sigma m mu) hxw hfw
    hxfw
  have hxfw_eq : ∀ c, c * f c * w c = c * h c ^ 2 * tiltWeight m mu c :=
    fun c => gm_mul_hsq_cancel m mu c
  have hfw_eq : ∀ c, f c * w c = h c ^ 2 * tiltWeight m mu c :=
    fun c => gm_hsq_mul_cancel m mu c
  have hxw_eq : ∀ c, c * w c = c * sigma c * tiltWeight m mu c := fun c =>
    (mul_assoc c (sigma c) (tiltWeight m mu c)).symm
  have hw_int : ∫ c, w c = rawMoment m mu sigma := by
    unfold rawMoment
    rfl
  rw [integral_congr_ae (ae_of_all _ hxfw_eq), integral_congr_ae (ae_of_all _ hfw_eq),
    integral_congr_ae (ae_of_all _ hxw_eq), hw_int] at hcov
  unfold rawMoment
  exact hcov

theorem strictMono_a_div_b (m : ℕ) : StrictMono fun mu => a m mu / b m mu := by
  have hfun : (fun mu => a m mu / b m mu) =
      fun mu => rawMoment m mu (fun c => h c ^ 2) / rawMoment m mu sigma := by
    ext mu
    exact gm_a_div_b_eq m mu
  rw [hfun]
  let g : ℝ → ℝ := fun mu =>
    rawMoment m mu (fun c => h c ^ 2) / rawMoment m mu sigma
  let g' : ℝ → ℝ := fun mu =>
    ((∫ c, c * h c ^ 2 * tiltWeight m mu c) * rawMoment m mu sigma -
      rawMoment m mu (fun c => h c ^ 2) * (∫ c, c * sigma c * tiltWeight m mu c)) /
    rawMoment m mu sigma ^ 2
  have hg : ∀ mu, HasDerivAt g (g' mu) mu := by
    intro mu
    exact (hasDerivAt_rawMoment m mu (fun c => h c ^ 2)
      ((continuous_h.pow 2).aestronglyMeasurable (μ := volume)) (2 + 2 * (h 0) ^ 2) 2
      gm_hsq_poly).div
      (hasDerivAt_rawMoment m mu sigma (continuous_sigma.aestronglyMeasurable (μ := volume)) 1 0
        gm_sigma_poly)
      (gm_raw_sigma_pos m mu).ne'
  have hg' : ∀ mu, 0 < g' mu := by
    intro mu
    exact div_pos (gm_ab_num_pos m mu) (sq_pos_of_pos (gm_raw_sigma_pos m mu))
  have hcont : Continuous g :=
    continuous_iff_continuousAt.mpr fun mu => (hg mu).continuousAt
  have hmono : StrictMonoOn g univ := by
    refine strictMonoOn_of_deriv_pos convex_univ (hcont.continuousOn : ContinuousOn g univ) ?_
    intro mu _hmu
    rw [(hg mu).deriv]
    exact hg' mu
  exact fun x y hxy => hmono (mem_univ x) (mem_univ y) hxy

#print axioms a_pos
#print axioms H_pos
#print axioms b_pos
#print axioms b_lt_one
#print axioms continuous_a
#print axioms continuous_b
#print axioms continuous_H
#print axioms strictMono_a
#print axioms strictMono_b
#print axioms strictMono_H
#print axioms gm_a_div_b_eq
#print axioms strictMono_a_div_b

end SimplexFull
