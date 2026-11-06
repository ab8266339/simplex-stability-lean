import SimplexFull.Tilted
import SimplexFull.Mills
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Set
namespace SimplexFull

theorem bal_h_bound (c : ℝ) :
    |h c| ≤ (1 + h 0) * (1 + |c| ^ (1 : ℕ)) := by
  have hb := abs_h_le_abs_add c
  have hzero := h_pos 0
  have ha := abs_nonneg c
  have hp := mul_nonneg hzero.le ha
  simp only [pow_one]
  nlinarith

theorem bal_hsq_bound (c : ℝ) :
    |h c ^ 2| ≤ (2 + 2 * h 0 ^ 2) * (1 + |c| ^ (2 : ℕ)) := by
  have hh := h_le_abs_add c
  have hzero := h_pos 0
  have hpos := h_pos c
  have ha := abs_nonneg c
  have hs : h c ^ 2 ≤ (|c| + h 0) ^ 2 :=
    (sq_le_sq₀ hpos.le (by positivity)).mpr hh
  rw [abs_of_nonneg (sq_nonneg (h c))]
  have hmix := sq_nonneg (|c| - h 0)
  have hprod := mul_nonneg (sq_nonneg (h 0)) (sq_nonneg |c|)
  nlinarith

theorem bal_sigma_bound (c : ℝ) :
    |sigma c| ≤ (1 : ℝ) * (1 + |c| ^ (0 : ℕ)) := by
  rw [abs_of_pos (sigma_pos c)]
  have hs := sigma_lt_one c
  norm_num
  linarith

theorem bal_integrable_h (m : ℕ) (mu : ℝ) :
    Integrable (fun c => h c * tiltWeight m mu c) :=
  integrable_polynomial_bound_tiltWeight m mu h continuous_h.aestronglyMeasurable
    (1 + h 0) 1 bal_h_bound

theorem bal_integrable_hsq (m : ℕ) (mu : ℝ) :
    Integrable (fun c => h c ^ 2 * tiltWeight m mu c) :=
  integrable_polynomial_bound_tiltWeight m mu (fun c => h c ^ 2)
    (continuous_h.pow 2).aestronglyMeasurable (2 + 2 * h 0 ^ 2) 2 bal_hsq_bound

theorem bal_integrable_sigma (m : ℕ) (mu : ℝ) :
    Integrable (fun c => sigma c * tiltWeight m mu c) :=
  integrable_polynomial_bound_tiltWeight m mu sigma continuous_sigma.aestronglyMeasurable
    1 0 bal_sigma_bound

theorem hasDerivAt_h_mul_tiltWeight (m : ℕ) (hm : 2 ≤ m) (mu c : ℝ) :
    HasDerivAt (fun x => h x * tiltWeight m mu x)
      (((m : ℝ) + mu * h c - 2 * h c ^ 2 - ((m : ℝ) - 1) * sigma c) *
        tiltWeight m mu c) c := by
  have hn : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub hm, Nat.cast_ofNat]
  have hh := (hasDerivAt_h c).mul (hasDerivAt_tiltWeight_x m mu c)
  rw [hn] at hh
  have he :
      sigma c * tiltWeight m mu c +
        h c * ((mu - 2 * c + ((m : ℝ) - 2) * q c) * tiltWeight m mu c) =
      (((m : ℝ) + mu * h c - 2 * h c ^ 2 - ((m : ℝ) - 1) * sigma c) *
        tiltWeight m mu c) := by
    rw [← balance_factor_identity (m : ℝ) mu c]
    ring
  rw [he] at hh
  exact hh

theorem gaussian_balance_identity (m : ℕ) (hm : 2 ≤ m) (mu : ℝ) :
    2 * a m mu + ((m : ℝ) - 1) * b m mu = (m : ℝ) + mu * H m mu := by
  let w : ℝ → ℝ := tiltWeight m mu
  have hw : Integrable w := integrable_tiltWeight m mu
  have hh : Integrable (fun c => h c * w c) := bal_integrable_h m mu
  have hh2 : Integrable (fun c => h c ^ 2 * w c) := bal_integrable_hsq m mu
  have hs : Integrable (fun c => sigma c * w c) := bal_integrable_sigma m mu
  have h1 := hw.const_mul (m : ℝ)
  have h2 := hh.const_mul mu
  have h3 := hh2.const_mul (2 : ℝ)
  have h4 := hs.const_mul ((m : ℝ) - 1)
  let g : ℝ → ℝ := fun c =>
    ((m : ℝ) + mu * h c - 2 * h c ^ 2 - ((m : ℝ) - 1) * sigma c) * w c
  have hg : Integrable g := by
    apply (((h1.add h2).sub h3).sub h4).congr
    filter_upwards [] with c
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    dsimp [g]
    ring
  have hz : (∫ c, g c) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun c => hasDerivAt_h_mul_tiltWeight m hm mu c) hg hh
  have hi : (∫ c, g c) =
      (m : ℝ) * normalizer m mu + mu * (∫ c, h c * w c) -
        2 * (∫ c, h c ^ 2 * w c) - ((m : ℝ) - 1) * (∫ c, sigma c * w c) := by
    calc
      (∫ c, g c) =
          ∫ c, (m : ℝ) * w c + mu * (h c * w c) -
            2 * (h c ^ 2 * w c) - ((m : ℝ) - 1) * (sigma c * w c) := by
              apply integral_congr_ae
              filter_upwards [] with c
              dsimp [g]
              ring
      _ = _ := by
        have hs4 := integral_sub ((h1.add h2).sub h3) h4
        have hs3 := integral_sub (h1.add h2) h3
        have hs2 := integral_add h1 h2
        simp only [Pi.sub_apply, Pi.add_apply] at hs4 hs3 hs2
        rw [hs4, hs3, hs2]
        simp only [integral_const_mul, normalizer, w]
  rw [hi] at hz
  unfold a b H tiltedMoment
  have hZ := (normalizer_pos m mu).ne'
  dsimp [w] at hz
  field_simp [hZ]
  linarith [hz]

#print axioms bal_integrable_h
#print axioms bal_integrable_hsq
#print axioms bal_integrable_sigma
#print axioms hasDerivAt_h_mul_tiltWeight
#print axioms gaussian_balance_identity
end SimplexFull
