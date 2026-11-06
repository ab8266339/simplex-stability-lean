import SimplexFull.Tilted
import SimplexFull.Mills
import SimplexFull.Covariance1D
import SimplexFull.MillsPrep
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.IntermediateValue

/-!
# Monotonicity of the tilted Mills moment `b`

For `m ≥ 2`, the tilted weight gains one Mills factor at each successor,
`tiltWeight (m + 1) μ = Phi * tiltWeight m μ`. The map `c ↦ Phi c` is continuous
and strictly increasing from `0` to `1`, and `c ↦ sigma c` is strictly increasing,
so the Gaussian weight has positive covariance between `sigma` and `Phi`.
That covariance is exactly the numerator of `b (m + 1) μ - b m μ`.
-/

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace SimplexFull

/-- Successor step for the tilted weight: each extra Mills factor is one `Phi`. -/
theorem tiltWeight_succ (m : ℕ) (mu c : ℝ) (hm : 2 ≤ m) :
    tiltWeight (m + 1) mu c = Phi c * tiltWeight m mu c := by
  unfold tiltWeight
  have hsub : (m + 1) - 2 = (m - 2) + 1 := by omega
  rw [hsub, pow_succ]
  ring

theorem order_strictMono_Phi : StrictMono Phi := by
  apply strictMono_of_deriv_pos
  intro c
  rw [(hasDerivAt_Phi c).deriv]
  exact phi_pos c

/-- `Phi` is the Gaussian distribution function, so it tends to `1` at `+∞`. -/
theorem order_tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) := by
  have hcov : AECover (volume : Measure ℝ) atTop (fun c : ℝ => Iic c) :=
    aecover_Iic (b := id) tendsto_id
  have hlim :
      Tendsto (fun c : ℝ => ∫ x in Iic c, phi x) atTop (𝓝 (∫ x, phi x)) := by
    simpa using hcov.integral_tendsto_of_countably_generated integrable_phi
  rw [integral_phi_eq_one] at hlim
  unfold Phi
  exact hlim

theorem order_integrable_bounded_tiltWeight (m : ℕ) (mu : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hfb : ∀ c, |f c| ≤ 1) :
    Integrable (fun c => f c * tiltWeight m mu c) := by
  refine (integrable_tiltWeight m mu).mono'
    ((hf.mul (continuous_tiltWeight m mu)).aestronglyMeasurable) (ae_of_all _ fun c => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tiltWeight_pos m mu c)]
  calc
    |f c| * tiltWeight m mu c ≤ 1 * tiltWeight m mu c :=
      mul_le_mul_of_nonneg_right (hfb c) (tiltWeight_pos m mu c).le
    _ = tiltWeight m mu c := one_mul _

theorem order_abs_sigma_le (c : ℝ) : |sigma c| ≤ 1 := by
  rw [abs_of_pos (sigma_pos c)]
  exact (sigma_lt_one c).le

theorem order_abs_Phi_le (c : ℝ) : |Phi c| ≤ 1 := by
  rw [abs_of_pos (Phi_pos c)]
  exact (Phi_lt_one c).le

theorem order_abs_sigma_mul_Phi_le (c : ℝ) : |sigma c * Phi c| ≤ 1 := by
  rw [abs_mul, abs_of_pos (sigma_pos c), abs_of_pos (Phi_pos c)]
  have hle : sigma c * Phi c ≤ sigma c := by
    simpa using mul_le_mul_of_nonneg_left (Phi_lt_one c).le (sigma_pos c).le
  exact hle.trans (sigma_lt_one c).le

theorem order_abs_one_sub_Phi_le (c : ℝ) : |(1 : ℝ) - Phi c| ≤ 1 := by
  rw [abs_of_pos (sub_pos.mpr (Phi_lt_one c))]
  exact (sub_lt_self (1 : ℝ) (Phi_pos c)).le

theorem order_integrable_sigma_tiltWeight (m : ℕ) (mu : ℝ) :
    Integrable (fun c => sigma c * tiltWeight m mu c) :=
  order_integrable_bounded_tiltWeight m mu sigma continuous_sigma order_abs_sigma_le

theorem order_integrable_Phi_tiltWeight (m : ℕ) (mu : ℝ) :
    Integrable (fun c => Phi c * tiltWeight m mu c) :=
  order_integrable_bounded_tiltWeight m mu Phi continuous_Phi order_abs_Phi_le

theorem order_integrable_sigma_Phi_tiltWeight (m : ℕ) (mu : ℝ) :
    Integrable (fun c => sigma c * Phi c * tiltWeight m mu c) :=
  order_integrable_bounded_tiltWeight m mu (fun c => sigma c * Phi c)
    (continuous_sigma.mul continuous_Phi) order_abs_sigma_mul_Phi_le

theorem order_integrable_one_sub_Phi_tiltWeight (m : ℕ) (mu : ℝ) :
    Integrable (fun c => ((1 : ℝ) - Phi c) * tiltWeight m mu c) :=
  order_integrable_bounded_tiltWeight m mu (fun c => (1 : ℝ) - Phi c)
    (continuous_const.sub continuous_Phi) order_abs_one_sub_Phi_le

/-- A value strictly between `0` and `1` is attained by `Phi`. -/
theorem order_exists_Phi_eq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : ∃ c, Phi c = r := by
  obtain ⟨a, ha⟩ := (tendsto_Phi_atBot_basic.eventually (eventually_lt_nhds hr0)).exists
  obtain ⟨b, hb⟩ := (order_tendsto_Phi_atTop.eventually (eventually_gt_nhds hr1)).exists
  exact mem_range_of_exists_le_of_exists_ge continuous_Phi ⟨a, ha.le⟩ ⟨b, hb.le⟩

lemma order_mono_mul_sub_nonneg {f g : ℝ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (a b : ℝ) : 0 ≤ (f a - f b) * (g a - g b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hfa : f a - f b < 0 := sub_neg.mpr (hf hab)
    have hga : g a - g b < 0 := sub_neg.mpr (hg hab)
    have hpos : 0 < -(f a - f b) * -(g a - g b) :=
      mul_pos (neg_pos.mpr hfa) (neg_pos.mpr hga)
    rw [neg_mul_neg] at hpos
    exact hpos.le
  · simp [hab]
  · exact (mul_pos (sub_pos.mpr (hf hab)) (sub_pos.mpr (hg hab))).le

/-- Covariance integrand of the two strictly increasing maps `sigma` and `Phi`. -/
def order_covIntegrand (m : ℕ) (mu cbar : ℝ) : ℝ → ℝ :=
  fun c => (sigma c - sigma cbar) * (Phi c - Phi cbar) * tiltWeight m mu c

lemma order_covIntegrand_nonneg (m : ℕ) (mu cbar c : ℝ) :
    0 ≤ order_covIntegrand m mu cbar c := by
  unfold order_covIntegrand
  exact mul_nonneg
    (order_mono_mul_sub_nonneg strictMono_sigma order_strictMono_Phi c cbar)
    (tiltWeight_pos m mu c).le

lemma order_covIntegrand_pos_add_one (m : ℕ) (mu cbar : ℝ) :
    0 < order_covIntegrand m mu cbar (cbar + 1) := by
  unfold order_covIntegrand
  have hx : cbar < cbar + 1 := lt_add_one cbar
  exact mul_pos
    (mul_pos (sub_pos.mpr (strictMono_sigma hx)) (sub_pos.mpr (order_strictMono_Phi hx)))
    (tiltWeight_pos m mu (cbar + 1))

lemma order_continuous_covIntegrand (m : ℕ) (mu cbar : ℝ) :
    Continuous (order_covIntegrand m mu cbar) := by
  unfold order_covIntegrand
  exact ((continuous_sigma.sub continuous_const).mul
    (continuous_Phi.sub continuous_const)).mul (continuous_tiltWeight m mu)

lemma order_integrable_covIntegrand (m : ℕ) (mu cbar : ℝ) :
    Integrable (order_covIntegrand m mu cbar) := by
  have hs := order_integrable_sigma_tiltWeight m mu
  have hp := order_integrable_Phi_tiltWeight m mu
  have hsp := order_integrable_sigma_Phi_tiltWeight m mu
  have hw := integrable_tiltWeight m mu
  have hEq : order_covIntegrand m mu cbar =
      (fun c => sigma c * Phi c * tiltWeight m mu c) -
        (fun c => Phi cbar * (sigma c * tiltWeight m mu c)) -
        (fun c => sigma cbar * (Phi c * tiltWeight m mu c)) +
        fun c => (sigma cbar * Phi cbar) * tiltWeight m mu c := by
    funext c
    simp only [order_covIntegrand, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hEq]
  exact ((hsp.sub (hs.const_mul (Phi cbar))).sub (hp.const_mul (sigma cbar))).add
    (hw.const_mul (sigma cbar * Phi cbar))

/-- The integrand is continuous, nonnegative, and positive at `cbar + 1`. -/
theorem order_integral_covIntegrand_pos (m : ℕ) (mu cbar : ℝ) :
    0 < ∫ c, order_covIntegrand m mu cbar c := by
  have hnn : 0 ≤ order_covIntegrand m mu cbar := fun c => order_covIntegrand_nonneg m mu cbar c
  have hint := order_integrable_covIntegrand m mu cbar
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  refine (order_continuous_covIntegrand m mu cbar).isOpen_support.measure_pos
    (volume : Measure ℝ) ⟨cbar + 1, ?_⟩
  rw [mem_support]
  exact (order_covIntegrand_pos_add_one m mu cbar).ne'

theorem order_integral_covIntegrand_expand (m : ℕ) (mu cbar : ℝ) :
    ∫ c, order_covIntegrand m mu cbar c =
      (∫ c, sigma c * Phi c * tiltWeight m mu c) -
        Phi cbar * (∫ c, sigma c * tiltWeight m mu c) -
        sigma cbar * (∫ c, Phi c * tiltWeight m mu c) +
        (sigma cbar * Phi cbar) * (∫ c, tiltWeight m mu c) := by
  have hs := order_integrable_sigma_tiltWeight m mu
  have hp := order_integrable_Phi_tiltWeight m mu
  have hsp := order_integrable_sigma_Phi_tiltWeight m mu
  have hw := integrable_tiltWeight m mu
  have h1 : Integrable fun c => sigma c * Phi c * tiltWeight m mu c := hsp
  have h2 : Integrable fun c => Phi cbar * (sigma c * tiltWeight m mu c) :=
    hs.const_mul (Phi cbar)
  have h3 : Integrable fun c => sigma cbar * (Phi c * tiltWeight m mu c) :=
    hp.const_mul (sigma cbar)
  have h4 : Integrable fun c => (sigma cbar * Phi cbar) * tiltWeight m mu c :=
    hw.const_mul (sigma cbar * Phi cbar)
  have h12 : Integrable fun c =>
      sigma c * Phi c * tiltWeight m mu c - Phi cbar * (sigma c * tiltWeight m mu c) :=
    h1.sub h2
  have h123 : Integrable fun c =>
      sigma c * Phi c * tiltWeight m mu c - Phi cbar * (sigma c * tiltWeight m mu c) -
        sigma cbar * (Phi c * tiltWeight m mu c) :=
    h12.sub h3
  calc
    ∫ c, order_covIntegrand m mu cbar c
        = ∫ c, (sigma c * Phi c * tiltWeight m mu c -
            Phi cbar * (sigma c * tiltWeight m mu c) -
            sigma cbar * (Phi c * tiltWeight m mu c)) +
            (sigma cbar * Phi cbar) * tiltWeight m mu c := by
          refine integral_congr_ae (ae_of_all _ fun c => ?_)
          simp only [order_covIntegrand]
          ring
      _ = (∫ c, sigma c * Phi c * tiltWeight m mu c -
            Phi cbar * (sigma c * tiltWeight m mu c) -
            sigma cbar * (Phi c * tiltWeight m mu c)) +
          ∫ c, (sigma cbar * Phi cbar) * tiltWeight m mu c :=
          integral_add h123 h4
      _ = ((∫ c, sigma c * Phi c * tiltWeight m mu c -
            Phi cbar * (sigma c * tiltWeight m mu c)) -
            ∫ c, sigma cbar * (Phi c * tiltWeight m mu c)) +
          ∫ c, (sigma cbar * Phi cbar) * tiltWeight m mu c := by
          rw [integral_sub h12 h3]
      _ = (((∫ c, sigma c * Phi c * tiltWeight m mu c) -
            ∫ c, Phi cbar * (sigma c * tiltWeight m mu c)) -
            ∫ c, sigma cbar * (Phi c * tiltWeight m mu c)) +
          ∫ c, (sigma cbar * Phi cbar) * tiltWeight m mu c := by
          rw [integral_sub h1 h2]
      _ = (((∫ c, sigma c * Phi c * tiltWeight m mu c) -
            Phi cbar * ∫ c, sigma c * tiltWeight m mu c) -
            sigma cbar * ∫ c, Phi c * tiltWeight m mu c) +
          (sigma cbar * Phi cbar) * ∫ c, tiltWeight m mu c := by
          rw [integral_const_mul (Phi cbar) fun c => sigma c * tiltWeight m mu c,
            integral_const_mul (sigma cbar) fun c => Phi c * tiltWeight m mu c,
            integral_const_mul (sigma cbar * Phi cbar) fun c => tiltWeight m mu c]
      _ = (∫ c, sigma c * Phi c * tiltWeight m mu c) -
            Phi cbar * (∫ c, sigma c * tiltWeight m mu c) -
            sigma cbar * (∫ c, Phi c * tiltWeight m mu c) +
            (sigma cbar * Phi cbar) * (∫ c, tiltWeight m mu c) := by
          ring

/-- For `m ≥ 2`, the tilted moment `b` increases at each successor. -/
theorem b_lt_succ (m : ℕ) (mu : ℝ) (hm : 2 ≤ m) : b m mu < b (m + 1) mu := by
  have hZm : 0 < normalizer m mu := normalizer_pos m mu
  have hZm1 : 0 < normalizer (m + 1) mu := normalizer_pos (m + 1) mu
  have hNphi_int := order_integrable_Phi_tiltWeight m mu
  have htail_int := order_integrable_one_sub_Phi_tiltWeight m mu
  have hZid : normalizer m mu = ∫ c, tiltWeight m mu c := rfl
  have hNphi_id : normalizer (m + 1) mu = ∫ c, Phi c * tiltWeight m mu c := by
    simp only [normalizer]
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    exact tiltWeight_succ m mu c hm
  have htail_pos : 0 < ∫ c, ((1 : ℝ) - Phi c) * tiltWeight m mu c :=
    integral_weight_pos
      ((continuous_const.sub continuous_Phi).mul (continuous_tiltWeight m mu))
      (fun c => mul_pos (sub_pos.mpr (Phi_lt_one c)) (tiltWeight_pos m mu c)) htail_int
  have hsplit : normalizer m mu - normalizer (m + 1) mu =
      ∫ c, ((1 : ℝ) - Phi c) * tiltWeight m mu c := by
    rw [hZid, hNphi_id, ← integral_sub (integrable_tiltWeight m mu) hNphi_int]
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    ring
  have hNphi_lt : normalizer (m + 1) mu < normalizer m mu := by
    have hpos : 0 < normalizer m mu - normalizer (m + 1) mu := by
      rw [hsplit]
      exact htail_pos
    linarith
  set Z : ℝ := normalizer m mu
  set Nphi : ℝ := normalizer (m + 1) mu
  set Ns : ℝ := ∫ c, sigma c * tiltWeight m mu c
  set Nsphi : ℝ := ∫ c, sigma c * Phi c * tiltWeight m mu c
  have hr0 : 0 < Nphi / Z := div_pos hZm1 hZm
  have hr1 : Nphi / Z < 1 := (div_lt_one hZm).2 hNphi_lt
  obtain ⟨cbar, hcbar⟩ := order_exists_Phi_eq hr0 hr1
  have hPhiZ : Phi cbar * Z = Nphi := by
    rw [hcbar]
    exact div_mul_cancel₀ Nphi hZm.ne'
  have hKpos : 0 < ∫ c, order_covIntegrand m mu cbar c :=
    order_integral_covIntegrand_pos m mu cbar
  have hKeq := order_integral_covIntegrand_expand m mu cbar
  have hIntW : ∫ c, tiltWeight m mu c = Z := by rw [hZid]
  have hIntPhi : ∫ c, Phi c * tiltWeight m mu c = Nphi := by rw [hNphi_id]
  have hIntSigma : ∫ c, sigma c * tiltWeight m mu c = Ns := rfl
  have hIntSP : ∫ c, sigma c * Phi c * tiltWeight m mu c = Nsphi := rfl
  have hnum : 0 < Nsphi * Z - Ns * Nphi := by
    have hcancel : sigma cbar * Nphi = (sigma cbar * Phi cbar) * Z := by
      rw [← hPhiZ]
      ring
    have hKsimp : ∫ c, order_covIntegrand m mu cbar c = Nsphi - Phi cbar * Ns := by
      rw [hKeq, hIntSP, hIntSigma, hIntW, hIntPhi, hcancel]
      ring
    have hKZ : (∫ c, order_covIntegrand m mu cbar c) * Z = Nsphi * Z - Ns * Nphi := by
      rw [hKsimp]
      calc
        (Nsphi - Phi cbar * Ns) * Z = Nsphi * Z - Phi cbar * Ns * Z := by ring
        _ = Nsphi * Z - Ns * (Phi cbar * Z) := by ring
        _ = Nsphi * Z - Ns * Nphi := by rw [hPhiZ]
    rw [← hKZ]
    exact mul_pos hKpos hZm
  have hratio : Ns / Z < Nsphi / Nphi :=
    (div_lt_div_iff₀ hZm hZm1).2 (sub_pos.mp hnum)
  have hb_left : b m mu = Ns / Z := by
    unfold b tiltedMoment
    rfl
  have hb_right : b (m + 1) mu = Nsphi / Nphi := by
    unfold b tiltedMoment
    have hnum_eq : (∫ c, sigma c * tiltWeight (m + 1) mu c) =
        ∫ c, sigma c * Phi c * tiltWeight m mu c := by
      refine integral_congr_ae (ae_of_all _ fun c => ?_)
      dsimp only
      rw [tiltWeight_succ m mu c hm]
      ring
    rw [hnum_eq]
  rw [hb_left, hb_right]
  exact hratio

/-- For `2 ≤ m ≤ n`, the tilted moment `b` is monotone in the discrete level. -/
theorem b_mono_nat {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) (mu : ℝ) : b m mu ≤ b n mu := by
  suffices ∀ k, b m mu ≤ b (m + k) mu by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
    simpa [hk] using this k
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    exact ih.trans (b_lt_succ (m + k) mu (by omega)).le

#print axioms tiltWeight_succ
#print axioms order_strictMono_Phi
#print axioms order_tendsto_Phi_atTop
#print axioms order_exists_Phi_eq
#print axioms order_integral_covIntegrand_pos
#print axioms order_integral_covIntegrand_expand
#print axioms b_lt_succ
#print axioms b_mono_nat

end SimplexFull
end
