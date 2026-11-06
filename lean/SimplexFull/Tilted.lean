import SimplexFull.GaussianBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Set
namespace SimplexFull

def tiltWeight (m : ℕ) (mu c : ℝ) : ℝ :=
  Real.exp (mu * c) * phi c ^ 2 * Phi c ^ (m - 2)

def normalizer (m : ℕ) (mu : ℝ) : ℝ := ∫ c, tiltWeight m mu c

def tiltedMoment (m : ℕ) (mu : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ c, f c * tiltWeight m mu c) / normalizer m mu

def a (m : ℕ) (mu : ℝ) : ℝ := tiltedMoment m mu (fun c => h c ^ 2)
def b (m : ℕ) (mu : ℝ) : ℝ := tiltedMoment m mu sigma
def H (m : ℕ) (mu : ℝ) : ℝ := tiltedMoment m mu h

def tiltEnvelopeConstant (mu : ℝ) : ℝ :=
  ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * Real.exp (mu ^ 2 / 2)

theorem phi_formula_tilt (c : ℝ) :
    phi c = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c ^ 2 / 2) := by
  simp [phi, ProbabilityTheory.gaussianPDFReal]

theorem exp_mul_phi_sq_identity (mu c : ℝ) :
    Real.exp (mu * c) * phi c ^ 2 =
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * Real.exp (mu * c - c ^ 2) := by
  rw [phi_formula_tilt]
  calc
    Real.exp (mu * c) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-c ^ 2 / 2)) ^ 2 =
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 *
        (Real.exp (mu * c) * (Real.exp (-c ^ 2 / 2) * Real.exp (-c ^ 2 / 2))) := by ring
    _ = ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * Real.exp (mu * c - c ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem exp_mul_phi_sq_le_envelope (mu c : ℝ) :
    Real.exp (mu * c) * phi c ^ 2 ≤
      tiltEnvelopeConstant mu * Real.exp (-(1 / 2 : ℝ) * c ^ 2) := by
  rw [exp_mul_phi_sq_identity]
  have hex : mu * c - c ^ 2 ≤ mu ^ 2 / 2 - c ^ 2 / 2 := by
    nlinarith [sq_nonneg (mu - c)]
  calc
    ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * Real.exp (mu * c - c ^ 2) ≤
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * Real.exp (mu ^ 2 / 2 - c ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (sq_nonneg _)
    _ = tiltEnvelopeConstant mu * Real.exp (-(1 / 2 : ℝ) * c ^ 2) := by
      unfold tiltEnvelopeConstant
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem integrable_abs_pow_exp_mul_phi_sq (n : ℕ) (mu : ℝ) :
    Integrable (fun c : ℝ => |c| ^ n * (Real.exp (mu * c) * phi c ^ 2)) := by
  have hp : Integrable (fun c : ℝ => c ^ n * Real.exp (-(1 / 2 : ℝ) * c ^ 2)) := by
    simpa using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
        (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)))
  have ha : Integrable (fun c : ℝ => |c| ^ n * Real.exp (-(1 / 2 : ℝ) * c ^ 2)) := by
    simpa only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using hp.abs
  refine (ha.const_mul (tiltEnvelopeConstant mu)).mono' ?_ (ae_of_all _ ?_)
  · exact ((continuous_abs.pow n).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_phi.pow 2))).aestronglyMeasurable
  · intro c
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |c| ^ n * (Real.exp (mu * c) * phi c ^ 2))]
    calc
      |c| ^ n * (Real.exp (mu * c) * phi c ^ 2) ≤
        |c| ^ n * (tiltEnvelopeConstant mu * Real.exp (-(1 / 2 : ℝ) * c ^ 2)) :=
          mul_le_mul_of_nonneg_left (exp_mul_phi_sq_le_envelope mu c) (by positivity)
      _ = tiltEnvelopeConstant mu * (|c| ^ n * Real.exp (-(1 / 2 : ℝ) * c ^ 2)) := by ring

theorem integrable_exp_mul_phi_sq (mu : ℝ) :
    Integrable (fun c : ℝ => Real.exp (mu * c) * phi c ^ 2) := by
  simpa using integrable_abs_pow_exp_mul_phi_sq 0 mu

#print axioms exp_mul_phi_sq_identity
#print axioms exp_mul_phi_sq_le_envelope
#print axioms integrable_abs_pow_exp_mul_phi_sq

theorem tiltWeight_pos (m : ℕ) (mu c : ℝ) : 0 < tiltWeight m mu c := by
  unfold tiltWeight
  exact mul_pos (mul_pos (Real.exp_pos _) (pow_pos (phi_pos c) 2))
    (pow_pos (Phi_pos c) (m - 2))

theorem continuous_tiltWeight (m : ℕ) (mu : ℝ) : Continuous (tiltWeight m mu) := by
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_phi.pow 2)).mul (continuous_Phi.pow (m - 2))

theorem integrable_abs_pow_tiltWeight (m n : ℕ) (mu : ℝ) :
    Integrable (fun c : ℝ => |c| ^ n * tiltWeight m mu c) := by
  refine (integrable_abs_pow_exp_mul_phi_sq n mu).mono'
    ((continuous_abs.pow n).mul (continuous_tiltWeight m mu)).aestronglyMeasurable
    (ae_of_all _ ?_)
  intro c
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (tiltWeight_pos m mu c).le)]
  have hp : Phi c ^ (m - 2) ≤ 1 := pow_le_one₀ (Phi_pos c).le (Phi_lt_one c).le
  calc
    |c| ^ n * tiltWeight m mu c =
      (|c| ^ n * (Real.exp (mu * c) * phi c ^ 2)) * Phi c ^ (m - 2) := by
        unfold tiltWeight
        ring
    _ ≤ |c| ^ n * (Real.exp (mu * c) * phi c ^ 2) :=
      mul_le_of_le_one_right (by positivity) hp

theorem integrable_tiltWeight (m : ℕ) (mu : ℝ) : Integrable (tiltWeight m mu) := by
  simpa using integrable_abs_pow_tiltWeight m 0 mu

theorem normalizer_pos (m : ℕ) (mu : ℝ) : 0 < normalizer m mu := by
  unfold normalizer
  rw [integral_pos_iff_support_of_nonneg
    (fun c => (tiltWeight_pos m mu c).le) (integrable_tiltWeight m mu)]
  have hs : Function.support (tiltWeight m mu) = Set.univ := by
    ext c
    simp only [Function.mem_support, ne_eq, (tiltWeight_pos m mu c).ne',
      not_false_eq_true, Set.mem_univ]
  simp [hs]

theorem tiltedMoment_one (m : ℕ) (mu : ℝ) :
    tiltedMoment m mu (fun _ => 1) = 1 := by
  unfold tiltedMoment
  simp only [one_mul]
  change normalizer m mu / normalizer m mu = 1
  exact div_self (normalizer_pos m mu).ne'

theorem integrable_mul_tiltWeight (m : ℕ) (mu : ℝ) :
    Integrable (fun c : ℝ => c * tiltWeight m mu c) := by
  apply (integrable_abs_pow_tiltWeight m 1 mu).mono'
    (continuous_id.mul (continuous_tiltWeight m mu)).aestronglyMeasurable
  filter_upwards [] with c
  simp only [Pi.mul_apply, id_eq, Real.norm_eq_abs, abs_mul, abs_of_pos (tiltWeight_pos m mu c), pow_one]
  exact le_rfl

theorem integrable_polynomial_bound_tiltWeight
    (m : ℕ) (mu : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume)
    (C : ℝ) (n : ℕ)
    (hbound : ∀ c, |f c| ≤ C * (1 + |c| ^ n)) :
    Integrable (fun c => f c * tiltWeight m mu c) := by
  have hi : Integrable (fun c : ℝ =>
      C * (tiltWeight m mu c + |c| ^ n * tiltWeight m mu c)) :=
    ((integrable_tiltWeight m mu).add (integrable_abs_pow_tiltWeight m n mu)).const_mul C
  apply hi.mono' (hf.mul (continuous_tiltWeight m mu).aestronglyMeasurable)
  filter_upwards [] with c
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tiltWeight_pos m mu c)]
  calc
    |f c| * tiltWeight m mu c ≤ C * (1 + |c| ^ n) * tiltWeight m mu c :=
      mul_le_mul_of_nonneg_right (hbound c) (tiltWeight_pos m mu c).le
    _ = C * (tiltWeight m mu c + |c| ^ n * tiltWeight m mu c) := by ring

#print axioms integrable_abs_pow_tiltWeight
#print axioms normalizer_pos
#print axioms integrable_polynomial_bound_tiltWeight

theorem hasDerivAt_tiltWeight_mu (m : ℕ) (mu c : ℝ) :
    HasDerivAt (fun t => tiltWeight m t c) (c * tiltWeight m mu c) mu := by
  have hx : HasDerivAt (fun t : ℝ => Real.exp (t * c)) (Real.exp (mu * c) * c) mu := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id mu).mul_const c).exp
  have hh := (hx.mul_const (phi c ^ 2)).mul_const (Phi c ^ (m - 2))
  have he : Real.exp (mu * c) * c * phi c ^ 2 * Phi c ^ (m - 2) =
      c * tiltWeight m mu c := by unfold tiltWeight; ring
  try simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat] at hh
  rw [he] at hh
  exact hh

theorem tiltWeight_le_endpoints (m : ℕ) (mu t c : ℝ)
    (ht : mu - 1 ≤ t ∧ t ≤ mu + 1) :
    tiltWeight m t c ≤ tiltWeight m (mu - 1) c + tiltWeight m (mu + 1) c := by
  have hphi : 0 ≤ phi c ^ 2 := sq_nonneg _
  have hPhi : 0 ≤ Phi c ^ (m - 2) := pow_nonneg (Phi_pos c).le _
  by_cases hc : 0 ≤ c
  · have hex : Real.exp (t * c) ≤ Real.exp ((mu + 1) * c) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2 hc)
    have hw : tiltWeight m t c ≤ tiltWeight m (mu + 1) c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hex hphi) hPhi
    exact hw.trans (le_add_of_nonneg_left (tiltWeight_pos m (mu - 1) c).le)
  · have hex : Real.exp (t * c) ≤ Real.exp ((mu - 1) * c) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ht.1 (le_of_lt (lt_of_not_ge hc)))
    have hw : tiltWeight m t c ≤ tiltWeight m (mu - 1) c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hex hphi) hPhi
    exact hw.trans (le_add_of_nonneg_right (tiltWeight_pos m (mu + 1) c).le)

theorem integrable_pow_mul_polynomial_bound_tiltWeight
    (m k : ℕ) (mu : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume)
    (C : ℝ) (n : ℕ)
    (hbound : ∀ c, |f c| ≤ C * (1 + |c| ^ n)) :
    Integrable (fun c : ℝ => c ^ k * f c * tiltWeight m mu c) := by
  have hi : Integrable (fun c : ℝ =>
      C * (|c| ^ k * tiltWeight m mu c + |c| ^ (k + n) * tiltWeight m mu c)) :=
    ((integrable_abs_pow_tiltWeight m k mu).add
      (integrable_abs_pow_tiltWeight m (k + n) mu)).const_mul C
  refine hi.mono'
    (((continuous_id.pow k).aestronglyMeasurable.mul hf).mul
      (continuous_tiltWeight m mu).aestronglyMeasurable) (ae_of_all _ ?_)
  intro c
  try simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_pos (tiltWeight_pos m mu c)]
  calc
    |c| ^ k * |f c| * tiltWeight m mu c ≤
      |c| ^ k * (C * (1 + |c| ^ n)) * tiltWeight m mu c :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound c) (by positivity))
          (tiltWeight_pos m mu c).le
    _ = C * (|c| ^ k * tiltWeight m mu c + |c| ^ (k + n) * tiltWeight m mu c) := by
      rw [pow_add]
      ring

#print axioms hasDerivAt_tiltWeight_mu
#print axioms tiltWeight_le_endpoints
#print axioms integrable_pow_mul_polynomial_bound_tiltWeight

theorem hasDerivAt_Phi_pow_tilt (n : ℕ) (c : ℝ) :
    HasDerivAt (fun x => Phi x ^ n) ((n : ℝ) * q c * Phi c ^ n) c := by
  have hh := (hasDerivAt_Phi c).pow n
  have he : (n : ℝ) * Phi c ^ (n - 1) * phi c = (n : ℝ) * q c * Phi c ^ n := by
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.succ_sub_one, pow_succ]
      unfold q
      field_simp [(Phi_pos c).ne']
      <;> ring
  try simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat] at hh
  rw [he] at hh
  exact hh

theorem hasDerivAt_tiltWeight_x (m : ℕ) (mu c : ℝ) :
    HasDerivAt (tiltWeight m mu)
      ((mu - 2 * c + ((m - 2 : ℕ) : ℝ) * q c) * tiltWeight m mu c) c := by
  have hex : HasDerivAt (fun x : ℝ => Real.exp (mu * x)) (Real.exp (mu * c) * mu) c := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id c).const_mul mu).exp
  have hp := (hasDerivAt_phi c).pow 2
  have hpp := hasDerivAt_Phi_pow_tilt (m - 2) c
  have hh := (hex.mul hp).mul hpp
  have he :
      (Real.exp (mu * c) * mu * phi c ^ 2 +
        Real.exp (mu * c) * ((2 : ℝ) * phi c ^ (2 - 1) * (-c * phi c))) *
          Phi c ^ (m - 2) +
      (Real.exp (mu * c) * phi c ^ 2) *
        (((m - 2 : ℕ) : ℝ) * q c * Phi c ^ (m - 2)) =
      (mu - 2 * c + ((m - 2 : ℕ) : ℝ) * q c) * tiltWeight m mu c := by
    unfold tiltWeight
    ring
  try simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat] at hh
  rw [he] at hh
  exact hh

theorem balance_factor_identity (m mu c : ℝ) :
    sigma c + h c * (mu - 2 * c + (m - 2) * q c) =
      m + mu * h c - 2 * h c ^ 2 - (m - 1) * sigma c := by
  unfold sigma h
  ring

#print axioms hasDerivAt_Phi_pow_tilt
#print axioms hasDerivAt_tiltWeight_x
#print axioms balance_factor_identity
end SimplexFull
