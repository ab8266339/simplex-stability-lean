import SimplexFull.MillsPrep
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section

open Filter Function MeasureTheory Real Set
open scoped Topology

namespace SimplexFull

/-- Mills truncation `1/t - 1/t^3 + 3/t^5 - 15/t^7 + 105/t^9`. -/
def millsP4 (t : ℝ) : ℝ :=
  1 / t - 1 / t ^ 3 + 3 / t ^ 5 - 15 / t ^ 7 + 105 / t ^ 9

/-- One further Mills term. `millsP5 t` may be negative for small `t > 0`. -/
def millsP5 (t : ℝ) : ℝ :=
  millsP4 t - 945 / t ^ 11

def millsP4Deriv (t : ℝ) : ℝ :=
  -1 / t ^ 2 + 3 / t ^ 4 - 15 / t ^ 6 + 105 / t ^ 8 - 945 / t ^ 10

def millsP5Deriv (t : ℝ) : ℝ :=
  millsP4Deriv t + 10395 / t ^ 12

lemma one_div_pow_deriv_simp {n : ℕ} {t : ℝ} (ht : t ≠ 0) :
    -((n : ℝ) * t ^ (n - 1)) / (t ^ n) ^ 2 = -(n : ℝ) / t ^ (n + 1) := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [sq, ← pow_add]
    rw [div_eq_div_iff (pow_ne_zero (n + n) ht) (pow_ne_zero (n + 1) ht)]
    rw [← neg_mul, mul_assoc]
    rw [mul_right_inj' (neg_ne_zero.mpr hn0)]
    rw [← pow_add]
    congr 1
    calc
      n - 1 + (n + 1) = n - 1 + (1 + n) := by rw [Nat.add_comm n 1]
      _ = n - 1 + 1 + n := by rw [← Nat.add_assoc]
      _ = n + n := by rw [Nat.sub_add_cancel hnpos]

lemma hasDerivAt_one_div {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 / s) (-1 / t ^ 2) t := by
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht
  refine (hinv.congr_of_eventuallyEq (Eventually.of_forall fun s => one_div s)).congr_deriv ?_
  field

lemma hasDerivAt_one_div_pow {n : ℕ} {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 / s ^ n) (-(n : ℝ) / t ^ (n + 1)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ n) ((n : ℝ) * t ^ (n - 1)) t :=
    hasDerivAt_pow n t
  have hinv := hpow.inv (pow_ne_zero n ht)
  refine (hinv.congr_of_eventuallyEq
    (Eventually.of_forall fun s => one_div (s ^ n))).congr_deriv
      (one_div_pow_deriv_simp ht)

lemma hasDerivAt_millsP4 {t : ℝ} (ht : t ≠ 0) : HasDerivAt millsP4 (millsP4Deriv t) t := by
  have h1 := hasDerivAt_one_div ht
  have h3 := hasDerivAt_one_div_pow (n := 3) ht
  have h5 := (hasDerivAt_one_div_pow (n := 5) ht).const_mul (3 : ℝ)
  have h7 := (hasDerivAt_one_div_pow (n := 7) ht).const_mul (15 : ℝ)
  have h9 := (hasDerivAt_one_div_pow (n := 9) ht).const_mul (105 : ℝ)
  have h := (((h1.sub h3).add h5).sub h7).add h9
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [millsP4, Pi.add_apply, Pi.sub_apply]
    field
  · unfold millsP4Deriv
    field

lemma hasDerivAt_millsP5 {t : ℝ} (ht : t ≠ 0) : HasDerivAt millsP5 (millsP5Deriv t) t := by
  have h11 := (hasDerivAt_one_div_pow (n := 11) ht).const_mul (945 : ℝ)
  have h := (hasDerivAt_millsP4 ht).sub h11
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [millsP5, Pi.sub_apply]
    field
  · unfold millsP5Deriv
    field

lemma millsP4_deriv_identity {t : ℝ} (ht : t ≠ 0) :
    1 - t * millsP4 t + millsP4Deriv t = -945 / t ^ 10 := by
  unfold millsP4 millsP4Deriv
  field

lemma millsP5_deriv_identity {t : ℝ} (ht : t ≠ 0) :
    1 - t * millsP5 t + millsP5Deriv t = 10395 / t ^ 12 := by
  unfold millsP5 millsP5Deriv millsP4 millsP4Deriv
  field

lemma hasDerivAt_Phi_neg (t : ℝ) : HasDerivAt (fun s : ℝ => Phi (-s)) (-phi t) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := hasDerivAt_neg' t
  refine (HasDerivAt.comp t (hasDerivAt_Phi (-t)) hneg).congr_deriv ?_
  rw [phi_neg_basic]
  ring

theorem hasDerivAt_phi_mul_millsP4_sub_Phi_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => phi s * millsP4 s - Phi (-s)) (-945 * phi t / t ^ 10) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hmul := (hasDerivAt_phi t).mul (hasDerivAt_millsP4 ht0)
  have h := hmul.sub (hasDerivAt_Phi_neg t)
  refine h.congr_deriv ?_
  have hid := millsP4_deriv_identity ht0
  calc
    (-t * phi t) * millsP4 t + phi t * millsP4Deriv t - -phi t
        = phi t * (1 - t * millsP4 t + millsP4Deriv t) := by ring
    _ = phi t * (-945 / t ^ 10) := by rw [hid]
    _ = -945 * phi t / t ^ 10 := by field

theorem hasDerivAt_phi_mul_millsP5_sub_Phi_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => phi s * millsP5 s - Phi (-s)) (10395 * phi t / t ^ 12) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hmul := (hasDerivAt_phi t).mul (hasDerivAt_millsP5 ht0)
  have h := hmul.sub (hasDerivAt_Phi_neg t)
  refine h.congr_deriv ?_
  have hid := millsP5_deriv_identity ht0
  calc
    (-t * phi t) * millsP5 t + phi t * millsP5Deriv t - -phi t
        = phi t * (1 - t * millsP5 t + millsP5Deriv t) := by ring
    _ = phi t * (10395 / t ^ 12) := by rw [hid]
    _ = 10395 * phi t / t ^ 12 := by field

lemma tendsto_phi_atTop_zero : Tendsto phi atTop (𝓝 0) := by
  have hphi : phi = fun t : ℝ => (√(2 * π))⁻¹ * exp (-(t ^ 2) / 2) := by
    funext t
    exact phi_eq_exp t
  rw [hphi]
  have hsq : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
  have hquad : Tendsto (fun t : ℝ => -(t ^ 2) / 2) atTop atBot := by
    have hfun : (fun t : ℝ => -(t ^ 2) / 2) = fun t => (-(1 / 2 : ℝ)) * t ^ 2 := by
      funext t
      ring
    rw [hfun]
    exact hsq.const_mul_atTop_of_neg (by norm_num)
  have hexp : Tendsto (fun t : ℝ => exp (-(t ^ 2) / 2)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp hquad
  simpa [mul_zero] using hexp.const_mul ((√(2 * π))⁻¹)

lemma tendsto_phi_mul_div_pow {c : ℝ} {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun t : ℝ => phi t * (c / t ^ n)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℝ => (t ^ n)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop hn).inv_tendsto_atTop
  have hmul : Tendsto (fun t : ℝ => phi t * (t ^ n)⁻¹) atTop (𝓝 0) := by
    simpa [mul_zero] using tendsto_phi_atTop_zero.mul hpow
  have hconst : Tendsto (fun t : ℝ => c * (phi t * (t ^ n)⁻¹)) atTop (𝓝 0) := by
    simpa [mul_zero] using hmul.const_mul c
  refine hconst.congr fun t => ?_
  rw [div_eq_mul_inv]
  ring

lemma tendsto_zero_add {f g : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun t => f t + g t) atTop (𝓝 0) := by
  simpa [add_zero] using hf.add hg

lemma tendsto_zero_sub {f g : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun t => f t - g t) atTop (𝓝 0) := by
  simpa [sub_zero] using hf.sub hg

lemma tendsto_phi_mul_millsP4_atTop : Tendsto (fun t => phi t * millsP4 t) atTop (𝓝 0) := by
  have h1 := tendsto_phi_mul_div_pow (c := (1 : ℝ)) (n := 1) (by decide)
  have h3 := tendsto_phi_mul_div_pow (c := (1 : ℝ)) (n := 3) (by decide)
  have h5 := tendsto_phi_mul_div_pow (c := (3 : ℝ)) (n := 5) (by decide)
  have h7 := tendsto_phi_mul_div_pow (c := (15 : ℝ)) (n := 7) (by decide)
  have h9 := tendsto_phi_mul_div_pow (c := (105 : ℝ)) (n := 9) (by decide)
  have h := tendsto_zero_add
    (tendsto_zero_sub (tendsto_zero_add (tendsto_zero_sub h1 h3) h5) h7) h9
  refine h.congr fun t => ?_
  simp only [millsP4, div_eq_mul_inv]
  ring

lemma tendsto_phi_mul_millsP5_atTop : Tendsto (fun t => phi t * millsP5 t) atTop (𝓝 0) := by
  have htail := tendsto_phi_mul_div_pow (c := (945 : ℝ)) (n := 11) (by decide)
  have h := tendsto_zero_sub tendsto_phi_mul_millsP4_atTop htail
  refine h.congr fun t => ?_
  simp only [millsP5, div_eq_mul_inv]
  ring

lemma tendsto_Phi_neg_atTop : Tendsto (fun t : ℝ => Phi (-t)) atTop (𝓝 0) := by
  have hneg : Tendsto (fun t : ℝ => -t) atTop atBot := by
    simpa [neg_one_mul] using
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1 : ℝ) < 0))
  simpa [Function.comp_def] using tendsto_Phi_atBot_basic.comp hneg

theorem tendsto_phi_mul_millsP4_sub_Phi_neg_atTop :
    Tendsto (fun t => phi t * millsP4 t - Phi (-t)) atTop (𝓝 0) :=
  tendsto_zero_sub tendsto_phi_mul_millsP4_atTop tendsto_Phi_neg_atTop

theorem tendsto_phi_mul_millsP5_sub_Phi_neg_atTop :
    Tendsto (fun t => phi t * millsP5 t - Phi (-t)) atTop (𝓝 0) :=
  tendsto_zero_sub tendsto_phi_mul_millsP5_atTop tendsto_Phi_neg_atTop

lemma upperGap_deriv_neg {t : ℝ} (ht : 0 < t) : -945 * phi t / t ^ 10 < 0 := by
  have hden : 0 < t ^ 10 := pow_pos ht 10
  have hnum : -945 * phi t < 0 := mul_neg_of_neg_of_pos (by norm_num) (phi_pos t)
  exact div_neg_of_neg_of_pos hnum hden

lemma lowerGap_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < 10395 * phi t / t ^ 12 := by
  exact div_pos (mul_pos (by norm_num) (phi_pos t)) (pow_pos ht 12)

lemma antitoneOn_from_deriv_nonpos {f df : ℝ → ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt f (df t) t)
    (hsign : ∀ t, 0 < t → df t ≤ 0) : AntitoneOn f (Ioi 0) := by
  have hcont : ContinuousOn f (Ioi 0) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0 : ℝ)) hcont (f' := df) ?_ ?_
  · intro x hx
    have hx0 : 0 < x := by simpa [isOpen_Ioi.interior_eq] using hx
    exact (hderiv x hx0).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa [isOpen_Ioi.interior_eq] using hx
    exact hsign x hx0

lemma gap_antitone_nonneg {f df : ℝ → ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt f (df t) t)
    (hsign : ∀ t, 0 < t → df t ≤ 0)
    (hlim : Tendsto f atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  have hanti : AntitoneOn f (Ioi 0) := antitoneOn_from_deriv_nonpos hderiv hsign
  by_contra hlt
  have hlt' : f t < 0 := lt_of_not_ge hlt
  have hε : 0 < -f t := neg_pos.mpr hlt'
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.mp hlim) (-f t) hε
  let s := max B (t + 1)
  have hsB : B ≤ s := le_max_left _ _
  have hst : t < s := by
    have hs1 : t + 1 ≤ s := le_max_right _ _
    linarith
  have hspos : 0 < s := lt_trans ht hst
  have hfs : f s ≤ f t := hanti ht hspos hst.le
  have habs : dist (f s) 0 < -f t := hB s hsB
  rw [Real.dist_0_eq_abs] at habs
  have hneg : f s < 0 := lt_of_le_of_lt hfs hlt'
  rw [abs_of_neg hneg] at habs
  linarith

lemma gap_monotone_nonpos {f df : ℝ → ℝ}
    (hderiv : ∀ t, 0 < t → HasDerivAt f (df t) t)
    (hsign : ∀ t, 0 < t → 0 ≤ df t)
    (hlim : Tendsto f atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) : f t ≤ 0 := by
  have hneg : ∀ t, 0 < t → HasDerivAt (fun s => -f s) (-df t) t :=
    fun t ht => (hderiv t ht).neg
  have hsign' : ∀ t, 0 < t → -df t ≤ 0 := fun t ht => neg_nonpos.mpr (hsign t ht)
  have hlim' : Tendsto (fun s => -f s) atTop (𝓝 0) := by simpa [neg_zero] using hlim.neg
  have h := gap_antitone_nonneg hneg hsign' hlim' ht
  linarith

theorem antitoneOn_phi_mul_millsP4_sub_Phi_neg :
    AntitoneOn (fun t => phi t * millsP4 t - Phi (-t)) (Ioi 0) :=
  antitoneOn_from_deriv_nonpos
    (fun _ ht => hasDerivAt_phi_mul_millsP4_sub_Phi_neg ht)
    (fun _ ht => (upperGap_deriv_neg ht).le)

theorem monotoneOn_phi_mul_millsP5_sub_Phi_neg :
    MonotoneOn (fun t => phi t * millsP5 t - Phi (-t)) (Ioi 0) := by
  have hanti : AntitoneOn (fun t => -(phi t * millsP5 t - Phi (-t))) (Ioi 0) :=
    antitoneOn_from_deriv_nonpos
      (fun _ ht => (hasDerivAt_phi_mul_millsP5_sub_Phi_neg ht).neg)
      (fun _ ht => neg_nonpos.mpr (lowerGap_deriv_pos ht).le)
  intro x hx y hy hxy
  have h := hanti hx hy hxy
  linarith

theorem phi_mul_millsP5_le_Phi_neg {t : ℝ} (ht : 0 < t) :
    phi t * millsP5 t ≤ Phi (-t) := by
  have h := gap_monotone_nonpos
    (fun s hs => hasDerivAt_phi_mul_millsP5_sub_Phi_neg hs)
    (fun s hs => (lowerGap_deriv_pos hs).le)
    tendsto_phi_mul_millsP5_sub_Phi_neg_atTop ht
  linarith

theorem Phi_neg_le_phi_mul_millsP4 {t : ℝ} (ht : 0 < t) :
    Phi (-t) ≤ phi t * millsP4 t := by
  have h := gap_antitone_nonneg
    (fun s hs => hasDerivAt_phi_mul_millsP4_sub_Phi_neg hs)
    (fun s hs => (upperGap_deriv_neg hs).le)
    tendsto_phi_mul_millsP4_sub_Phi_neg_atTop ht
  linarith

theorem mills_ratio_bounds {t : ℝ} (ht : 0 < t) :
    millsP5 t ≤ Phi (-t) / phi t ∧ Phi (-t) / phi t ≤ millsP4 t := by
  constructor
  · rw [le_div_iff₀ (phi_pos t)]
    simpa [mul_comm] using phi_mul_millsP5_le_Phi_neg ht
  · rw [div_le_iff₀ (phi_pos t)]
    simpa [mul_comm] using Phi_neg_le_phi_mul_millsP4 ht

#print axioms hasDerivAt_phi_mul_millsP4_sub_Phi_neg
#print axioms hasDerivAt_phi_mul_millsP5_sub_Phi_neg
#print axioms tendsto_phi_mul_millsP4_sub_Phi_neg_atTop
#print axioms tendsto_phi_mul_millsP5_sub_Phi_neg_atTop
#print axioms phi_mul_millsP5_le_Phi_neg
#print axioms Phi_neg_le_phi_mul_millsP4
#print axioms mills_ratio_bounds

end SimplexFull
