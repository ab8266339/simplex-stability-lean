import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Filter Set
namespace WeakSimplexPilot

def L0 (m a : ℝ) : ℝ := (m - 1) * a / m
def L1 (m a b : ℝ) : ℝ := (a + (m - 2) * b) / 2
def Lp (m : ℝ) : ℝ := (m - 1) / 2

-- Frozen propositions only. No proofs or placeholders are asserted here.
def T1 : Prop :=
  ∀ h s : ℝ, 0 < h → 0 < s → s < 1 →
    s + s^2 - (1-s)*h^2 = 0 →
    ((1+2*s+h^2) * ((1-s)*(h^2-s)/h) - 2*h*(1-s)*s
      = 4*s^3/(h*(1-s))) ∧
    0 < 4*s^3/(h*(1-s))

def T2 : Prop :=
  ∀ m a b : ℝ, 4 ≤ m → 0 < a → (1:ℝ)/2 < b → b < 1 →
    ((a = m/2 → L0 m a = Lp m ∧ Lp m < L1 m a b) ∧
     (a = m*b → L0 m a = L1 m a b ∧ Lp m < L0 m a) ∧
     min (L0 m a) (Lp m) < L1 m a b)

def T3 : Prop :=
  ∀ (m : ℝ) (a b : ℝ → ℝ),
    4 ≤ m →
    ContinuousOn a (Ici 0) →
    ContinuousOn b (Ici 0) →
    StrictMonoOn a (Ici 0) →
    StrictMonoOn (fun t => a t / b t) (Ici 0) →
    StrictMonoOn (fun t => a t + (m-2)*b t) (Ici 0) →
    (∀ t ∈ Ici (0:ℝ), 0 < a t ∧ (1:ℝ)/2 < b t ∧ b t < 1) →
    Tendsto a atTop atTop →
    a 0 < m/2 →
    a 0 / b 0 < m →
    a 0 + (m-2)*b 0 < m-1 →
    ∃ t1 t0 t01 : ℝ,
      0 < t1 ∧ t1 < t0 ∧ t0 < t01 ∧
      a t1 + (m-2)*b t1 = m-1 ∧
      a t0 = m/2 ∧
      a t01 = m*b t01 ∧
      (∀ t ∈ Ici (0:ℝ), a t + (m-2)*b t = m-1 → t = t1) ∧
      (∀ t ∈ Ici (0:ℝ), a t = m/2 → t = t0) ∧
      (∀ t ∈ Ici (0:ℝ), a t = m*b t → t = t01)

end WeakSimplexPilot

namespace WeakSimplexPilot

theorem proof_T1 : T1 := by
  intro h s hh hs hs1 he
  have h1pos : 0 < 1 - s := by linarith
  have hh0 : Ne h 0 := ne_of_gt hh
  have h1s : Ne (1 - s) 0 := ne_of_gt h1pos
  constructor
  · field_simp [hh0, h1s]
    linear_combination -((1 - s) * h ^ 2 + s + s ^ 2 + (1 - s) ^ 2) * he
  · positivity

theorem proof_T2 : T2 := by
  intro m a b hm ha hb1 hb
  have hmpos : 0 < m := by linarith
  have hmne : Ne m 0 := ne_of_gt hmpos
  have h2pos : (0 : ℝ) < 2 := by linarith
  have h2ne : Ne (2 : ℝ) 0 := ne_of_gt h2pos
  have hb2 : 1 < b * 2 := (div_lt_iff₀ h2pos).mp hb1
  have hm2 : 0 < m - 2 := by linarith
  have hbdiff : 0 < b * 2 - 1 := by linarith
  constructor
  · intro haeq
    subst haeq
    constructor
    · dsimp only [L0, Lp]
      field_simp [hmne]
    · dsimp only [Lp, L1]
      rw [div_lt_div_iff_of_pos_right h2pos]
      have hid : (m / 2 + (m - 2) * b) - (m - 1) =
          (m - 2) * (b * 2 - 1) / 2 := by
        field_simp [h2ne]
        ring
      have hpos : 0 < (m - 2) * (b * 2 - 1) / 2 :=
        div_pos (mul_pos hm2 hbdiff) h2pos
      linarith [hid, hpos]
  constructor
  · intro haeq
    subst haeq
    constructor
    · dsimp only [L0, L1]
      field_simp [hmne]
      ring
    · dsimp only [Lp, L0]
      rw [div_lt_div_iff₀ h2pos hmpos]
      have hposm : 0 < (m - 1) * m := mul_pos (by linarith) hmpos
      have hstep : (m - 1) * m * 1 < (m - 1) * m * (b * 2) :=
        mul_lt_mul_of_pos_left hb2 hposm
      rw [mul_one] at hstep
      have hid : (m - 1) * (m * b) * 2 = (m - 1) * m * (b * 2) := by ring
      linarith [hstep, hid]
  · rcases le_or_gt a (m / 2) with hle | hgt
    · have hle2 : a * 2 ≤ m := (le_div_iff₀ h2pos).mp hle
      have hbnonneg : 0 ≤ b := by linarith
      have ha_lt_mb : a < m * b := by
        have hstep : a * 1 < a * (b * 2) := mul_lt_mul_of_pos_left hb2 ha
        rw [mul_one] at hstep
        have hstep2 : a * (b * 2) ≤ m * b := by
          calc
            a * (b * 2) = (a * 2) * b := by ring
            _ ≤ m * b := mul_le_mul_of_nonneg_right hle2 hbnonneg
        exact lt_of_lt_of_le hstep hstep2
      have hL0 : L0 m a < L1 m a b := by
        dsimp only [L0, L1]
        rw [div_lt_div_iff₀ hmpos h2pos]
        have hgap : 0 < m * b - a := by linarith
        have hpos : 0 < (m - 2) * (m * b - a) := mul_pos hm2 hgap
        have hid : (a + (m - 2) * b) * m - (m - 1) * a * 2 =
            (m - 2) * (m * b - a) := by ring
        linarith [hid, hpos]
      exact lt_of_le_of_lt (min_le_left (L0 m a) (Lp m)) hL0
    · have hgt2 : m < a * 2 := (div_lt_iff₀ h2pos).mp hgt
      have hLp : Lp m < L1 m a b := by
        dsimp only [Lp, L1]
        rw [div_lt_div_iff_of_pos_right h2pos]
        have hdifa : 0 < a * 2 - m := by linarith
        have hpos : 0 < (a * 2 - m) + (m - 2) * (b * 2 - 1) :=
          add_pos hdifa (mul_pos hm2 hbdiff)
        have hid : 2 * (a + (m - 2) * b) - 2 * (m - 1) =
            (a * 2 - m) + (m - 2) * (b * 2 - 1) := by ring
        linarith [hid, hpos, hgt2]
      exact lt_of_le_of_lt (min_le_right (L0 m a) (Lp m)) hLp

lemma exists_unique_level_Ici {f : ℝ → ℝ} {c : ℝ}
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_mono : StrictMonoOn f (Ici (0 : ℝ)))
    (hf0 : f 0 < c) (hf_top : Tendsto f atTop atTop) :
    ∃ t : ℝ, 0 < t ∧ f t = c ∧ ∀ s, s ∈ Ici (0 : ℝ) → f s = c → s = t := by
  obtain ⟨T, hT_ge, hT_val⟩ := exists_lt_of_tendsto_atTop hf_top 0 c
  have hsub : Icc (0 : ℝ) T ⊆ Ici (0 : ℝ) := fun _ hx => hx.1
  have hc_mem : c ∈ Icc (f 0) (f T) := ⟨le_of_lt hf0, le_of_lt hT_val⟩
  have himg : c ∈ f '' Icc (0 : ℝ) T :=
    intermediate_value_Icc hT_ge (hf_cont.mono hsub) hc_mem
  obtain ⟨t, ht, ht_eq⟩ := (mem_image _ _ _).1 himg
  have ht_mem : t ∈ Ici (0 : ℝ) := ht.1
  have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := (le_rfl : (0 : ℝ) ≤ 0)
  have ht_pos : 0 < t :=
    (hf_mono.lt_iff_lt h0mem ht_mem).1 (lt_of_lt_of_eq hf0 ht_eq.symm)
  refine ⟨t, ht_pos, ht_eq, ?_⟩
  intro s hs hs_eq
  exact (hf_mono.eq_iff_eq hs ht_mem).1 (hs_eq.trans ht_eq.symm)

theorem proof_T3 : T3 := by
  intro m a b hm ha_cont hb_cont ha_mono hr_mono hg_mono hbnd ha_top ha0 hr0 hg0
  have hmpos : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have h2pos : (0 : ℝ) < 2 := by linarith
  have hratio_cont : ContinuousOn (fun t => a t / b t) (Ici (0 : ℝ)) :=
    ha_cont.div hb_cont fun t ht => by
      have hbt : (1 : ℝ) / 2 < b t := (hbnd t ht).2.1
      linarith
  have hg_cont : ContinuousOn (fun t => a t + (m - 2) * b t) (Ici (0 : ℝ)) :=
    ha_cont.add (hb_cont.const_mul (m - 2))
  have hr_top : Tendsto (fun t => a t / b t) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro C
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp ha_top) (max C 0)
    refine ⟨max i 0, ?_⟩
    intro t ht
    have hti : i ≤ t := le_trans (le_max_left i 0) ht
    have ht0 : (0 : ℝ) ≤ t := le_trans (le_max_right i 0) ht
    have ha_ge : max C 0 ≤ a t := hi t hti
    have hb := hbnd t ht0
    have hbp : 0 < b t := by linarith
    have hab : a t * b t < a t := by
      have hlt : a t * b t < a t * 1 := mul_lt_mul_of_pos_left hb.2.2 hb.1
      simpa using hlt
    have hineq : a t * b t / b t ≤ a t / b t := by
      rw [div_le_div_iff_of_pos_right hbp]
      exact le_of_lt hab
    have hid : a t * b t / b t = a t := by
      field_simp [ne_of_gt hbp]
    have hC : C ≤ max C 0 := le_max_left C 0
    linarith
  have hg_top : Tendsto (fun t => a t + (m - 2) * b t) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro C
    obtain ⟨i, hi⟩ := (tendsto_atTop_atTop.mp ha_top) C
    refine ⟨max i 0, ?_⟩
    intro t ht
    have hti : i ≤ t := le_trans (le_max_left i 0) ht
    have ht0 : (0 : ℝ) ≤ t := le_trans (le_max_right i 0) ht
    have ha_ge : C ≤ a t := hi t hti
    have hb := hbnd t ht0
    have hnn : 0 ≤ (m - 2) * b t :=
      mul_nonneg (le_of_lt hm2) (le_of_lt (by linarith : 0 < b t))
    linarith
  obtain ⟨t0, ht0pos, ht0eq, ht0uniq⟩ :=
    exists_unique_level_Ici ha_cont ha_mono ha0 ha_top
  obtain ⟨t01, ht01pos, ht01eq, ht01uniq⟩ :=
    exists_unique_level_Ici hratio_cont hr_mono hr0 hr_top
  obtain ⟨t1, ht1pos, ht1eq, ht1uniq⟩ :=
    exists_unique_level_Ici hg_cont hg_mono hg0 hg_top
  have ht0mem : t0 ∈ Ici (0 : ℝ) := le_of_lt ht0pos
  have ht1mem : t1 ∈ Ici (0 : ℝ) := le_of_lt ht1pos
  have ht01mem : t01 ∈ Ici (0 : ℝ) := le_of_lt ht01pos
  have hg_t0 : m - 1 < a t0 + (m - 2) * b t0 := by
    rw [ht0eq]
    have hbgt : (1 : ℝ) / 2 < b t0 := (hbnd t0 ht0mem).2.1
    have hb2 : 1 < b t0 * 2 := (div_lt_iff₀ h2pos).mp hbgt
    have hpos : 0 < (m - 2) * (b t0 * 2 - 1) / 2 :=
      div_pos (mul_pos hm2 (by linarith)) h2pos
    have hid : (m / 2 + (m - 2) * b t0) - (m - 1) =
        (m - 2) * (b t0 * 2 - 1) / 2 := by
      field_simp [ne_of_gt h2pos]
      ring
    linarith [hid, hpos]
  have hf_t0 : a t0 / b t0 < m := by
    rw [ht0eq]
    have hbgt : (1 : ℝ) / 2 < b t0 := (hbnd t0 ht0mem).2.1
    have hbpos : 0 < b t0 := by linarith
    rw [div_lt_iff₀ hbpos]
    have hb2 : 1 < b t0 * 2 := (div_lt_iff₀ h2pos).mp hbgt
    have hstep : m * 1 < m * (b t0 * 2) := mul_lt_mul_of_pos_left hb2 hmpos
    rw [mul_one] at hstep
    have hid : m * b t0 * 2 = m * (b t0 * 2) := by ring
    rw [div_lt_iff₀ h2pos]
    linarith
  have ht1_lt_t0 : t1 < t0 :=
    (hg_mono.lt_iff_lt ht1mem ht0mem).1 (by linarith [ht1eq, hg_t0])
  have ht0_lt_t01 : t0 < t01 :=
    (hr_mono.lt_iff_lt ht0mem ht01mem).1 (by linarith [hf_t0, ht01eq])
  have hb01 : 0 < b t01 := by
    have hhalf : (1 : ℝ) / 2 < b t01 := (hbnd t01 ht01mem).2.1
    linarith
  have ht01_prod : a t01 = m * b t01 := by
    have hdiv : a t01 / b t01 = m := ht01eq
    field_simp [ne_of_gt hb01] at hdiv
    rw [mul_comm] at hdiv
    exact hdiv
  have huniq01 : ∀ t, t ∈ Ici (0 : ℝ) → a t = m * b t → t = t01 := by
    intro t ht heq
    have hbpos : 0 < b t := by
      have hhalf : (1 : ℝ) / 2 < b t := (hbnd t ht).2.1
      linarith
    have hdiv : a t / b t = m := by
      field_simp [ne_of_gt hbpos]
      rw [mul_comm]
      exact heq
    exact ht01uniq t ht hdiv
  refine ⟨t1, t0, t01, ht1pos, ht1_lt_t0, ht0_lt_t01, ht1eq, ht0eq, ht01_prod,
    ?_, ?_, huniq01⟩
  · intro t ht heq
    exact ht1uniq t ht heq
  · intro t ht heq
    exact ht0uniq t ht heq

#print axioms proof_T1
#print axioms proof_T2
#print axioms proof_T3
#check proof_T1
#check proof_T2
#check proof_T3

end WeakSimplexPilot

end

open Filter Set
open scoped Topology

namespace WeakSimplexPilot

theorem balance_linear_lower
    (m H0 : ℝ) (a b H : ℝ → ℝ)
    (hm : 1 < m) (_hH0 : 0 < H0)
    (hb : ∀ t, 0 ≤ t → b t < 1)
    (hH : ∀ t, 0 ≤ t → H0 ≤ H t)
    (hbal : ∀ t, 0 ≤ t → 2 * a t + (m - 1) * b t = m + t * H t)
    {t : ℝ} (ht : 0 ≤ t) :
    1 + t * H0 < 2 * a t := by
  have hm1 : 0 < m - 1 := by linarith
  have heq := hbal t ht
  have hsub : (m - 1) * b t < m - 1 := by
    have hlt : (m - 1) * b t < (m - 1) * 1 := mul_lt_mul_of_pos_left (hb t ht) hm1
    rw [mul_one] at hlt
    exact hlt
  have hgt : 1 + t * H t < 2 * a t := by
    linarith [heq, hsub]
  have hHt : t * H0 ≤ t * H t := mul_le_mul_of_nonneg_left (hH t ht) ht
  linarith [hgt, hHt]

theorem growth_from_balance
    (m H0 : ℝ) (a b H : ℝ → ℝ)
    (hm : 1 < m) (hH0 : 0 < H0)
    (hb : ∀ t, 0 ≤ t → b t < 1)
    (hH : ∀ t, 0 ≤ t → H0 ≤ H t)
    (hbal : ∀ t, 0 ≤ t → 2 * a t + (m - 1) * b t = m + t * H t) :
    Tendsto a atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨max 0 ((2 * B - 1) / H0), ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (le_max_left 0 ((2 * B - 1) / H0)) ht
  have htcut : (2 * B - 1) / H0 ≤ t :=
    le_trans (le_max_right 0 ((2 * B - 1) / H0)) ht
  have hlow := balance_linear_lower m H0 a b H hm hH0 hb hH hbal ht0
  have hscale : 2 * B - 1 ≤ t * H0 := (div_le_iff₀ hH0).mp htcut
  have htwo : 2 * B ≤ 1 + t * H0 := by linarith
  have : B < a t := by linarith [hlow, htwo]
  exact le_of_lt this

theorem triangular_prod_strictMonoOn
    {H : ℝ → ℝ}
    (hmono : MonotoneOn H (Ici (0 : ℝ)))
    (hpos : ∀ t, 0 ≤ t → 0 < H t) :
    StrictMonoOn (fun t => t * H t) (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hHt : 0 < H t := hpos t ht
  have hleft : s * H s ≤ s * H t := mul_le_mul_of_nonneg_left (hmono hs ht hst.le) hs
  have hright : s * H t < t * H t := mul_lt_mul_of_pos_right hst hHt
  exact lt_of_le_of_lt hleft hright

theorem triangular_switch
    {H : ℝ → ℝ}
    (hcont : ContinuousOn H (Ici (0 : ℝ)))
    (hmono : MonotoneOn H (Ici (0 : ℝ)))
    (hpos : ∀ t, 0 ≤ t → 0 < H t) :
    ∃ t : ℝ, 0 < t ∧ t * H t = 1 ∧ ∀ s, 0 ≤ s → s * H s = 1 → s = t := by
  have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := (le_rfl : (0 : ℝ) ≤ 0)
  have hH0 : 0 < H 0 := hpos 0 h0mem
  let x : ℝ := 2 / H 0
  have h2 : (0 : ℝ) < 2 := by linarith
  have hx : 0 < x := div_pos h2 hH0
  have hxmem : x ∈ Ici (0 : ℝ) := le_of_lt hx
  have hHx : H 0 ≤ H x := hmono h0mem hxmem (le_of_lt hx)
  have hxH0 : x * H 0 = 2 := by
    simpa [x] using div_mul_cancel₀ (2 : ℝ) (ne_of_gt hH0)
  have hxHx : 2 ≤ x * H x := by
    have hmul : x * H 0 ≤ x * H x := mul_le_mul_of_nonneg_left hHx (le_of_lt hx)
    linarith [hxH0, hmul]
  have hsub : Icc (0 : ℝ) x ⊆ Ici (0 : ℝ) := fun _ hy => hy.1
  have hf_cont : ContinuousOn (fun t => t * H t) (Icc (0 : ℝ) x) :=
    ((continuous_id.continuousOn.mul hcont).mono hsub)
  have hone : (1 : ℝ) ∈ Icc ((0 : ℝ) * H 0) (x * H x) := by
    refine ⟨by simp, ?_⟩
    linarith [hxHx]
  obtain ⟨t, ht, ht_eq⟩ :=
    (mem_image _ _ _).1 (intermediate_value_Icc (le_of_lt hx) hf_cont hone)
  have ht0 : 0 ≤ t := ht.1
  have htpos : 0 < t := by
    refine lt_of_le_of_ne ht0 ?_
    intro hz
    have : (0 : ℝ) * H 0 = 1 := by simpa [hz] using ht_eq
    simp at this
  have hstrict := triangular_prod_strictMonoOn hmono hpos
  refine ⟨t, htpos, ht_eq, ?_⟩
  intro s hs hs_eq
  exact (hstrict.eq_iff_eq hs ht0).1 (hs_eq.trans ht_eq.symm)

theorem no_downcross
    (f : ℝ → ℝ)
    (hdiff : Differentiable ℝ f)
    (A : ℝ)
    (hpos : ∀ x, x ≤ A → 0 < f x)
    (hderiv : ∀ x, f x = 0 → 0 < deriv f x) :
    ∀ x, 0 < f x := by
  intro x
  by_contra hx
  have hxle : f x ≤ 0 := le_of_not_gt hx
  have hAx : A < x := by
    by_contra h
    linarith [hpos x (le_of_not_gt h)]
  let S : Set ℝ := {t | A ≤ t ∧ t ≤ x ∧ f t ≤ 0}
  have hxS : x ∈ S := ⟨le_of_lt hAx, le_rfl, hxle⟩
  have hne : S.Nonempty := ⟨x, hxS⟩
  have hbb : BddBelow S := ⟨A, fun _t ht => ht.1⟩
  have hclosed : IsClosed S := by
    have hseq : S = Icc A x ∩ f ⁻¹' Iic (0 : ℝ) := by
      ext t
      simp only [S, mem_setOf_eq, mem_inter_iff, mem_Icc, mem_preimage, mem_Iic]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    rw [hseq]
    exact isClosed_Icc.inter (IsClosed.preimage hdiff.continuous isClosed_Iic)
  have hleast : IsLeast S (sInf S) := hclosed.isLeast_csInf hne hbb
  let z : ℝ := sInf S
  have hzle : f z ≤ 0 := hleast.1.2.2
  have hfz : f z = 0 := by
    apply le_antisymm hzle
    by_contra hge
    have hfneg : f z < 0 := lt_of_not_ge hge
    have hev : ∀ᶠ y in 𝓝 z, f y < 0 :=
      (hdiff.continuous.continuousAt (x := z)).tendsto.eventually (eventually_lt_nhds hfneg)
    obtain ⟨y, hyz, hyf⟩ := hev.exists_lt
    by_cases hyA : y ≤ A
    · linarith [hpos y hyA]
    · have hyA' : A ≤ y := le_of_lt (lt_of_not_ge hyA)
      have hyx : y ≤ x := le_trans (le_of_lt hyz) (csInf_le hbb hxS)
      have hyS : y ∈ S := ⟨hyA', hyx, le_of_lt hyf⟩
      linarith [hleast.2 hyS]
  have hdz : 0 < deriv f z := hderiv z hfz
  have hleft : Tendsto (slope f z) (𝓝[<] z) (𝓝 (deriv f z)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hdiff.differentiableAt.hasDerivAt).1
  have hevSlope : ∀ᶠ y in 𝓝[<] z, 0 < slope f z y :=
    hleft.eventually (eventually_gt_nhds hdz)
  have hevLt : ∀ᶠ y in 𝓝[<] z, y < z := by
    simpa [mem_Iio] using
      eventually_of_mem (self_mem_nhdsWithin : Iio z ∈ 𝓝[Iio z] z) (fun _ hy => hy)
  haveI : (𝓝[<] z).NeBot := nhdsLT_neBot z
  obtain ⟨y, hy⟩ := (hevLt.and hevSlope).exists
  have hylt : y < z := hy.1
  have hdiv : 0 < f y / (y - z) := by
    have hspos : 0 < slope f z y := hy.2
    rw [slope_def_field, hfz, sub_zero] at hspos
    exact hspos
  have hfy : f y < 0 := by
    rcases div_pos_iff.mp hdiv with hposden | hnegden
    · linarith [hylt]
    · exact hnegden.1
  by_cases hyA : y ≤ A
  · linarith [hpos y hyA]
  · have hyA' : A ≤ y := le_of_lt (lt_of_not_ge hyA)
    have hyx : y ≤ x := le_trans (le_of_lt hylt) (csInf_le hbb hxS)
    have hyS : y ∈ S := ⟨hyA', hyx, le_of_lt hfy⟩
    linarith [hleast.2 hyS]

#print axioms balance_linear_lower
#print axioms growth_from_balance
#print axioms triangular_prod_strictMonoOn
#print axioms triangular_switch
#print axioms no_downcross
#check balance_linear_lower
#check growth_from_balance
#check triangular_prod_strictMonoOn
#check triangular_switch
#check no_downcross

/-- From `2a + (m - 1)b = m`, with `m ≥ 4`, `a > 0` and `1/2 < b < 1`. -/
theorem endpoint_from_balance
    (m a b : ℝ)
    (hm : 4 ≤ m) (ha : 0 < a) (hb1 : (1 : ℝ) / 2 < b) (hb : b < 1)
    (hbal : 2 * a + (m - 1) * b = m) :
    a < m / 2 ∧ a / b < m ∧ a + (m - 2) * b < m - 1 := by
  have hm1 : 0 < m - 1 := by linarith
  have hm3 : 0 < m - 3 := by linarith
  have hbpos : 0 < b := by linarith
  have h2pos : (0 : ℝ) < 2 := by linarith
  have h3pos : 0 < 3 * m - 1 := by linarith
  have ha_half : a < m / 2 := by
    have hmul : 0 < (m - 1) * b := mul_pos hm1 hbpos
    have h2a : 2 * a < m := by linarith [hbal, hmul, ha]
    have h2a' : a * 2 < m := by
      calc
        a * 2 = 2 * a := by ring
        _ < m := h2a
    exact (lt_div_iff₀ h2pos).mpr h2a'
  have hab : a / b < m := by
    have h2m : m * 2 < 3 * m - 1 := by linarith
    have hdiv : m < (3 * m - 1) / 2 := (lt_div_iff₀ h2pos).mpr h2m
    have heq : (3 * m - 1) / 2 = (3 * m - 1) * ((1 : ℝ) / 2) :=
      div_eq_mul_one_div (3 * m - 1) 2
    have hlow : m < (3 * m - 1) * ((1 : ℝ) / 2) := by
      rw [← heq]
      exact hdiv
    have hscale : (3 * m - 1) * ((1 : ℝ) / 2) < (3 * m - 1) * b :=
      mul_lt_mul_of_pos_left hb1 h3pos
    have hmb : m < (3 * m - 1) * b := lt_trans hlow hscale
    have hid : (m - 1) * b + 2 * (m * b) = (3 * m - 1) * b := by ring
    have hsum : m < (m - 1) * b + 2 * (m * b) := by linarith [hid, hmb]
    have h2a : 2 * a < 2 * (m * b) := by linarith [hbal, hsum]
    have ha_lt_mb : a < m * b := lt_of_mul_lt_mul_left h2a (le_of_lt h2pos)
    exact (div_lt_iff₀ hbpos).mpr ha_lt_mb
  have hweight : a + (m - 2) * b < m - 1 := by
    have hbb : (m - 3) * b < (m - 3) * 1 := mul_lt_mul_of_pos_left hb hm3
    have hbb' : (m - 3) * b < m - 3 := by simpa using hbb
    have hgap : 0 < (m - 2) - (m - 3) * b := by linarith
    have hdiff : 2 * ((m - 1) - (a + (m - 2) * b)) - ((m - 2) - (m - 3) * b) =
        m - (2 * a + (m - 1) * b) := by ring
    rw [hbal] at hdiff
    have hid : 2 * ((m - 1) - (a + (m - 2) * b)) = (m - 2) - (m - 3) * b := by
      linarith
    have hpos2 : 0 < 2 * ((m - 1) - (a + (m - 2) * b)) := by linarith [hid, hgap]
    have hpos : 0 < (m - 1) - (a + (m - 2) * b) :=
      (mul_pos_iff_of_pos_left h2pos).mp hpos2
    linarith
  exact ⟨ha_half, hab, hweight⟩

/-- `m - 2 > 0`, so monotonicity of `b` is enough; strict increase comes from `a`. -/
theorem weighted_sum_strictMonoOn
    (m : ℝ) (a b : ℝ → ℝ)
    (hm : 4 ≤ m)
    (ha : StrictMonoOn a (Ici (0 : ℝ)))
    (hb : MonotoneOn b (Ici (0 : ℝ))) :
    StrictMonoOn (fun t => a t + (m - 2) * b t) (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hm2 : 0 < m - 2 := by linarith
  have has : a s < a t := ha hs ht hst
  have hbs : b s ≤ b t := hb hs ht hst.le
  have hmul : (m - 2) * b s ≤ (m - 2) * b t :=
    mul_le_mul_of_nonneg_left hbs (le_of_lt hm2)
  linarith

/-- T3's ordered positive roots. Growth uses `growth_from_balance` at `H0 = H 0`.
Endpoints use `endpoint_from_balance` at `t = 0`. The weighted sum uses
`weighted_sum_strictMonoOn`. The conclusion is `proof_T3`. -/
theorem crossing_from_balance
    (m : ℝ) (a b H : ℝ → ℝ)
    (hm : 4 ≤ m)
    (ha_cont : ContinuousOn a (Ici (0 : ℝ)))
    (hb_cont : ContinuousOn b (Ici (0 : ℝ)))
    (ha_mono : StrictMonoOn a (Ici (0 : ℝ)))
    (hr_mono : StrictMonoOn (fun t => a t / b t) (Ici (0 : ℝ)))
    (hb_mono : MonotoneOn b (Ici (0 : ℝ)))
    (hbnd : ∀ t ∈ Ici (0 : ℝ), 0 < a t ∧ (1 : ℝ) / 2 < b t ∧ b t < 1)
    (hH_mono : MonotoneOn H (Ici (0 : ℝ)))
    (hH0 : 0 < H 0)
    (hbal : ∀ t, 0 ≤ t → 2 * a t + (m - 1) * b t = m + t * H t) :
    ∃ t1 t0 t01 : ℝ,
      0 < t1 ∧ t1 < t0 ∧ t0 < t01 ∧
      a t1 + (m - 2) * b t1 = m - 1 ∧
      a t0 = m / 2 ∧
      a t01 = m * b t01 ∧
      (∀ t ∈ Ici (0 : ℝ), a t + (m - 2) * b t = m - 1 → t = t1) ∧
      (∀ t ∈ Ici (0 : ℝ), a t = m / 2 → t = t0) ∧
      (∀ t ∈ Ici (0 : ℝ), a t = m * b t → t = t01) := by
  have hm1 : 1 < m := by linarith
  have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := (le_rfl : (0 : ℝ) ≤ 0)
  have hH_lower : ∀ t, 0 ≤ t → H 0 ≤ H t := by
    intro t ht
    exact hH_mono h0mem ht ht
  have hb_lt : ∀ t, 0 ≤ t → b t < 1 := by
    intro t ht
    exact (hbnd t ht).2.2
  have ha_top : Tendsto a atTop atTop :=
    growth_from_balance m (H 0) a b H hm1 hH0 hb_lt hH_lower hbal
  have hbal0 : 2 * a 0 + (m - 1) * b 0 = m := by
    have h := hbal 0 (le_rfl : (0 : ℝ) ≤ 0)
    rw [zero_mul, add_zero] at h
    exact h
  have hbnd0 := hbnd 0 h0mem
  have hep :=
    endpoint_from_balance m (a 0) (b 0) hm hbnd0.1 hbnd0.2.1 hbnd0.2.2 hbal0
  have hg_mono : StrictMonoOn (fun t => a t + (m - 2) * b t) (Ici (0 : ℝ)) :=
    weighted_sum_strictMonoOn m a b hm ha_mono hb_mono
  have hT : T3 := proof_T3
  unfold T3 at hT
  exact hT m a b hm ha_cont hb_cont ha_mono hr_mono hg_mono hbnd ha_top
    hep.1 hep.2.1 hep.2.2

example :
    ∀ m a b : ℝ, 4 ≤ m → 0 < a → (1 : ℝ) / 2 < b → b < 1 →
      2 * a + (m - 1) * b = m →
      a < m / 2 ∧ a / b < m ∧ a + (m - 2) * b < m - 1 :=
  endpoint_from_balance

example :
    ∀ (m : ℝ) (a b : ℝ → ℝ), 4 ≤ m →
      StrictMonoOn a (Ici (0 : ℝ)) →
      MonotoneOn b (Ici (0 : ℝ)) →
      StrictMonoOn (fun t => a t + (m - 2) * b t) (Ici (0 : ℝ)) :=
  weighted_sum_strictMonoOn

example :
    ∀ (m : ℝ) (a b H : ℝ → ℝ),
      4 ≤ m →
      ContinuousOn a (Ici (0 : ℝ)) →
      ContinuousOn b (Ici (0 : ℝ)) →
      StrictMonoOn a (Ici (0 : ℝ)) →
      StrictMonoOn (fun t => a t / b t) (Ici (0 : ℝ)) →
      MonotoneOn b (Ici (0 : ℝ)) →
      (∀ t ∈ Ici (0 : ℝ), 0 < a t ∧ (1 : ℝ) / 2 < b t ∧ b t < 1) →
      MonotoneOn H (Ici (0 : ℝ)) →
      0 < H 0 →
      (∀ t, 0 ≤ t → 2 * a t + (m - 1) * b t = m + t * H t) →
      ∃ t1 t0 t01 : ℝ,
        0 < t1 ∧ t1 < t0 ∧ t0 < t01 ∧
        a t1 + (m - 2) * b t1 = m - 1 ∧
        a t0 = m / 2 ∧
        a t01 = m * b t01 ∧
        (∀ t ∈ Ici (0 : ℝ), a t + (m - 2) * b t = m - 1 → t = t1) ∧
        (∀ t ∈ Ici (0 : ℝ), a t = m / 2 → t = t0) ∧
        (∀ t ∈ Ici (0 : ℝ), a t = m * b t → t = t01) :=
  crossing_from_balance

#print axioms endpoint_from_balance
#print axioms weighted_sum_strictMonoOn
#print axioms crossing_from_balance
#check endpoint_from_balance
#check weighted_sum_strictMonoOn
#check crossing_from_balance

end WeakSimplexPilot
