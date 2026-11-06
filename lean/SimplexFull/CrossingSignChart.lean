import SimplexFull.GaussianCrossings

noncomputable section
open Set
open WeakSimplexPilot (L0 L1 Lp)
namespace SimplexFull

private theorem sc_L0_lt_L1 {m x y : ℝ} (hm : 4 ≤ m) (hxy : x < m*y) :
    L0 m x < L1 m x y := by
  have hm0 : 0 < m := by linarith
  dsimp [L0, L1]
  rw [div_lt_div_iff₀ hm0 (by norm_num : (0 : ℝ) < 2)]
  have hp : 0 < (m-2)*(m*y-x) := mul_pos (by linarith) (by linarith)
  nlinarith

private theorem sc_L1_lt_L0 {m x y : ℝ} (hm : 4 ≤ m) (hxy : m*y < x) :
    L1 m x y < L0 m x := by
  have hm0 : 0 < m := by linarith
  dsimp [L0, L1]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hm0]
  have hp : 0 < (m-2)*(x-m*y) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- The complete normalized curvature sign chart for the actual Gaussian moments.
The three scalar coefficients are L0=(m-1)*a/m, L1=(a+(m-2)*b)/2,
and Lp=(m-1)/2. All roots, uniqueness clauses, open intervals, and endpoints
are returned together; no analytic hypotheses are supplied by the caller. -/
theorem gaussian_ordered_crossings_sign_chart (m : ℕ) (hm : 4 ≤ m) :
    ∃ t1 t0 t01 : ℝ,
      0 < t1 ∧ t1 < t0 ∧ t0 < t01 ∧
      a m t1 + ((m : ℝ)-2)*b m t1 = (m : ℝ)-1 ∧
      a m t0 = (m : ℝ)/2 ∧
      a m t01 = (m : ℝ)*b m t01 ∧
      (∀ t ∈ Ici (0 : ℝ),
        a m t + ((m : ℝ)-2)*b m t = (m : ℝ)-1 → t=t1) ∧
      (∀ t ∈ Ici (0 : ℝ), a m t = (m : ℝ)/2 → t=t0) ∧
      (∀ t ∈ Ici (0 : ℝ), a m t = (m : ℝ)*b m t → t=t01) ∧
      (∀ t : ℝ, 0 < t → t < t1 →
        L0 m (a m t) < L1 m (a m t) (b m t) ∧
        L1 m (a m t) (b m t) < Lp m) ∧
      (∀ t : ℝ, t1 < t → t < t0 →
        L0 m (a m t) < Lp m ∧ Lp m < L1 m (a m t) (b m t)) ∧
      (∀ t : ℝ, t0 < t → t < t01 →
        Lp m < L0 m (a m t) ∧ L0 m (a m t) < L1 m (a m t) (b m t)) ∧
      (∀ t : ℝ, t01 < t →
        Lp m < L1 m (a m t) (b m t) ∧ L1 m (a m t) (b m t) < L0 m (a m t)) ∧
      (L0 m (a m t1) < L1 m (a m t1) (b m t1) ∧
        L1 m (a m t1) (b m t1) = Lp m) ∧
      (L0 m (a m t0) = Lp m ∧ Lp m < L1 m (a m t0) (b m t0)) ∧
      (Lp m < L0 m (a m t01) ∧ L0 m (a m t01) = L1 m (a m t01) (b m t01)) := by
  obtain ⟨t1,t0,t01,ht1,ht10,ht001,he1,he0,he01,hu1,hu0,hu01⟩ :=
    gaussian_ordered_crossings m hm
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hmono0 : StrictMono (fun t => L0 m (a m t)) := by
    intro s t hst
    dsimp [L0]
    exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left (strictMono_a m hst) (by linarith)) hmpos
  have hmono1 : StrictMono (fun t => L1 m (a m t) (b m t)) := by
    intro s t hst
    have ha := strictMono_a m hst
    have hb := mul_lt_mul_of_pos_left (strictMono_b m hst)
      (show (0 : ℝ) < (m : ℝ)-2 by linarith)
    dsimp [L1]
    linarith
  have hlevel1 : L1 m (a m t1) (b m t1) = Lp m := by
    simpa only [L1, Lp, he1]
  have hlevel0 : L0 m (a m t0) = Lp m := by
    dsimp [L0,Lp]
    rw [he0]
    field_simp
    <;> ring
  have hlevel01 : L0 m (a m t01) = L1 m (a m t01) (b m t01) := by
    dsimp [L0,L1]
    rw [he01]
    field_simp
    <;> ring
  have hratio : a m t01 / b m t01 = (m : ℝ) :=
    (div_eq_iff (ne_of_gt (b_pos m t01))).2 he01
  have hbefore : ∀ t : ℝ, t < t01 →
      L0 m (a m t) < L1 m (a m t) (b m t) := by
    intro t htt
    have hr := strictMono_a_div_b m htt
    dsimp only at hr
    rw [hratio] at hr
    exact sc_L0_lt_L1 hmr ((div_lt_iff₀ (b_pos m t)).mp hr)
  have hafter : ∀ t : ℝ, t01 < t →
      L1 m (a m t) (b m t) < L0 m (a m t) := by
    intro t htt
    have hr := strictMono_a_div_b m htt
    dsimp only at hr
    rw [hratio] at hr
    exact sc_L1_lt_L0 hmr ((lt_div_iff₀ (b_pos m t)).mp hr)
  refine ⟨t1,t0,t01,ht1,ht10,ht001,he1,he0,he01,hu1,hu0,hu01,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t _ht htt
    refine ⟨hbefore t (htt.trans (ht10.trans ht001)), ?_⟩
    simpa only [hlevel1] using hmono1 htt
  · intro t htlo hthi
    constructor
    · simpa only [hlevel0] using hmono0 hthi
    · simpa only [hlevel1] using hmono1 htlo
  · intro t htlo hthi
    constructor
    · simpa only [hlevel0] using hmono0 htlo
    · exact hbefore t hthi
  · intro t htt
    constructor
    · simpa only [hlevel1] using hmono1 ((ht10.trans ht001).trans htt)
    · exact hafter t htt
  · exact ⟨hbefore t1 (ht10.trans ht001),hlevel1⟩
  · refine ⟨hlevel0,?_⟩
    simpa only [hlevel1] using hmono1 ht10
  · refine ⟨?_,hlevel01⟩
    simpa only [hlevel0] using hmono0 ht001


/-- Positive common scaling preserves the full chart, with the same unique roots.
The scale may be instantiated pointwise by the positive physical Gaussian coefficient. -/
theorem gaussian_ordered_crossings_sign_chart_scaled (m : ℕ) (hm : 4 ≤ m) :
    ∃ t1 t0 t01 : ℝ,
      0 < t1 ∧ t1 < t0 ∧ t0 < t01 ∧
      a m t1 + ((m : ℝ)-2)*b m t1 = (m : ℝ)-1 ∧
      a m t0 = (m : ℝ)/2 ∧
      a m t01 = (m : ℝ)*b m t01 ∧
      (∀ t ∈ Ici (0 : ℝ),
        a m t + ((m : ℝ)-2)*b m t = (m : ℝ)-1 → t=t1) ∧
      (∀ t ∈ Ici (0 : ℝ), a m t = (m : ℝ)/2 → t=t0) ∧
      (∀ t ∈ Ici (0 : ℝ), a m t = (m : ℝ)*b m t → t=t01) ∧
      ∀ c : ℝ, 0 < c →
      (∀ t : ℝ, 0 < t → t < t1 →
        c*L0 m (a m t) < c*L1 m (a m t) (b m t) ∧
        c*L1 m (a m t) (b m t) < c*Lp m) ∧
      (∀ t : ℝ, t1 < t → t < t0 →
        c*L0 m (a m t) < c*Lp m ∧ c*Lp m < c*L1 m (a m t) (b m t)) ∧
      (∀ t : ℝ, t0 < t → t < t01 →
        c*Lp m < c*L0 m (a m t) ∧ c*L0 m (a m t) < c*L1 m (a m t) (b m t)) ∧
      (∀ t : ℝ, t01 < t →
        c*Lp m < c*L1 m (a m t) (b m t) ∧ c*L1 m (a m t) (b m t) < c*L0 m (a m t)) ∧
      (c*L0 m (a m t1) < c*L1 m (a m t1) (b m t1) ∧
        c*L1 m (a m t1) (b m t1) = c*Lp m) ∧
      (c*L0 m (a m t0) = c*Lp m ∧ c*Lp m < c*L1 m (a m t0) (b m t0)) ∧
      (c*Lp m < c*L0 m (a m t01) ∧ c*L0 m (a m t01) = c*L1 m (a m t01) (b m t01)) := by
  obtain ⟨t1,t0,t01,ht1,ht10,ht001,he1,he0,he01,hu1,hu0,hu01,
    hi1,hi2,hi3,hi4,hend1,hend0,hend01⟩ :=
    gaussian_ordered_crossings_sign_chart m hm
  refine ⟨t1,t0,t01,ht1,ht10,ht001,he1,he0,he01,hu1,hu0,hu01,?_⟩
  intro c hc
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro t ht htt
    exact ⟨mul_lt_mul_of_pos_left (hi1 t ht htt).1 hc,
      mul_lt_mul_of_pos_left (hi1 t ht htt).2 hc⟩
  · intro t ht htt
    exact ⟨mul_lt_mul_of_pos_left (hi2 t ht htt).1 hc,
      mul_lt_mul_of_pos_left (hi2 t ht htt).2 hc⟩
  · intro t ht htt
    exact ⟨mul_lt_mul_of_pos_left (hi3 t ht htt).1 hc,
      mul_lt_mul_of_pos_left (hi3 t ht htt).2 hc⟩
  · intro t ht
    exact ⟨mul_lt_mul_of_pos_left (hi4 t ht).1 hc,
      mul_lt_mul_of_pos_left (hi4 t ht).2 hc⟩
  · exact ⟨mul_lt_mul_of_pos_left hend1.1 hc, congrArg (fun x => c*x) hend1.2⟩
  · exact ⟨congrArg (fun x => c*x) hend0.1, mul_lt_mul_of_pos_left hend0.2 hc⟩
  · exact ⟨mul_lt_mul_of_pos_left hend01.1 hc, congrArg (fun x => c*x) hend01.2⟩

#print axioms gaussian_ordered_crossings_sign_chart
#print axioms gaussian_ordered_crossings_sign_chart_scaled
end SimplexFull
