import SimplexFull.Benchmark
import SimplexFull.MomentOrder
import SimplexFull.Abstract
import SimplexFull.GaussianMoments
import SimplexFull.Balance

noncomputable section
open Filter Set
namespace SimplexFull

theorem gaussian_triangular_switch :
    ∃ t : ℝ, 0 < t ∧ t * H 3 t = 1 ∧
      ∀ s : ℝ, 0 ≤ s → s * H 3 s = 1 → s = t := by
  exact WeakSimplexPilot.triangular_switch
    (continuous_H 3).continuousOn
    (fun s _hs t _ht hst => (strictMono_H 3).monotone hst)
    (fun t _ht => H_pos 3 t)

theorem gaussian_triangular_coefficient_eq_iff (mu : ℝ) :
    (a 3 mu + b 3 mu) / 2 = 1 ↔ mu * H 3 mu = 1 := by
  have hb := gaussian_balance_identity 3 (by decide) mu
  norm_num at hb
  constructor <;> intro he <;> nlinarith

theorem gaussian_triangular_coefficient_lt_iff (mu : ℝ) :
    (a 3 mu + b 3 mu) / 2 < 1 ↔ mu * H 3 mu < 1 := by
  have hb := gaussian_balance_identity 3 (by decide) mu
  norm_num at hb
  constructor <;> intro he <;> nlinarith

theorem gaussian_triangular_coefficient_gt_iff (mu : ℝ) :
    1 < (a 3 mu + b 3 mu) / 2 ↔ 1 < mu * H 3 mu := by
  have hb := gaussian_balance_identity 3 (by decide) mu
  norm_num at hb
  constructor <;> intro he <;> nlinarith

theorem gaussian_triangular_unique_crossing :
    ∃ t : ℝ, 0 < t ∧ (a 3 t + b 3 t) / 2 = 1 ∧
      (∀ s : ℝ, 0 ≤ s → (a 3 s + b 3 s) / 2 = 1 → s = t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t → (a 3 s + b 3 s) / 2 < 1) ∧
      (∀ s : ℝ, t < s → 1 < (a 3 s + b 3 s) / 2) := by
  obtain ⟨t, ht, he, hu⟩ := gaussian_triangular_switch
  have hmono : StrictMonoOn (fun s => s * H 3 s) (Ici (0 : ℝ)) :=
    WeakSimplexPilot.triangular_prod_strictMonoOn
      (fun s _hs t _ht hst => (strictMono_H 3).monotone hst)
      (fun t _ht => H_pos 3 t)
  refine ⟨t, ht, (gaussian_triangular_coefficient_eq_iff t).mpr he, ?_, ?_, ?_⟩
  · intro s hs hsEq
    exact hu s hs ((gaussian_triangular_coefficient_eq_iff s).mp hsEq)
  · intro s hs hst
    apply (gaussian_triangular_coefficient_lt_iff s).mpr
    rw [← he]
    exact hmono hs ht.le hst
  · intro s hts
    apply (gaussian_triangular_coefficient_gt_iff s).mpr
    rw [← he]
    exact hmono ht.le (lt_trans ht hts).le hts

#print axioms gaussian_triangular_switch
#print axioms gaussian_triangular_unique_crossing

theorem gaussian_b_gt_half (m : ℕ) (hm : 4 ≤ m) (mu : ℝ) (hmu : 0 ≤ mu) :
    (1 : ℝ) / 2 < b m mu := by
  have hmu_mono : b 4 0 ≤ b 4 mu := (strictMono_b 4).monotone hmu
  have hm_mono : b 4 mu ≤ b m mu := b_mono_nat (by decide : 2 ≤ 4) hm mu
  exact lt_of_lt_of_le b4_zero_gt_half (hmu_mono.trans hm_mono)

theorem gaussian_a_tendsto_atTop (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (a m) atTop atTop := by
  have hmr : (1 : ℝ) < (m : ℝ) := by
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  exact WeakSimplexPilot.growth_from_balance (m : ℝ) (H m 0) (a m) (b m) (H m)
    hmr (H_pos m 0)
    (fun t _ht => b_lt_one m t)
    (fun t ht => (strictMono_H m).monotone ht)
    (fun t _ht => gaussian_balance_identity m hm t)

theorem gaussian_ordered_crossings (m : ℕ) (hm : 4 ≤ m) :
    ∃ t1 t0 t01 : ℝ,
      0 < t1 ∧ t1 < t0 ∧ t0 < t01 ∧
      a m t1 + ((m : ℝ) - 2) * b m t1 = (m : ℝ) - 1 ∧
      a m t0 = (m : ℝ) / 2 ∧
      a m t01 = (m : ℝ) * b m t01 ∧
      (∀ t ∈ Ici (0 : ℝ),
        a m t + ((m : ℝ) - 2) * b m t = (m : ℝ) - 1 → t = t1) ∧
      (∀ t ∈ Ici (0 : ℝ), a m t = (m : ℝ) / 2 → t = t0) ∧
      (∀ t ∈ Ici (0 : ℝ), a m t = (m : ℝ) * b m t → t = t01) := by
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 4) hm
  exact WeakSimplexPilot.crossing_from_balance (m : ℝ) (a m) (b m) (H m) hmr
    (continuous_a m).continuousOn
    (continuous_b m).continuousOn
    (fun s _hs t _ht hst => strictMono_a m hst)
    (fun s _hs t _ht hst => strictMono_a_div_b m hst)
    (fun s _hs t _ht hst => (strictMono_b m).monotone hst)
    (fun t ht => ⟨a_pos m t, gaussian_b_gt_half m hm t ht, b_lt_one m t⟩)
    (fun s _hs t _ht hst => (strictMono_H m).monotone hst)
    (H_pos m 0)
    (fun t _ht => gaussian_balance_identity m hm2 t)

theorem gaussian_middle_coefficient_not_min (m : ℕ) (hm : 4 ≤ m)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    min (WeakSimplexPilot.L0 (m : ℝ) (a m mu)) (WeakSimplexPilot.Lp (m : ℝ)) <
      WeakSimplexPilot.L1 (m : ℝ) (a m mu) (b m mu) := by
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact (WeakSimplexPilot.proof_T2 (m : ℝ) (a m mu) (b m mu) hmr
    (a_pos m mu) (gaussian_b_gt_half m hm mu hmu) (b_lt_one m mu)).2.2

#print axioms gaussian_b_gt_half
#print axioms gaussian_a_tendsto_atTop
#print axioms gaussian_ordered_crossings
#print axioms gaussian_middle_coefficient_not_min
end SimplexFull
