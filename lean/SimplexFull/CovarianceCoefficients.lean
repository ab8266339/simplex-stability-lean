import SimplexFull.GaussianMoments
import SimplexFull.GaussianCrossings
noncomputable section
open MeasureTheory
namespace SimplexFull.Covariance

def gaussianScale (m : ℕ) (mu : ℝ) : ℝ := mu * Real.exp (-mu^2/2) / (m : ℝ)
def coefficientWeight (m : ℕ) (mu c : ℝ) : ℝ := gaussianScale m mu * tiltWeight m mu c
def gaussianC (m : ℕ) (mu : ℝ) : ℝ := gaussianScale m mu * normalizer m mu
def gaussianA (m : ℕ) (mu : ℝ) : ℝ := gaussianC m mu * a m mu
def gaussianB (m : ℕ) (mu : ℝ) : ℝ := gaussianC m mu * b m mu

theorem gaussianC_pos {m : ℕ} (hm : 0 < m) {mu : ℝ} (hmu : 0 < mu) :
    0 < gaussianC m mu := by
  exact mul_pos (div_pos (mul_pos hmu (Real.exp_pos _)) (by exact_mod_cast hm)) (normalizer_pos m mu)

theorem integral_coefficientWeight_mul (m : ℕ) (mu : ℝ) (f : ℝ → ℝ) :
    (∫ c, coefficientWeight m mu c * f c) = gaussianC m mu * tiltedMoment m mu f := by
  have hz := ne_of_gt (normalizer_pos m mu)
  unfold coefficientWeight gaussianC tiltedMoment
  have heq : (fun c => gaussianScale m mu * tiltWeight m mu c * f c) =
      fun c => gaussianScale m mu * (f c * tiltWeight m mu c) := by funext c; ring
  rw [heq, integral_const_mul]
  field_simp

theorem integral_coefficientWeight (m : ℕ) (mu : ℝ) :
    (∫ c, coefficientWeight m mu c) = gaussianC m mu := by
  exact integral_const_mul _ _

theorem integral_coefficientWeight_hsq (m : ℕ) (mu : ℝ) :
    (∫ c, coefficientWeight m mu c * h c^2) = gaussianA m mu :=
  integral_coefficientWeight_mul m mu _

theorem integral_coefficientWeight_sigma (m : ℕ) (mu : ℝ) :
    (∫ c, coefficientWeight m mu c * sigma c) = gaussianB m mu :=
  integral_coefficientWeight_mul m mu _

theorem integral_coefficientWeight_qh (m : ℕ) (mu : ℝ) :
    (∫ c, coefficientWeight m mu c * (q c * h c)) = gaussianC m mu - gaussianB m mu := by
  have hi : Integrable (coefficientWeight m mu) := (integrable_tiltWeight m mu).const_mul (gaussianScale m mu)
  have hj := (gm_integrable_sigma m mu).const_mul (gaussianScale m mu)
  have heq : (fun c => coefficientWeight m mu c * (q c * h c)) =
      fun c => coefficientWeight m mu c - gaussianScale m mu * (sigma c * tiltWeight m mu c) := by
    funext c
    dsimp [coefficientWeight, sigma]
    ring
  rw [heq, integral_sub hi hj, integral_coefficientWeight]
  have heq2 : (fun c => gaussianScale m mu * (sigma c * tiltWeight m mu c)) =
      fun c => coefficientWeight m mu c * sigma c := by funext c; unfold coefficientWeight; ring
  rw [heq2, integral_coefficientWeight_sigma]
#print axioms integral_coefficientWeight_qh

theorem gaussian_gap0_identity (m : ℕ) (hm : m ≠ 0) (mu : ℝ) :
    ((m:ℝ)-1)/(m:ℝ)*gaussianA m mu - ((m:ℝ)-1)/2*gaussianC m mu =
      gaussianC m mu * (((m:ℝ)-1)/(m:ℝ)) * (a m mu-(m:ℝ)/2) := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold gaussianA
  field_simp <;> ring

theorem gaussian_gap1_identity (m : ℕ) (mu : ℝ) :
    (gaussianA m mu+((m:ℝ)-2)*gaussianB m mu)/2 - ((m:ℝ)-1)/2*gaussianC m mu =
      gaussianC m mu / 2 * (a m mu+((m:ℝ)-2)*b m mu-((m:ℝ)-1)) := by
  unfold gaussianA gaussianB
  ring

theorem gaussian_gap0_pos {m : ℕ} (hm : 3 ≤ m) {mu : ℝ} (hmu : 0 < mu)
    (hgap : (m:ℝ)/2 < a m mu) :
    0 < ((m:ℝ)-1)/(m:ℝ)*gaussianA m mu - ((m:ℝ)-1)/2*gaussianC m mu := by
  have hm0 : 0 < m := by omega
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  rw [gaussian_gap0_identity m (Nat.ne_of_gt hm0) mu]
  exact mul_pos (mul_pos (gaussianC_pos hm0 hmu) (div_pos (by linarith) (by linarith))) (sub_pos.mpr hgap)

theorem gaussian_gap1_pos {m : ℕ} (hm : 0 < m) {mu : ℝ} (hmu : 0 < mu)
    (hgap : (m:ℝ)-1 < a m mu+((m:ℝ)-2)*b m mu) :
    0 < (gaussianA m mu+((m:ℝ)-2)*gaussianB m mu)/2 - ((m:ℝ)-1)/2*gaussianC m mu := by
  rw [gaussian_gap1_identity]
  exact mul_pos (div_pos (gaussianC_pos hm hmu) (by norm_num)) (sub_pos.mpr hgap)
#print axioms gaussian_gap0_pos
#print axioms gaussian_gap1_pos



theorem gaussian_gap1_of_gap0 {m : ℕ} (hm : 4 ≤ m) {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : (m:ℝ)/2 < a m mu) : (m:ℝ)-1 < a m mu+((m:ℝ)-2)*b m mu := by
  have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := gaussian_b_gt_half m hm mu hmu
  nlinarith [mul_pos (show (0:ℝ) < (m:ℝ)-2 by linarith) (show 0 < b m mu-1/2 by linarith)]

theorem gaussian_normal_region_threshold (m : ℕ) (hm : 4 ≤ m) :
    ∃ t : ℝ, 0 < t ∧ ∀ mu : ℝ, 0 ≤ mu →
      (((m:ℝ)/2 < a m mu ∧ (m:ℝ)-1 < a m mu+((m:ℝ)-2)*b m mu) ↔ t < mu) := by
  obtain ⟨t1,t0,t01,ht1,ht10,ht001,he1,he0,he01,hu1,hu0,hu01⟩ := gaussian_ordered_crossings m hm
  refine ⟨t0,lt_trans ht1 ht10,fun mu hmu => ?_⟩
  constructor
  · rintro ⟨hgap,_⟩
    by_contra hn
    have hl := (strictMono_a m).monotone (le_of_not_gt hn)
    linarith
  · intro ht
    have hg : (m:ℝ)/2 < a m mu := by
      rw [← he0]
      exact strictMono_a m ht
    exact ⟨hg,gaussian_gap1_of_gap0 hm hmu hg⟩

theorem gaussian_triangle_normal_region_threshold :
    ∃ t : ℝ, 0 < t ∧ ∀ mu : ℝ, 0 ≤ mu →
      (2 < a 3 mu+b 3 mu ↔ t < mu) := by
  obtain ⟨t,ht,he,hu,hl,hr⟩ := gaussian_triangular_unique_crossing
  refine ⟨t,ht,fun mu hmu => ?_⟩
  constructor
  · intro hg
    by_contra hn
    have hle := le_of_not_gt hn
    have ha := (strictMono_a 3).monotone hle
    have hb := (strictMono_b 3).monotone hle
    linarith
  · intro hg
    have hh := hr mu hg
    linarith
#print axioms gaussian_normal_region_threshold
#print axioms gaussian_triangle_normal_region_threshold


theorem gaussian_raw_gap0_pos {m : ℕ} (hm : 0 < m) {mu : ℝ} (hmu : 0 < mu)
    (hgap : (m:ℝ)/2 < a m mu) : 0 < gaussianA m mu-(m:ℝ)*gaussianC m mu/2 := by
  have heq : gaussianA m mu-(m:ℝ)*gaussianC m mu/2 = gaussianC m mu*(a m mu-(m:ℝ)/2) := by
    unfold gaussianA
    ring
  rw [heq]
  exact mul_pos (gaussianC_pos hm hmu) (sub_pos.mpr hgap)

theorem gaussian_twoB_subC_pos {m : ℕ} (hm : 4 ≤ m) {mu : ℝ} (hmu : 0 < mu) :
    0 < 2*gaussianB m mu-gaussianC m mu := by
  have heq : 2*gaussianB m mu-gaussianC m mu = gaussianC m mu*(2*b m mu-1) := by
    unfold gaussianB
    ring
  rw [heq]
  exact mul_pos (gaussianC_pos (by omega) hmu) (by linarith [gaussian_b_gt_half m hm mu hmu.le])

theorem gaussian_triangle_gap_pos {mu : ℝ} (hmu : 0 < mu) (hgap : 2 < a 3 mu+b 3 mu) :
    0 < gaussianA 3 mu+gaussianB 3 mu-2*gaussianC 3 mu := by
  have heq : gaussianA 3 mu+gaussianB 3 mu-2*gaussianC 3 mu =
      gaussianC 3 mu*(a 3 mu+b 3 mu-2) := by unfold gaussianA gaussianB; ring
  rw [heq]
  exact mul_pos (gaussianC_pos (by decide) hmu) (sub_pos.mpr hgap)
#print axioms gaussian_raw_gap0_pos
#print axioms gaussian_twoB_subC_pos
#print axioms gaussian_triangle_gap_pos
end SimplexFull.Covariance
