import SimplexFull.GlobalScalarTaylor
import SimplexFull.GeometryBase
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
noncomputable section
open Set MeasureTheory
namespace SimplexFull.GlobalCentroid
open GlobalScalar
abbrev alpha := Geometry.alpha

theorem alpha_pos {m : Nat} (hm : 2 ≤ m) : 0 < alpha m := by
  have hmR : (2:Real) ≤ m := by exact_mod_cast hm
  dsimp [alpha, Geometry.alpha]
  exact div_pos (by linarith) (by linarith)

theorem alpha_mul_m {m : Nat} (hm : 0 < m) : alpha m*(m:Real) = (m:Real)-1 := by
  dsimp [alpha, Geometry.alpha]
  exact div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt hm)

def tau (m : Nat) : Real :=
  min (h 0/(2*alpha m*(m:Real))) (q 1/(1+M0*alpha m*(m:Real)))

def eta (m : Nat) : Real := (2:Real)⁻¹^m*(alpha m*q 1*tau m/2)

theorem tau_pos {m : Nat} (hm : 2 ≤ m) : 0 < tau m := by
  have ha := alpha_pos hm
  have hmR : (0:Real) < m := by exact_mod_cast (show 0<m by omega)
  have hM := M0_pos
  exact lt_min (div_pos (h_pos 0) (by positivity)) (div_pos (q_pos 1) (by positivity))

theorem eta_pos {m : Nat} (hm : 2 ≤ m) : 0 < eta m := by
  unfold eta
  exact mul_pos (pow_pos (by norm_num) _) (div_pos
    (mul_pos (mul_pos (alpha_pos hm) (q_pos 1)) (tau_pos hm)) (by norm_num))

theorem tau_shift_le {m : Nat} (hm : 2 ≤ m) : tau m*((m:Real)-1) ≤ h 0/2 := by
  have ha := alpha_pos hm
  have hmR : (0:Real) < m := by exact_mod_cast (show 0<m by omega)
  have hb : tau m ≤ h 0/(2*alpha m*(m:Real)) := min_le_left _ _
  have hh := (le_div_iff₀ (by positivity : 0<2*alpha m*(m:Real))).mp hb
  rw [← alpha_mul_m (show 0<m by omega)]
  nlinarith

theorem tau_curvature_le {m : Nat} (hm : 2 ≤ m) :
    tau m*(1+M0*((m:Real)-1)) ≤ q 1 := by
  have ha := alpha_pos hm
  have hmR : (0:Real) < m := by exact_mod_cast (show 0<m by omega)
  have hM := M0_pos
  have hb : tau m ≤ q 1/(1+M0*alpha m*(m:Real)) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0<1+M0*alpha m*(m:Real))).mp hb
  rw [← alpha_mul_m (show 0<m by omega)]
  nlinarith

#print axioms tau_pos
#print axioms eta_pos
end SimplexFull.GlobalCentroid
