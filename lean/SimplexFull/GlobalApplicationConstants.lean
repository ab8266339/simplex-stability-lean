import SimplexFull.GlobalUnitMeanBounds
import SimplexFull.GlobalCentroidDecoderGram
import SimplexFull.GlobalComparisonConstants
import Mathlib.Tactic

noncomputable section
namespace SimplexFull.GlobalApplication

def kappa (m : ℕ) : ℝ := GlobalComparison.paperKappa m 0 1
def meanGramConstant (m : ℕ) : ℝ :=
  kappa m * (Geometry.alpha m)^2 / Real.sqrt (Geometry.alpha m)
def gramDecoderConstant (m : ℕ) (lam : ℝ) : ℝ :=
  GlobalTail.expWindowWeight m (lam / Real.sqrt (Geometry.alpha m)) *
    kappa m * (Geometry.alpha m)^2
def procrustesDecoderConstant (m : ℕ) (lam : ℝ) : ℝ :=
  (Geometry.alpha m / gramDecoderConstant m lam +
    1 / ((m:ℝ)*GlobalTail.centroidDecoderConstant m lam))⁻¹

theorem kappa_pos {m : ℕ} (hm : 2 ≤ m) : 0 < kappa m :=
  GlobalComparison.paperKappa_pos hm 0 1

theorem meanGramConstant_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < meanGramConstant m :=
  div_pos (mul_pos (kappa_pos hm) (sq_pos_of_pos (GlobalCentroid.alpha_pos hm)))
    (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm))

theorem meanGramConstant_eq_sqrt {m : ℕ} (hm : 2 ≤ m) :
    meanGramConstant m = kappa m * Geometry.alpha m * Real.sqrt (Geometry.alpha m) := by
  have ha := GlobalCentroid.alpha_pos hm
  have hs := Real.sqrt_pos.mpr ha
  unfold meanGramConstant
  apply (div_eq_iff hs.ne').mpr
  calc
    _ = kappa m * Geometry.alpha m *
        (Real.sqrt (Geometry.alpha m) * Real.sqrt (Geometry.alpha m)) := by
      rw [Real.mul_self_sqrt ha.le]
      ring
    _ = _ := by ring

theorem gramDecoderConstant_pos {m : ℕ} (hm : 2 ≤ m)
    {lam : ℝ} (hlam : 0 < lam) : 0 < gramDecoderConstant m lam := by
  apply mul_pos
  · exact mul_pos (GlobalTail.expWindowWeight_pos (by omega)
      (div_pos hlam (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm)))) (kappa_pos hm)
  · exact sq_pos_of_pos (GlobalCentroid.alpha_pos hm)

theorem procrustesDecoderConstant_pos {m : ℕ} (hm : 2 ≤ m)
    {lam : ℝ} (hlam : 0 < lam) : 0 < procrustesDecoderConstant m lam := by
  letI : NeZero m := ⟨by omega⟩
  unfold procrustesDecoderConstant
  apply inv_pos.mpr
  exact add_pos (div_pos (GlobalCentroid.alpha_pos hm) (gramDecoderConstant_pos hm hlam))
    (one_div_pos.mpr (mul_pos (by exact_mod_cast (show 0<m by omega))
      (GlobalTail.centroidDecoderConstant_pos hm hlam)))

#print axioms meanGramConstant_pos
#print axioms procrustesDecoderConstant_pos
end SimplexFull.GlobalApplication
