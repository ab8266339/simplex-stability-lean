import SimplexFull.SignalSmooth
import SimplexFull.TaylorDefinitions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
noncomputable section
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]
/-- The exact deficit is real analytic; its iterated derivatives are genuine derivatives. -/
theorem contDiff_normalDeficit (lam : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (normalDeficit m lam) := by
  have hp : ContDiff ℝ n (simplexSuccess m) :=
    SimplexFull.contDiff_decodingSuccess _ SimplexFull.simplexGram_posSemidef
  have harg : ContDiff ℝ n (fun rho : ℝ => lam*shellKappa m rho) := by
    unfold shellKappa
    fun_prop
  exact contDiff_const.sub (hp.comp harg)
#print axioms contDiff_normalDeficit
/-- Every odd derivative at the origin vanishes, not only the cubic coefficient. -/
theorem normalDeficit_odd_iteratedDeriv_zero (lam : ℝ) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n (normalDeficit m lam) 0=0 := by
  have heq : (fun rho : ℝ => normalDeficit m lam (-rho))=normalDeficit m lam := by
    funext rho
    exact normalDeficit_neg lam rho
  have hh := iteratedDeriv_comp_neg n (normalDeficit m lam) 0
  rw [heq,neg_zero,hn.neg_one_pow,neg_one_smul] at hh
  linarith
 theorem normalDeficit_no_cubic (lam : ℝ) : iteratedDeriv 3 (normalDeficit m lam) 0=0 :=
  normalDeficit_odd_iteratedDeriv_zero lam (by decide)
#print axioms normalDeficit_odd_iteratedDeriv_zero
#print axioms normalDeficit_no_cubic
end SimplexFull.Geometry

