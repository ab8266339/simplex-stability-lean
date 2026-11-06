import SimplexFull.ShellObjective
import SimplexFull.CovarianceGeometry
import SimplexFull.GaussianDensityIntegrals
noncomputable section
open MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
variable {m d : ℕ} [NeZero m]
def muFromSNR (m : ℕ) (lam : ℝ) : ℝ := lam / Real.sqrt (alpha m)
def configPc (X : Config m d) (lam : ℝ) : ℝ := SimplexFull.decodingSuccess (gram X) lam
lemma alpha_pos_of_gt_one {m : ℕ} (hm : 1 < m) : 0 < alpha m := by
  unfold alpha
  have hmR : (1:ℝ) < m := by exact_mod_cast hm
  exact div_pos (sub_pos.mpr hmR) (by linarith)
lemma muFromSNR_mul_sqrt (hm : 1 < m) (lam : ℝ) :
    muFromSNR m lam * Real.sqrt (alpha m) = lam := by
  exact div_mul_cancel₀ lam (Real.sqrt_pos.mpr (alpha_pos_of_gt_one hm)).ne'
lemma muFromSNR_pos (hm : 1 < m) {lam : ℝ} (hlam : 0 < lam) :
    0 < muFromSNR m lam := div_pos hlam (Real.sqrt_pos.mpr (alpha_pos_of_gt_one hm))
lemma decodingSuccess_eq_rhoExpectation (mu : ℝ) (R : ShapeMatrix m) (hR : R.PosDef) :
    SimplexFull.decodingSuccess R mu = Real.exp (-mu^2/2)/(m:ℝ)*Covariance.rhoExpectation mu R := by
  rw [Covariance.decodingSuccess_eq_rho_integral R hR mu]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _
lemma extendedLoss_eq_decodingDeficit (mu : ℝ) (R : ShapeMatrix m) (hR : R.PosDef) :
    extendedLoss mu R = SimplexFull.decodingSuccess (1:ShapeMatrix m) mu -
      SimplexFull.decodingSuccess R mu := by
  rw [extendedLoss, mul_sub, decodingSuccess_eq_rhoExpectation mu 1 Matrix.PosDef.one,
    decodingSuccess_eq_rhoExpectation mu R hR]
#print axioms extendedLoss_eq_decodingDeficit
theorem extendedLoss_channelCovariance (hm : 1 < m) (V X : Config m d)
    (hV : gram V = simplexGram m) (hX : (channelCovariance X).PosDef) (lam : ℝ) :
    extendedLoss (muFromSNR m lam) (channelCovariance X) = configPc V lam - configPc X lam := by
  have hsV := SimplexFull.decodingSuccess_independenceCov (gram V) (gram_posSemidef V) (muFromSNR m lam)
  have hsX := SimplexFull.decodingSuccess_independenceCov (gram X) (gram_posSemidef X) (muFromSNR m lam)
  change SimplexFull.decodingSuccess (channelCovariance V) (muFromSNR m lam) = _ at hsV
  change SimplexFull.decodingSuccess (channelCovariance X) (muFromSNR m lam) = _ at hsX
  rw [channelCovariance_of_simplex V hm hV, muFromSNR_mul_sqrt hm lam] at hsV
  rw [muFromSNR_mul_sqrt hm lam] at hsX
  rw [extendedLoss_eq_decodingDeficit _ _ hX, hsV, hsX]
  rfl
theorem exists_local_extendedLoss_configPc (hm : 1 < m) (V : Config m d)
    (hV : gram V = simplexGram m) (lam : ℝ) :
    ∃ delta > 0, ∀ X : Config m d, procrustesSq X V < delta →
      extendedLoss (muFromSNR m lam) (channelCovariance X) = configPc V lam - configPc X lam := by
  obtain ⟨delta,hdelta,hpd⟩ := exists_local_channelCovariance_posDef V hm hV
  exact ⟨delta,hdelta,fun X hX => extendedLoss_channelCovariance hm V X hV (hpd X hX) lam⟩
#print axioms extendedLoss_channelCovariance
#print axioms exists_local_extendedLoss_configPc
end SimplexFull.Geometry