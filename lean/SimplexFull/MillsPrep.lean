import SimplexFull.GaussianBase

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SimplexFull

theorem Phi_nonneg_basic (c : ℝ) : 0 ≤ Phi c := integral_nonneg phi_nonneg

theorem Phi_le_one_basic (c : ℝ) : Phi c ≤ 1 := by
  calc
    Phi c ≤ ∫ x, phi x := setIntegral_le_integral integrable_phi (ae_of_all _ phi_nonneg)
    _ = 1 := integral_phi_eq_one

theorem tendsto_Phi_atBot_basic : Tendsto Phi atBot (𝓝 0) :=
  MeasureTheory.tendsto_integral_Iic_zero (f := phi) tendsto_id

theorem phi_neg_basic (x : ℝ) : phi (-x) = phi x := by
  simp [phi, ProbabilityTheory.gaussianPDFReal]

end SimplexFull