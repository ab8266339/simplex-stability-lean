import SimplexFull.GlobalComparisonActual
noncomputable section
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators
namespace SimplexFull.GlobalComparison

/-- Original Theorem 2: the exact square-root quantitative orthant comparison.
Every covariance is the actual PSD Gaussian covariance, singular cases included. -/
theorem orthant_sqrt_comparison {m : ℕ} (hm : 2 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R)
    (u v c : ℝ) (huc : u ≤ c) (hcv : c ≤ v) :
    (Phi u)^m * (Real.sqrt (1+paperK m u v*covarianceDefect R)-1) ≤
      orthantMass R c-(Phi c)^m := by
  by_cases hne : R=1
  · subst R
    have ho : orthantMass (1 : Matrix (Fin m) (Fin m) ℝ) c = (Phi c)^m := by
      rw [orthantMass, SimplexUniqueness.lowerOrthant_eq_iid_of_eq_one,
        ENNReal.toReal_pow, ← normalCDF_eq_measure_Iic,
        ENNReal.toReal_ofReal (normalCDF_pos c).le]
      rfl
    simp [covarianceDefect,ho]
  · obtain ⟨w⟩ := SimplexUniqueness.exists_adaptiveWitnesses_of_isWeakSimplexCov
      (by omega) R hR c
    have hd := witness_doubling_lower hm hR.1 hne w huc hcv
    have hq1 := witnessQ1_ge_one hR.1 w
    have hq0 := witnessQ0_nonneg w
    have hK := (paperK_pos hm u v).le
    have hD := covarianceDefect_nonneg R
    have harg : 0 ≤ 1+paperK m u v*covarianceDefect R := by positivity
    have hsq := Real.sq_sqrt harg
    have hs0 := Real.sqrt_nonneg (1+paperK m u v*covarianceDefect R)
    have hs : Real.sqrt (1+paperK m u v*covarianceDefect R) ≤ witnessQ0 w := by
      nlinarith
    have hs1 : 1 ≤ Real.sqrt (1+paperK m u v*covarianceDefect R) := by
      nlinarith [mul_nonneg hK hD]
    have hv := witnessValue_exp_lower w
    have hp : (Phi u)^m ≤ (Phi c)^m :=
      pow_le_pow_left₀ (Phi_pos u).le (SimplexUniqueness.Witness.normalCDF_mono huc) m
    have hpc : 0 ≤ (Phi c)^m := pow_nonneg (Phi_pos c).le m
    have hprod := mul_le_mul hs hv hpc hq0
    have hmul := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hs1)
    rw [orthantMass_eq_witness hR.1.1 w]
    nlinarith

/-- Original linear quantitative comparison with the exact paper constant. -/
theorem orthant_linear_comparison {m : ℕ} (hm : 2 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R)
    (u v c : ℝ) (huc : u ≤ c) (hcv : c ≤ v) :
    paperKappa m u v * covarianceDefect R ≤ orthantMass R c-(Phi c)^m :=
  (paperKappa_defect_le_sqrt_gap hm R hR.1 u v).trans
    (orthant_sqrt_comparison hm R hR u v c huc hcv)

/-- Uniform interval formulation, with no witness or analytic hypotheses. -/
theorem quantitative_lowerOrthant {m : ℕ} (hm : 2 ≤ m)
    (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsWeakSimplexCov R)
    (u v : ℝ) (c : ℝ) (hc : c ∈ Icc u v) :
    0 < paperK m u v ∧ 0 < paperKappa m u v ∧
    (Phi u)^m * (Real.sqrt (1+paperK m u v*covarianceDefect R)-1) ≤
      orthantMass R c-(Phi c)^m ∧
    paperKappa m u v * covarianceDefect R ≤ orthantMass R c-(Phi c)^m :=
  ⟨paperK_pos hm u v,paperKappa_pos hm u v,
    orthant_sqrt_comparison hm R hR u v c hc.1 hc.2,
    orthant_linear_comparison hm R hR u v c hc.1 hc.2⟩

#print axioms orthant_sqrt_comparison
#print axioms orthant_linear_comparison
#print axioms quantitative_lowerOrthant
end SimplexFull.GlobalComparison
