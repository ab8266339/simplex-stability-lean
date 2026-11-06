import SimplexFull.GlobalCentroidGrowth
import SimplexFull.GlobalWitnessOrthantBound
import SimplexFull.Benchmark
noncomputable section
open WeakSimplex Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SimplexFull.GlobalCentroid

def orthantCDF {m : Nat} (R : Matrix (Fin m) (Fin m) Real) (c : Real) : Real :=
  (multivariateGaussian (0 : Coord m) R (lowerOrthant c)).toReal

def thresholdDeficit {m : Nat} (R : Matrix (Fin m) (Fin m) Real) (c : Real) : Real :=
  orthantCDF R c-(Phi c)^m

theorem Phi_zero : Phi 0 = 1/2 := by
  have hh := Phi_add_Phi_neg 0
  simp only [neg_zero] at hh
  linarith

theorem Phi_zero_le {c : Real} (hc : 0≤c) : (1:Real)/2 ≤ Phi c := by
  have hmono : StrictMono Phi := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hasDerivAt_Phi x).deriv]
    exact phi_pos x
  rw [← Phi_zero]
  exact hmono.monotone hc

theorem thresholdDeficit_nonneg {m : Nat} (hm : 0<m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R) (c : Real) :
    0 ≤ thresholdDeficit R c := by
  have hh := ENNReal.toReal_mono (measure_ne_top _ _)
    (WeakSimplex.lowerOrthant_ge_iid hm R hR c)
  rw [← normalCDF_eq_measure_Iic, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (show 0 ≤ normalCDF c from (Phi_pos c).le)] at hh
  exact sub_nonneg.mpr hh

theorem centroidExcess_one (m : Nat) :
    centroidExcess (1 : Matrix (Fin m) (Fin m) Real)=0 := by
  have hh := inner_one_self m
  rw [real_inner_self_eq_norm_sq] at hh
  simpa [centroidExcess, qform, matrixMul] using sub_eq_zero.mpr hh


/-- Actual quantitative centroid penalty for every admissible PSD covariance, including singular ones. -/
theorem centroid_matrix_penalty {m : Nat} (hm : 2≤m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R)
    {c : Real} (hc : c ∈ Icc (0:Real) 1) :
    (eta m/alpha m)*centroidExcess R ≤ thresholdDeficit R c := by
  have hm0 : 0<m := by omega
  by_cases he : R=1
  · subst R
    rw [centroidExcess_one, mul_zero]
    exact thresholdDeficit_nonneg hm0 hR c
  obtain ⟨w⟩ := SimplexUniqueness.exists_adaptiveWitnesses_of_isWeakSimplexCov hm0 R hR c
  let g : Real := (q 1*tau m/2)*centroidExcess R
  have hg : 0≤g := mul_nonneg
    (div_nonneg (mul_nonneg (q_pos 1).le (tau_pos hm).le) (by norm_num))
    (centroidExcess_nonneg hm0 hR)
  have hvalue : (m:Real)*Real.log (Phi c)+g ≤ adaptiveValue w :=
    adaptive_value_centroid_gain hm hR hc w
  have hprob := GlobalWitness.exp_adaptive_value_le_orthant_of_ne_one hR he w
  change Real.exp (adaptiveValue w) ≤ orthantCDF R c at hprob
  have hprod : (Phi c)^m*Real.exp g ≤ orthantCDF R c := by
    have hh := Real.exp_le_exp.mpr hvalue
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (Phi_pos c)] at hh
    exact hh.trans hprob
  have hlin := mul_le_mul_of_nonneg_left (Real.add_one_le_exp g)
    (pow_nonneg (Phi_pos c).le m)
  have hp : (2:Real)⁻¹^m ≤ (Phi c)^m := by
    apply pow_le_pow_left₀ (by norm_num)
    simpa only [one_div] using Phi_zero_le hc.1
  have hhalf := mul_le_mul_of_nonneg_right hp hg
  have hid : (eta m/alpha m)*centroidExcess R=(2:Real)⁻¹^m*g := by
    dsimp [eta, g]
    field_simp [ne_of_gt (alpha_pos hm)]
    <;> ring
  rw [hid]
  unfold thresholdDeficit
  nlinarith

#print axioms centroid_matrix_penalty
end SimplexFull.GlobalCentroid
