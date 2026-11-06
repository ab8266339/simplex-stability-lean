import SimplexFull.OrthantMomentTable
import SimplexFull.OrthantAlgebra

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SimplexFull.Covariance
variable {m : ℕ}

theorem integral_orthant_pair_moment2 (c : ℝ) (i j : Fin m) :
    ∫ x in orthantIic c, rho 1 x*(x i*x j) = Phi c^m*moment2 (-q c) (sigma c) i j := by
  by_cases hij : i=j
  · subst j
    rw [integral_orthant_pair_same_normalized]
    simp [moment2]
  · rw [integral_orthant_pair_distinct_normalized c hij]
    simp [moment2, hij]

theorem integral_orthant_quad_moment4 (c : ℝ) {i j k l : Fin m}
    (hij : i ≠ j) (hkl : k ≠ l) :
    ∫ x in orthantIic c, rho 1 x*(x i*x j*x k*x l) =
      Phi c^m*moment4 (-q c) (sigma c) i j k l := by
  by_cases hik : i=k
  · subst k
    by_cases hjl : j=l
    · subst l
      convert integral_orthant_twoPowers c hij 2 2 using 1
      · congr 1; ext x; ring
      · simp only [if_true, if_false, moment4, kronecker, hij, (Ne.symm hij), normMoment_two]
        ring
    · convert integral_orthant_threePowers c hij hkl hjl 2 1 1 using 1
      · congr 1; ext x; ring
      · simp only [if_true, if_false, moment4, kronecker, hij, hkl, hjl, (Ne.symm hij), (Ne.symm hkl), (Ne.symm hjl),
          normMoment_two, normMoment_one]
        ring
  · by_cases hil : i=l
    · subst l
      by_cases hjk : j=k
      · subst k
        convert integral_orthant_twoPowers c hij 2 2 using 1
        · congr 1; ext x; ring
        · simp only [if_true, if_false, moment4, kronecker, hij, (Ne.symm hij), normMoment_two]
          ring
      · convert integral_orthant_threePowers c hij hik hjk 2 1 1 using 1
        · congr 1; ext x; ring
        · simp only [if_true, if_false, moment4, kronecker, hij, hik, hjk, (Ne.symm hij), (Ne.symm hik), (Ne.symm hjk),
            normMoment_two, normMoment_one]
          ring
    · by_cases hjk : j=k
      · subst k
        convert integral_orthant_threePowers c (Ne.symm hij) hkl hil 2 1 1 using 1
        · congr 1; ext x; ring
        · simp only [if_true, if_false, moment4, kronecker, hij, hil, hkl, (Ne.symm hij), (Ne.symm hil), (Ne.symm hkl),
            normMoment_two, normMoment_one]
          ring
      · by_cases hjl : j=l
        · subst l
          convert integral_orthant_threePowers c (Ne.symm hij) hjk hik 2 1 1 using 1
          · congr 1; ext x; ring
          · simp only [if_true, if_false, moment4, kronecker, hij, hik, hjk, (Ne.symm hij), (Ne.symm hik), (Ne.symm hjk),
              normMoment_two, normMoment_one]
            ring
        · convert integral_orthant_fourPowers c hij hik hil hjk hjl hkl 1 1 1 1 using 1
          · congr 1; ext x; ring
          · simp only [if_true, if_false, moment4, kronecker, hij, hik, hil, hjk, hjl, hkl, normMoment_one]
            ring

#print axioms integral_orthant_pair_moment2
#print axioms integral_orthant_quad_moment4
end SimplexFull.Covariance