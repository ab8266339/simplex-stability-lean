import SimplexFull.GlobalCentroidMatrix
noncomputable section
open WeakSimplex
open scoped InnerProductSpace BigOperators
namespace SimplexFull.GlobalCentroid

-- The following elementary quadratic identities parallel the attributed
-- WeakSimplexConjectureLean/Tilt/RankOneInverse algebra and require no inverse.
theorem qform_sub_matrix {m : Nat} (A B : Matrix (Fin m) (Fin m) Real) (x : Coord m) :
    qform (A-B) x = qform A x-qform B x := by
  simp [qform, matrixMul, inner_sub_right]

theorem qform_smul_matrix {m : Nat} (k : Real) (A : Matrix (Fin m) (Fin m) Real) (x : Coord m) :
    qform (k • A) x = k*qform A x := by
  simp [qform, matrixMul, real_inner_smul_right]

theorem qform_allOnes {m : Nat} (x : Coord m) :
    qform (allOnesMatrix m) x = (∑ i, x i)^2 := by
  rw [qform_eq_dotProduct]
  simp [allOnesMatrix, Matrix.mulVec, dotProduct, Coord.toFun, pow_two, Finset.sum_mul]

theorem inner_one_eq_sum {m : Nat} (x : Coord m) :
    inner Real (allOnesVector m) x = ∑ i, x i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [allOnesVector, dotProduct]

theorem inner_one_self (m : Nat) :
    inner Real (allOnesVector m) (allOnesVector m) = (m:Real) := by
  rw [inner_one_eq_sum]
  simp

theorem qform_rankOne_dom {m : Nat} {R : Matrix (Fin m) (Fin m) Real}
    (hdom : (R-(1/(m:Real)) • allOnesMatrix m).PosSemidef) (x : Coord m) :
    (inner Real (allOnesVector m) x)^2/(m:Real) ≤ qform R x := by
  have hh := qform_nonneg_of_posSemidef hdom x
  rw [qform_sub_matrix, qform_smul_matrix, qform_allOnes] at hh
  have hb : (1/(m:Real))*(∑ i, x i)^2 ≤ qform R x := by linarith
  simpa [inner_one_eq_sum, div_eq_mul_inv, mul_comm] using hb

theorem centroid_energy_lower {m : Nat} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R)
    (a : Coord m) (r t : Real) :
    -((m:Real)*r^2+t^2*(qform R (allOnesVector m)-(m:Real)))/2 ≤
      qform R a/2 - t*inner Real (allOnesVector m) (matrixMul R a) -
        (r-t)*inner Real (allOnesVector m) a := by
  have hmR : (0:Real) < m := by exact_mod_cast hm
  have hh := qform_rankOne_dom hR.2 ((-t) • allOnesVector m+a)
  rw [qform_add_smul hR.1.1] at hh
  simp only [inner_add_right, real_inner_smul_right, inner_one_self] at hh
  have hmul := (div_le_iff₀ hmR).mp hh
  apply (mul_le_mul_iff_right₀ hmR).mp
  nlinarith [sq_nonneg (inner Real (allOnesVector m) a-(m:Real)*r)]

#print axioms centroid_energy_lower
end SimplexFull.GlobalCentroid
