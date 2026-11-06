import WeakSimplexConjectureLean.Core.QuadraticCoercivity
import Mathlib.Algebra.QuadraticDiscriminant
noncomputable section
open WeakSimplex
open scoped InnerProductSpace BigOperators
namespace SimplexFull.GlobalCentroid

theorem inner_matrixMul_eq_of_posSemidef {m : Nat}
    {A : Matrix (Fin m) (Fin m) Real} (hA : A.PosSemidef) (x y : Coord m) :
    inner Real (matrixMul A x) y = inner Real x (matrixMul A y) := by
  rw [real_inner_comm]
  simp only [matrixMul, Matrix.inner_toEuclideanCLM]
  have hs : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  simpa only [hs.eq, Coord.toFun] using
    (Matrix.dotProduct_transpose_mulVec A (Coord.toFun x) (Coord.toFun y)).symm

theorem qform_add_smul {m : Nat} {A : Matrix (Fin m) (Fin m) Real}
    (hA : A.PosSemidef) (x y : Coord m) (t : Real) :
    qform A (t • x + y) =
      t^2*qform A x + 2*t*inner Real x (matrixMul A y) + qform A y := by
  have hc : inner Real y (matrixMul A x) = inner Real x (matrixMul A y) := by
    rw [real_inner_comm (matrixMul A x) y, inner_matrixMul_eq_of_posSemidef hA]
  have hm : matrixMul A (t • x+y) = t • matrixMul A x+matrixMul A y := by
    simp [matrixMul]
  change inner Real (t • x+y) (matrixMul A (t • x+y)) = _
  rw [hm]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [hc]
  dsimp [qform]
  ring

theorem qform_cauchy {m : Nat} {A : Matrix (Fin m) (Fin m) Real}
    (hA : A.PosSemidef) (x y : Coord m) :
    (inner Real x (matrixMul A y))^2 ≤ qform A x * qform A y := by
  have hp : ∀ t : Real, 0 ≤ qform A x * (t*t) +
      (2*inner Real x (matrixMul A y))*t + qform A y := by
    intro t
    have hh := qform_nonneg_of_posSemidef hA (t • x+y)
    rw [qform_add_smul hA] at hh
    nlinarith
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

#print axioms qform_cauchy

def coordBasis {m : Nat} (i : Fin m) : Coord m := Coord.ofFun (Pi.single i 1)

theorem inner_coordBasis {m : Nat} (i : Fin m) (x : Coord m) :
    inner Real (coordBasis i) x = x i := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [coordBasis, Coord.ofFun, dotProduct, Pi.single_apply]

theorem matrixMul_coordBasis {m : Nat} (A : Matrix (Fin m) (Fin m) Real) (i j : Fin m) :
    matrixMul A (coordBasis i) j = A j i := by
  classical
  simp [coordBasis, matrixMul_ofFun, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem qform_coordBasis {m : Nat} (A : Matrix (Fin m) (Fin m) Real) (i : Fin m) :
    qform A (coordBasis i) = A i i := by
  rw [qform, inner_coordBasis, matrixMul_coordBasis]

theorem matrixMul_one_apply {m : Nat} (A : Matrix (Fin m) (Fin m) Real) (i : Fin m) :
    matrixMul A (allOnesVector m) i = ∑ j, A i j := by
  simp [allOnesVector, matrixMul_ofFun, Matrix.mulVec, dotProduct]

theorem entry_sq_le {m : Nat} {A : Matrix (Fin m) (Fin m) Real}
    (hA : A.PosSemidef) (i j : Fin m) : (A i j)^2 ≤ A i i * A j j := by
  have hc := qform_cauchy hA (coordBasis i) (coordBasis j)
  rwa [inner_coordBasis, matrixMul_coordBasis, qform_coordBasis, qform_coordBasis] at hc

theorem row_sq_le {m : Nat} {A : Matrix (Fin m) (Fin m) Real}
    (hA : A.PosSemidef) (i : Fin m) :
    (matrixMul A (allOnesVector m) i)^2 ≤ A i i * qform A (allOnesVector m) := by
  have hc := qform_cauchy hA (coordBasis i) (allOnesVector m)
  rwa [inner_coordBasis, qform_coordBasis] at hc

#print axioms row_sq_le

theorem sum_row_sq_le {m : Nat} {A : Matrix (Fin m) (Fin m) Real} {alpha : Real}
    (hA : A.PosSemidef) (hdiag : ∀ i, A i i=alpha) :
    (∑ i, (matrixMul A (allOnesVector m) i)^2) ≤
      (m:Real)*alpha*qform A (allOnesVector m) := by
  calc
    _ ≤ ∑ _i : Fin m, alpha*qform A (allOnesVector m) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hdiag i] using row_sq_le hA i
    _ = _ := by simp; ring

theorem row_abs_le {m : Nat} {A : Matrix (Fin m) (Fin m) Real} {alpha : Real}
    (hA : A.PosSemidef) (ha : 0 ≤ alpha) (hdiag : ∀ i, A i i=alpha) (i : Fin m) :
    |matrixMul A (allOnesVector m) i| ≤ (m:Real)*alpha := by
  have he : ∀ j, |A i j| ≤ alpha := by
    intro j
    have hs := entry_sq_le hA i j
    rw [hdiag i, hdiag j] at hs
    nlinarith [sq_abs (A i j), abs_nonneg (A i j)]
  rw [matrixMul_one_apply]
  calc
    _ ≤ ∑ j, |A i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, alpha := Finset.sum_le_sum fun j _ => he j
    _ = _ := by simp

#print axioms sum_row_sq_le
#print axioms row_abs_le
end SimplexFull.GlobalCentroid
