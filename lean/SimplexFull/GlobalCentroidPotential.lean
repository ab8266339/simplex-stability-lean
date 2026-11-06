import SimplexFull.GlobalCentroidRows
import SimplexFull.GlobalScalarRange
import SimplexFull.GlobalCentroidEnergy
import SimplexUniquenessLean.SingularWitnesses
noncomputable section
open WeakSimplex Set
open scoped InnerProductSpace BigOperators
namespace SimplexFull.GlobalCentroid
open GlobalScalar

theorem Psi_tangent_upper {x y : Real} (hx : 0 < x) (hy : 0 < y) :
    Psi y ≤ Psi x + q (hInv x)*(y-x) := by
  have hconv : ConvexOn Real (Ioi (0:Real)) (fun z => -Psi z) :=
    strictConcaveOn_Psi.concaveOn.neg
  have hd := (hasDerivAt_Psi hx).neg
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hh := hconv.le_slope_of_hasDerivAt hx hy hlt hd
    rw [slope_def_field] at hh
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hh
    try dsimp at hm
    nlinarith
  · subst y
    simp
  · have hh := hconv.slope_le_of_hasDerivAt hy hx hgt hd
    rw [slope_def_field] at hh
    have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hh
    try dsimp at hm
    nlinarith

theorem witness_a_eq_q {m : Nat} {R : Matrix (Fin m) (Fin m) Real} {c : Real}
    (w : AdaptiveWitnesses R c) (i : Fin m) : w.a i=q (w.s i) := w.a_eq_r i

theorem witness_h_eq {m : Nat} {R : Matrix (Fin m) (Fin m) Real} {c : Real}
    (w : AdaptiveWitnesses R c) (i : Fin m) : h (w.s i)=c+matrixMul R w.a i := by
  have hh := congrArg (fun x : Coord m => x i) w.compatibility
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, allOnesVector_apply, mul_one] at hh
  dsimp [h]
  rw [← witness_a_eq_q w i]
  linarith

theorem inner_eq_sum {m : Nat} (a b : Coord m) :
    inner Real a b = ∑ i, a i*b i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

def adaptiveValue {m : Nat} {R : Matrix (Fin m) (Fin m) Real} {c : Real}
    (w : AdaptiveWitnesses R c) : Real :=
  (∑ i, psiPull (w.s i))-qform R w.a/2

def trialCoordinate {m : Nat} (R : Matrix (Fin m) (Fin m) Real) (c t : Real) (i : Fin m) : Real :=
  h c+t*(matrixMul R (allOnesVector m) i-1)

#print axioms Psi_tangent_upper
#print axioms witness_h_eq

theorem adaptive_value_ge_centroid_trial {m : Nat} (hm : 0<m)
    {R : Matrix (Fin m) (Fin m) Real} {c : Real} (hR : IsWeakSimplexCov R)
    (w : AdaptiveWitnesses R c) (t : Real) (hb : ∀ i, 0<trialCoordinate R c t i) :
    (∑ i, Psi (trialCoordinate R c t i))-
      ((m:Real)*(q c)^2+t^2*centroidExcess R)/2 ≤ adaptiveValue w := by
  have hs : (∑ i, Psi (trialCoordinate R c t i)) ≤
      (∑ i, psiPull (w.s i))+(∑ i, w.a i*(trialCoordinate R c t i-h (w.s i))) := by
    calc
      _ ≤ ∑ i, (psiPull (w.s i)+w.a i*(trialCoordinate R c t i-h (w.s i))) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := Psi_tangent_upper (h_pos (w.s i)) (hb i)
        rwa [Psi_h, hInv_h, ← witness_a_eq_q w i] at hi
      _ = _ := Finset.sum_add_distrib
  have hlin : (∑ i, w.a i*(trialCoordinate R c t i-h (w.s i))) =
      t*inner Real (allOnesVector m) (matrixMul R w.a)+
      (q c-t)*inner Real (allOnesVector m) w.a-qform R w.a := by
    have hx : inner Real w.a (matrixMul R (allOnesVector m)) =
        inner Real (allOnesVector m) (matrixMul R w.a) := by
      rw [real_inner_comm (matrixMul R (allOnesVector m)) w.a]
      exact inner_matrixMul_eq_of_posSemidef hR.1.1 _ _
    rw [← hx]
    simp only [qform, inner_eq_sum, allOnesVector_apply, one_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [witness_h_eq]
    dsimp [trialCoordinate, h]
    ring
  rw [hlin] at hs
  have he := centroid_energy_lower hm hR w.a (q c) t
  dsimp [adaptiveValue, centroidExcess]
  nlinarith

#print axioms adaptive_value_ge_centroid_trial
end SimplexFull.GlobalCentroid
