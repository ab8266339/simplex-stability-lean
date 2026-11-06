import SimplexFull.GlobalMeanWidthBase
import Mathlib.Algebra.BigOperators.Fin
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull.Geometry

def BallConfig {m d : ℕ} (X : Config m d) : Prop := ∀ i, ‖X i‖ ≤ 1

def energyDeficit {m d : ℕ} (X : Config m d) (i : Fin m) : ℝ :=
  1 - ‖X i‖^2

def widthConcatVec {d k : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (d+k)) :=
  WithLp.toLp 2 (Fin.addCases (fun i => x i) (fun j => y j))

theorem inner_widthConcatVec {d k : ℕ} (x x' : EuclideanSpace ℝ (Fin d))
    (y y' : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (widthConcatVec x y) (widthConcatVec x' y') =
      inner ℝ x x' + inner ℝ y y' := by
  simp only [euclidean_inner_eq_sum]
  rw [Fin.sum_univ_add]
  simp [widthConcatVec]

/-- Add a distinct orthogonal coordinate for each vertex. -/
def orthogonalUnitLift {m d : ℕ} (X : Config m d) : Config m (d+m) :=
  fun i => widthConcatVec (X i) (EuclideanSpace.single i (Real.sqrt (energyDeficit X i)))

theorem energyDeficit_bounds {m d : ℕ} (X : Config m d) (hX : BallConfig X) (i : Fin m) :
    0 ≤ energyDeficit X i ∧ energyDeficit X i ≤ 1 := by
  have hn := norm_nonneg (X i)
  have hu := hX i
  unfold energyDeficit
  constructor <;> nlinarith [sq_nonneg ‖X i‖]

theorem gram_orthogonalUnitLift {m d : ℕ} (X : Config m d) (hX : BallConfig X) :
    gram (orthogonalUnitLift X) = gram X + Matrix.diagonal (energyDeficit X) := by
  ext i j
  simp only [gram_apply, orthogonalUnitLift, inner_widthConcatVec, Matrix.add_apply]
  congr 1
  by_cases hij : i = j
  · subst j
    simp [EuclideanSpace.inner_single_left, Real.sq_sqrt (energyDeficit_bounds X hX i).1,
      ← pow_two]
  · simp [EuclideanSpace.inner_single_left, PiLp.single_apply, Matrix.diagonal_apply,
      hij, Ne.symm hij]

theorem unitConfig_orthogonalUnitLift {m d : ℕ} (X : Config m d) (hX : BallConfig X) :
    UnitConfig (orthogonalUnitLift X) := by
  intro i
  have hii : inner ℝ (orthogonalUnitLift X i) (orthogonalUnitLift X i) = 1 := by
    rw [← gram_apply, gram_orthogonalUnitLift X hX, Matrix.add_apply,
      Matrix.diagonal_apply_eq, gram_apply, real_inner_self_eq_norm_sq, energyDeficit]
    ring
  rw [norm_eq_sqrt_real_inner, hii, Real.sqrt_one]

theorem centroid_sq_orthogonalUnitLift {m d : ℕ} (X : Config m d) (hX : BallConfig X) :
    ‖∑ i, orthogonalUnitLift X i‖^2 =
      ‖∑ i, X i‖^2 + ∑ i, energyDeficit X i := by
  rw [← global_entrySum_gram, gram_orthogonalUnitLift X hX]
  simp only [entrySum, Matrix.add_apply, Finset.sum_add_distrib]
  rw [← entrySum, global_entrySum_gram]
  simp [Matrix.diagonal_apply]

theorem frobSq_gram_lift_identity {m d : ℕ} (hm : 2 ≤ m)
    (X : Config m d) (hX : BallConfig X) :
    frobSq (gram X-simplexGram m) =
      frobSq (gram (orthogonalUnitLift X)-simplexGram m) +
        ∑ i, (energyDeficit X i)^2 := by
  have hterm : ∀ i j,
      ((gram X-simplexGram m) i j)^2 =
        ((gram (orthogonalUnitLift X)-simplexGram m) i j)^2 +
          (if i=j then (energyDeficit X i)^2 else 0) := by
    intro i j
    by_cases hij : i=j
    · subst j
      rw [Matrix.sub_apply, gram_apply, real_inner_self_eq_norm_sq,
        simplexGram_diagonal m (by omega), Matrix.sub_apply,
        gram_diagonal_unit _ (unitConfig_orthogonalUnitLift X hX),
        simplexGram_diagonal m (by omega)]
      simp only [ite_true, sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_add, energyDeficit]
      ring
    · rw [gram_orthogonalUnitLift X hX]
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply, hij]
  simp only [frobSq, hterm, Finset.sum_add_distrib]
  simp

#print axioms gram_orthogonalUnitLift
#print axioms unitConfig_orthogonalUnitLift
#print axioms centroid_sq_orthogonalUnitLift
#print axioms frobSq_gram_lift_identity
end SimplexFull.Geometry
