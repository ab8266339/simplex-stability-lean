import SimplexFull.GlobalMeanWidthBase
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace SimplexFull.Geometry

/-- Real support function, evaluated on the actual set of inner products.
The following finite-convex-hull theorem supplies boundedness and attainment. -/
def realSupport {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun y => inner ℝ g y) '' K)

variable {m d : ℕ} [NeZero m]

theorem inner_vertex_le_maxCoord (X : Config m d)
    (g : EuclideanSpace ℝ (Fin d)) (i : Fin m) :
    inner ℝ g (X i) ≤ maxCoord (scoreMap X g) := by
  have hh := Finset.le_sup' (fun j => scoreMap X g j) (Finset.mem_univ i)
  simpa only [maxCoord, scoreMap_apply, real_inner_comm g (X i)] using hh

theorem inner_convexHull_range_le_maxCoord (X : Config m d)
    (g y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ convexHull ℝ (range X)) :
    inner ℝ g y ≤ maxCoord (scoreMap X g) := by
  have hs : range X ⊆ {z | inner ℝ g z ≤ maxCoord (scoreMap X g)} := by
    rintro z ⟨i,rfl⟩
    exact inner_vertex_le_maxCoord X g i
  have hc : Convex ℝ {z | inner ℝ g z ≤ maxCoord (scoreMap X g)} := by
    intro x hx z hz a b ha hb hab
    change inner ℝ g (a • x + b • z) ≤ _
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hbz := mul_le_mul_of_nonneg_left hz hb
    calc
      _ ≤ a * maxCoord (scoreMap X g) + b * maxCoord (scoreMap X g) := add_le_add hax hbz
      _ = (a+b) * maxCoord (scoreMap X g) := by ring
      _ = _ := by rw [hab, one_mul]
  exact convexHull_min hs hc hy

theorem support_convexHull_range_isGreatest (X : Config m d)
    (g : EuclideanSpace ℝ (Fin d)) :
    IsGreatest ((fun y => inner ℝ g y) '' convexHull ℝ (range X))
      (maxCoord (scoreMap X g)) := by
  classical
  constructor
  · obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup' univNonempty (fun i => scoreMap X g i)
    refine ⟨X i, subset_convexHull ℝ (range X) (mem_range_self i), ?_⟩
    change maxCoord (scoreMap X g) = scoreMap X g i at hmax
    rw [hmax]
    rw [scoreMap_apply]
    exact (real_inner_comm g (X i)).symm
  · rintro t ⟨y,hy,rfl⟩
    exact inner_convexHull_range_le_maxCoord X g y hy

/-- The actual support of a finite convex hull is the attained finite score maximum. -/
theorem realSupport_convexHull_range (X : Config m d)
    (g : EuclideanSpace ℝ (Fin d)) :
    realSupport (convexHull ℝ (range X)) g = maxCoord (scoreMap X g) := by
  have hh := support_convexHull_range_isGreatest X g
  exact hh.isLUB.csSup_eq ⟨_,hh.1⟩

theorem continuous_realSupport_convexHull_range (X : Config m d) :
    Continuous (realSupport (convexHull ℝ (range X))) := by
  have he : realSupport (convexHull ℝ (range X)) =
      fun g => maxCoord (scoreMap X g) := funext (realSupport_convexHull_range X)
  rw [he]
  exact continuous_maxCoord.comp (scoreMap X).continuous

theorem integrable_realSupport_convexHull_range (X : Config m d) :
    Integrable (realSupport (convexHull ℝ (range X)))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have he : realSupport (convexHull ℝ (range X)) =
      fun g => maxCoord (scoreMap X g) := funext (realSupport_convexHull_range X)
  rw [he]
  exact integrable_configGaussianMax X

theorem integral_realSupport_convexHull_range (X : Config m d) :
    (∫ g, realSupport (convexHull ℝ (range X)) g
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) = configGaussianMax X := by
  simp_rw [realSupport_convexHull_range]
  exact (configGaussianMax_eq_integral X).symm

#print axioms support_convexHull_range_isGreatest
#print axioms realSupport_convexHull_range
#print axioms integral_realSupport_convexHull_range
end SimplexFull.Geometry
