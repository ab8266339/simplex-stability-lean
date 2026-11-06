import SimplexFull.CenteredSqrt
import SimplexFull.ProcrustesFormula
import SimplexFull.NormalMinimizer
import Mathlib.Analysis.Normed.Ring.Units
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
namespace SimplexFull.Geometry
def rootCompletion {m d : ℕ} (X : Config m d) : ShapeMatrix m :=
  centeredRoot X + (1-centering m)
lemma continuous_rootCompletion {m d : ℕ} (hm : 1 ≤ m) :
    Continuous (@rootCompletion m d) :=
  (continuous_centeredRoot hm).add continuous_const
lemma rootCompletion_of_simplex {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) : rootCompletion V = 1 := by
  rw [rootCompletion, centeredRoot_of_simplex V hm hV, add_sub_cancel]
lemma rootCompletion_act {m d : ℕ} (U : Orthogonal d) (X : Config m d) :
    rootCompletion (act U X) = rootCompletion X := by
  simp only [rootCompletion, centeredRoot, centeredGram, gram_act]
lemma exists_ball_rootCompletion_isUnit {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) :
    ∃ eps > 0, ∀ X : Config m d, ‖X-V‖ < eps → IsUnit (rootCompletion X) := by
  have hopen : IsOpen {X : Config m d | IsUnit (rootCompletion X)} :=
    Units.isOpen.preimage (continuous_rootCompletion (by omega))
  have hmem : V ∈ {X : Config m d | IsUnit (rootCompletion X)} := by
    change IsUnit (rootCompletion V)
    rw [rootCompletion_of_simplex V hm hV]
    exact isUnit_one
  obtain ⟨eps, heps, hb⟩ := Metric.isOpen_iff.mp hopen V hmem
  refine ⟨eps,heps, fun X hX => hb ?_⟩
  simpa only [Metric.mem_ball, dist_eq_norm] using hX
#print axioms exists_ball_rootCompletion_isUnit
lemma aligned_norm_lt_of_energy_lt {m d : ℕ} (X V : Config m d) (U : Orthogonal d)
    {eps : ℝ} (heps : 0 < eps) (h : procrustesEnergy X V U < eps^2) :
    ‖act U.symm X - V‖ < eps := by
  apply (pi_norm_lt_iff heps).mpr
  intro i
  change ‖U.symm (X i)-V i‖ < eps
  have hn : ‖U.symm (X i)-V i‖ = ‖X i-U (V i)‖ := by
    simpa only [map_sub, U.apply_symm_apply] using
      (U.norm_map (U.symm (X i)-V i)).symm
  rw [hn]
  have hi : ‖X i-U (V i)‖^2 ≤ procrustesEnergy X V U :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖X j-U (V j)‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (X i-U (V i))]
lemma exists_procrustes_neighborhood_isUnit {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) :
    ∃ delta > 0, ∀ X : Config m d, procrustesSq X V < delta →
      IsUnit (rootCompletion X) := by
  obtain ⟨eps, heps, hb⟩ := exists_ball_rootCompletion_isUnit V hm hV
  refine ⟨eps^2, sq_pos_of_pos heps, ?_⟩
  intro X hX
  obtain ⟨a, ⟨U,rfl⟩, ha⟩ := exists_lt_of_csInf_lt
    (procrustesEnergy_range_nonempty X V) hX
  have hclose := aligned_norm_lt_of_energy_lt X V U heps ha
  have hunit := hb (act U.symm X) hclose
  rwa [rootCompletion_act] at hunit
#print axioms exists_procrustes_neighborhood_isUnit
theorem exists_local_procrustes_formula {m d : ℕ} (hm : 3 ≤ m) (V : Config m d)
    (hV : gram V = simplexGram m) :
    ∃ delta > 0, ∀ X : Config m d, UnitConfig X → procrustesSq X V < delta →
      procrustesSq X V = 2*(m:ℝ)-2/alpha m*Matrix.trace (centeredRoot X) := by
  obtain ⟨delta,hdelta,hu⟩ := exists_procrustes_neighborhood_isUnit V (by omega) hV
  refine ⟨delta,hdelta,?_⟩
  intro X hX hclose
  obtain ⟨hPT,hTP⟩ := centered_mul_centering (centeredRoot_centered X (by omega))
  exact procrustesSq_sqrt hm X V hX (unitConfig_of_simplexGram V (by omega) hV)
    hV (centeredRoot X) (centeredRoot_posSemidef X) hPT hTP
    (centeredRoot_mul_self X (by omega)) (hu X hclose)
#print axioms exists_local_procrustes_formula
end SimplexFull.Geometry