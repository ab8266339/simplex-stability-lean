import SimplexFull.UniformNeighborhood
import SimplexFull.ActualShell
import SimplexFull.ShellProbability
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]
theorem exists_uniform_actualShell (hm : 3 ≤ m) (lam : ℝ) :
    ∃ delta > 0, ∀ (d : ℕ) (V X : Config m d) (tau : ℝ),
      gram V=simplexGram m → UnitConfig X → procrustesSq X V=tau → tau<delta →
      actualDeviation X tau ∈ shellSpace m ∧ frobSq (actualDeviation X tau) ≤ tau ∧
      shellCovariance m tau (actualDeviation X tau)=channelCovariance X ∧
      ‖actualDeviation X tau‖^2 ≤ frobSq (actualDeviation X tau) ∧
      ‖actualDeviation X tau‖ ≤ Real.sqrt tau ∧
      extendedLoss (muFromSNR m lam) (channelCovariance X)=configPc V lam-configPc X lam := by
  obtain ⟨delta,hdelta,hpack⟩ := exists_uniform_geometric_neighborhood m hm
  refine ⟨delta,hdelta,?_⟩
  intro d V X tau hV hX hτ hlt
  have hclose : procrustesSq X V<delta := by rwa [hτ]
  obtain ⟨hunit,hpd⟩ := hpack d V X hV hX hclose
  obtain ⟨hPT,hTP⟩ := centered_mul_centering (centeredRoot_centered X (by omega))
  have hTsq : centeredRoot X*centeredRoot X=
      (alpha m) • (centering m*gram X*centering m) := by
    rw [centeredRoot_mul_self X (by omega),centeredGram,compression]
  have hK : IsUnit (centeredRoot X+(1-centering m)) := by simpa [rootCompletion] using hunit
  have henc := shell_enclosure hm X V hX hV (centeredRoot X)
    (centeredRoot_posSemidef X) hPT hTP hTsq hK tau hτ
  rcases henc with ⟨_,_,_,_,hmem,_,_,_,hle,hcov⟩
  have hmem' : actualDeviation X tau ∈ shellSpace m := hmem
  have hle' : frobSq (actualDeviation X tau)≤tau := hle
  have hcov' : shellCovariance m tau (actualDeviation X tau)=channelCovariance X := hcov
  have hnorm : ‖actualDeviation X tau‖≤Real.sqrt tau :=
    (l2_opNorm_le_sqrt_frobSq _).trans (Real.sqrt_le_sqrt hle')
  exact ⟨hmem',hle',hcov',l2_opNorm_sq_le_frobSq _,hnorm,extendedLoss_channelCovariance (by omega) V X hV hpd lam⟩
#print axioms exists_uniform_actualShell
end SimplexFull.Geometry

