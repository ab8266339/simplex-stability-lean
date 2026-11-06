import SimplexFull.TaylorDefinitions
import SimplexFull.UniformNormalShell
noncomputable section
namespace SimplexFull.Geometry
/-- The exact optimum together with the manuscript's quantitative sixth-order remainder,
uniform over ambient dimension and regular simplex embedding. -/
def UniformTaylorNormalShell (m : ℕ) [NeZero m] (lam : ℝ) : Prop :=
  ∃ C > 0, ∃ rho0 > 0, ∀ d : ℕ, m ≤ d → ∀ V : Config m d, gram V=simplexGram m →
    ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖=1 ∧ (∀ i, inner ℝ (V i) z=0) ∧
      ∀ rho : ℝ, 0 < rho → rho < rho0 →
        let N := normalConfig (shellKappa m rho) (shellShift m rho) V z
        UnitConfig N ∧ procrustesSq N V=rho^2 ∧
        configPc V lam-configPc N lam=normalDeficit m lam rho ∧
        |configPc V lam-configPc N lam-normalTaylorPolynomial m lam rho| ≤ C*rho^6 ∧
        ∀ X : Config m d, UnitConfig X → procrustesSq X V=rho^2 →
          normalDeficit m lam rho ≤ configPc V lam-configPc X lam ∧
          (configPc V lam-configPc X lam=normalDeficit m lam rho ↔ orthoOrbit X N)
theorem uniformTaylorNormalShell_of_bound {m : ℕ} [NeZero m] {lam : ℝ}
    (hopt : UniformExactNormalShell m lam)
    (hbound : ∃ C > 0, ∃ r > 0, ∀ rho : ℝ, |rho|<r →
      |normalTaylorRemainder m lam rho| ≤ C*|rho|^6) : UniformTaylorNormalShell m lam := by
  obtain ⟨r0,hr0,hopt⟩ := hopt
  obtain ⟨C,hC,r,hr,hbound⟩ := hbound
  refine ⟨C,hC,min r0 r,lt_min hr0 hr,?_⟩
  intro d hd V hV
  obtain ⟨z,hz,hperp,hzopt⟩ := hopt d hd V hV
  refine ⟨z,hz,hperp,?_⟩
  intro rho hp hs
  have hs0 : rho<r0 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs1 : rho<r := lt_of_lt_of_le hs (min_le_right _ _)
  obtain ⟨hU,hdis,hval,hmax⟩ := hzopt rho hp hs0
  have hVval := configPc_eq_simplexSuccess V hV lam
  have hVscaled := configPc_eq_simplexSuccess V hV (lam*shellKappa m rho)
  have hdelt : configPc V lam-
      configPc (normalConfig (shellKappa m rho) (shellShift m rho) V z) lam =
      normalDeficit m lam rho := by
    rw [hval,hVval,hVscaled]
    rfl
  refine ⟨hU,hdis,hdelt,?_,?_⟩
  · rw [hdelt]
    have hb := hbound rho (by rwa [abs_of_pos hp])
    simpa only [normalTaylorRemainder,abs_of_pos hp] using hb
  · intro X hX hdist
    obtain ⟨hle,heq⟩ := hmax X hX hdist
    have hd : normalDeficit m lam rho=configPc V lam-configPc V (lam*shellKappa m rho) := by
      rw [hVval,hVscaled]
      rfl
    rw [hd]
    refine ⟨by linarith,?_⟩
    have hEq : configPc V lam-configPc X lam=configPc V lam-configPc V (lam*shellKappa m rho) ↔
        configPc X lam=configPc V (lam*shellKappa m rho) := by
      constructor <;> intro h <;> linarith
    exact hEq.trans heq
#print axioms uniformTaylorNormalShell_of_bound
end SimplexFull.Geometry
