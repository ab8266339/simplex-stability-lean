import SimplexFull.NormalShellOptimization
import SimplexFull.GaussianShift
noncomputable section
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
/-- Common normal Gaussian displacement gives the exact scaled-SNR value. -/
theorem configPc_normalConfig {m d : ℕ} [NeZero m] (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hk : 0 ≤ k) (hkt : k^2+t^2=1)
    (hperp : ∀ i, inner ℝ (V i) z=0) (hz : ‖z‖=1) (lam : ℝ) :
    configPc (normalConfig k t V z) lam = configPc V (lam*k) := by
  unfold configPc
  rw [gram_normalConfig k t V z hperp hz]
  exact SimplexFull.decodingSuccess_commonShift (gram V) (gram_posSemidef V) hk hkt lam
/-- The normal point is feasible on the true Procrustes shell and attains the
regular simplex success probability at precisely the reduced signal strength. -/
theorem normalShell_value_and_feasible {m d : ℕ} [NeZero m] (hm : 3 ≤ m)
    (V : Config m d) (z : EuclideanSpace ℝ (Fin d)) (hV : gram V=simplexGram m)
    (hz : ‖z‖=1) (hperp : ∀ i, inner ℝ (V i) z=0) (lam rho : ℝ)
    (hrho : 0 < rho) (hsmall : rho < Real.sqrt (2*(m:ℝ))) :
    UnitConfig (normalConfig (shellKappa m rho) (shellShift m rho) V z) ∧
    procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V=rho^2 ∧
    configPc (normalConfig (shellKappa m rho) (shellShift m rho) V z) lam =
      configPc V (lam*shellKappa m rho) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨hU, _, hdist⟩ := normalShell_geometry rho V z hm
    (unitConfig_of_simplexGram V (by omega) hV)
    (config_barycenter_of_simplexGram V hm0 hV) hperp hz hrho hsmall
  obtain ⟨hk,hkt⟩ := shellShift_sq rho (by omega) hrho hsmall
  exact ⟨hU,hdist,configPc_normalConfig _ _ V z hk hkt hperp hz lam⟩
/-- Exact small-shell assertion, including attainment, best value, and all equality
cases. The shell uses the actual infimum over the full orthogonal group. -/
def ExactNormalShell {m d : ℕ} [NeZero m] (V : Config m d) (lam : ℝ) : Prop :=
  ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖=1 ∧ (∀ i, inner ℝ (V i) z=0) ∧
    ∃ rho0 > 0, ∀ rho : ℝ, 0 < rho → rho < rho0 →
      let N := normalConfig (shellKappa m rho) (shellShift m rho) V z
      UnitConfig N ∧ procrustesSq N V=rho^2 ∧
      configPc N lam=configPc V (lam*shellKappa m rho) ∧
      ∀ X : Config m d, UnitConfig X → procrustesSq X V=rho^2 →
        configPc X lam ≤ configPc V (lam*shellKappa m rho) ∧
        (configPc X lam=configPc V (lam*shellKappa m rho) ↔ orthoOrbit X N)
/-- All geometric and probability conclusions, given point Hessian coercivity. -/
theorem exactNormalShell_of_hessian {m d : ℕ} [NeZero m] {lam c : ℝ}
    (hm : 3 ≤ m) (hd : m ≤ d) (hlam : 0 < lam) (V : Config m d)
    (hV : gram V=simplexGram m) (hc : 0 < c)
    (hcoer : ∀ H : shellSpace m, c*‖H‖^2 ≤
      fderiv ℝ (fderiv ℝ (shellLoss (m:=m) (muFromSNR m lam)))
        (0,0) (0,H) (0,H)) : ExactNormalShell V lam := by
  obtain ⟨z,hz,hperp,r,hr,hopt⟩ :=
    exists_normalShell_maximizes_configPc hm hd hlam V hV hc hcoer
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  refine ⟨z,hz,hperp,min r (Real.sqrt (2*(m:ℝ))),
    lt_min hr (Real.sqrt_pos.mpr (by positivity)),?_⟩
  intro rho hp hs
  have hs1 : rho < r := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : rho < Real.sqrt (2*(m:ℝ)) := lt_of_lt_of_le hs (min_le_right _ _)
  obtain ⟨hU,hdis,hval⟩ := normalShell_value_and_feasible hm V z hV hz hperp lam rho hp hs2
  refine ⟨hU,hdis,hval,?_⟩
  intro X hX hXdis
  simpa only [hval] using hopt rho hp hs1 X hX hXdis
#print axioms configPc_normalConfig
#print axioms normalShell_value_and_feasible
#print axioms exactNormalShell_of_hessian
end SimplexFull.Geometry
