import SimplexFull.GaussianShellNormal
import SimplexFull.UniformShell
noncomputable section
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
open SimplexFull.Covariance
theorem uniform_normalShell_maximizes_configPc
    {m : ℕ} [NeZero m] {lam c : ℝ} (hm : 3 ≤ m) (hlam : 0 < lam)
    (hc : 0 < c)
    (hcoer : ∀ H : shellSpace m, c * ‖H‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (shellLoss (m := m) (muFromSNR m lam))) (0, 0) (0, H) (0, H)) :
    ∃ rho0 > 0, ∀ (d : ℕ) (V : Config m d) (z : EuclideanSpace ℝ (Fin d)), gram V = simplexGram m → ‖z‖ = 1 → (∀ i, inner ℝ (V i) z = 0) → ∀ rho : ℝ, 0 < rho → rho < rho0 →
      ∀ X : Config m d, UnitConfig X → procrustesSq X V = rho ^ 2 →
        configPc X lam ≤
          configPc (normalConfig (shellKappa m rho) (shellShift m rho) V z) lam ∧
        (configPc X lam =
            configPc (normalConfig (shellKappa m rho) (shellShift m rho) V z) lam ↔
          orthoOrbit X (normalConfig (shellKappa m rho) (shellShift m rho) V z)) := by
  have hm1 : 1 < m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm0 : m ≠ 0 := NeZero.ne m
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have _hmu : 0 < muFromSNR m lam := muFromSNR_pos hm1 hlam
  obtain ⟨epsQ, hepsQ, deltaQ, hdeltaQ, hmin⟩ :=
    exists_shellLoss_quadratic_min hm2 (muFromSNR m lam) hc hcoer
  obtain ⟨deltaS, hdeltaS, hShell⟩ := exists_uniform_actualShell hm lam
  have h2m : 0 < 2 * (m : ℝ) := mul_pos two_pos (Nat.cast_pos.mpr hmpos)
  refine ⟨min (Real.sqrt epsQ)
      (min deltaQ (min (Real.sqrt deltaS)
        (min (Real.sqrt deltaS) (Real.sqrt (2 * (m : ℝ)))))), ?_, ?_⟩
  · exact lt_min (Real.sqrt_pos.mpr hepsQ)
      (lt_min hdeltaQ (lt_min (Real.sqrt_pos.mpr hdeltaS)
        (lt_min (Real.sqrt_pos.mpr hdeltaS) (Real.sqrt_pos.mpr h2m))))
  · intro d V z hV hz hperp rho hρ0 hρlt X hX hdist
    have hρ_eps : rho < Real.sqrt epsQ := lt_of_lt_of_le hρlt (min_le_left _ _)
    have hρ_tail : rho < min deltaQ (min (Real.sqrt deltaS)
        (min (Real.sqrt deltaS) (Real.sqrt (2 * (m : ℝ))))) :=
      lt_of_lt_of_le hρlt (min_le_right _ _)
    have hρ_dQ : rho < deltaQ := lt_of_lt_of_le hρ_tail (min_le_left _ _)
    have hρ_tail2 : rho < min (Real.sqrt deltaS)
        (min (Real.sqrt deltaS) (Real.sqrt (2 * (m : ℝ)))) :=
      lt_of_lt_of_le hρ_tail (min_le_right _ _)
    have hρ_dS : rho < Real.sqrt deltaS := lt_of_lt_of_le hρ_tail2 (min_le_left _ _)
    have hρ_tail3 : rho < min (Real.sqrt deltaS) (Real.sqrt (2 * (m : ℝ))) :=
      lt_of_lt_of_le hρ_tail2 (min_le_right _ _)
    have hρ_dPc : rho < Real.sqrt deltaS := lt_of_lt_of_le hρ_tail3 (min_le_left _ _)
    have hρ_2m : rho < Real.sqrt (2 * (m : ℝ)) := lt_of_lt_of_le hρ_tail3 (min_le_right _ _)
    have hτ_eps : rho ^ 2 < epsQ := (Real.lt_sqrt hρ0.le).mp hρ_eps
    have hτ_dS : rho ^ 2 < deltaS := (Real.lt_sqrt hρ0.le).mp hρ_dS
    have hτ_dPc : rho ^ 2 < deltaS := (Real.lt_sqrt hρ0.le).mp hρ_dPc
    have hτ_abs : |rho ^ 2| < epsQ := by rwa [abs_of_nonneg (sq_nonneg rho)]
    have hVunit : UnitConfig V := unitConfig_of_simplexGram V hm1 hV
    have hsum : ∑ i, V i = 0 := config_barycenter_of_simplexGram V hm0 hV
    obtain ⟨hk, hkt⟩ := shellShift_sq rho hmpos hρ0 hρ_2m
    set N : Config m d := normalConfig (shellKappa m rho) (shellShift m rho) V z with hNeq
    obtain ⟨hNunit, _, hNdist⟩ :=
      normalShell_geometry rho V z hm hVunit hsum hperp hz hρ0 hρ_2m
    obtain ⟨hmemX, _, hcovX, _, hnormX, hpcX⟩ := hShell d V X (rho ^ 2) hV hX hdist hτ_dS
    obtain ⟨_, _, hcovN, _, _, hpcN⟩ := hShell d V N (rho ^ 2) hV hNunit hNdist hτ_dS
    have hDN : actualDeviation N (procrustesSq N V) = 0 :=
      actualDeviation_normalConfig hm (shellKappa m rho) (shellShift m rho) V z
        hk hV hperp hz hkt
    have hDN' : actualDeviation N (rho ^ 2) = 0 := by
      rw [← hNdist, hNeq]
      exact hDN
    have hrecX : shellCovariance m
        (procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V)
        (actualDeviation X
          (procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V)) =
        channelCovariance X := by
      rw [hNdist]
      exact hcovX
    have hrecN : shellCovariance m
        (procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V)
        (actualDeviation (normalConfig (shellKappa m rho) (shellShift m rho) V z)
          (procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V)) =
        channelCovariance (normalConfig (shellKappa m rho) (shellShift m rho) V z) := by
      rw [hNeq] at hcovN
      rw [hNdist]
      exact hcovN
    have hdev_iff : actualDeviation X (rho ^ 2) = 0 ↔ orthoOrbit X N := by
      rw [← hNdist, hNeq]
      exact actualDeviation_eq_zero_iff_orthoOrbit hm (shellKappa m rho) (shellShift m rho)
        V z hk hV hperp hz hkt X hrecX hrecN
    let DX : shellSpace m := ⟨actualDeviation X (rho ^ 2), hmemX⟩
    have hcoeDX : (DX : ShapeMatrix m) = actualDeviation X (rho ^ 2) := rfl
    have hnormDX : ‖DX‖ < deltaQ := by
      rw [Submodule.coe_norm, hcoeDX]
      calc
        ‖actualDeviation X (rho ^ 2)‖ ≤ Real.sqrt (rho ^ 2) := hnormX
        _ = rho := Real.sqrt_sq hρ0.le
        _ < deltaQ := hρ_dQ
    have hquad := hmin (rho ^ 2) hτ_abs DX hnormDX
    have hlossX : shellLoss (muFromSNR m lam) (rho ^ 2, DX) =
        extendedLoss (muFromSNR m lam) (channelCovariance X) := by
      unfold shellLoss shellCovarianceOnSpace
      rw [hcoeDX, hcovX]
    have hloss0 : shellLoss (muFromSNR m lam) (rho ^ 2, (0 : shellSpace m)) =
        extendedLoss (muFromSNR m lam) (channelCovariance N) := by
      unfold shellLoss shellCovarianceOnSpace
      rw [Submodule.coe_zero, ← hDN', hcovN]
    have hle := hquad.1
    rw [hlossX, hloss0, hpcX, hpcN] at hle
    have hnn : 0 ≤ (c / 4) * ‖DX‖ ^ 2 :=
      mul_nonneg (div_nonneg hc.le (by norm_num)) (sq_nonneg _)
    have hmax : configPc X lam ≤ configPc N lam := by linarith
    have heq_pc : configPc X lam = configPc N lam ↔
        shellLoss (muFromSNR m lam) (rho ^ 2, DX) =
          shellLoss (muFromSNR m lam) (rho ^ 2, (0 : shellSpace m)) := by
      rw [hlossX, hloss0, hpcX, hpcN]
      constructor
      · intro h
        rw [h]
      · intro h
        linarith
    have hDX0 : DX = 0 ↔ actualDeviation X (rho ^ 2) = 0 := by
      rw [← Submodule.coe_eq_zero, hcoeDX]
    refine ⟨hmax, ?_⟩
    constructor
    · intro hpc
      have hloss_eq := (heq_pc).mp hpc
      have hD0 : DX = 0 := (hquad.2).mp hloss_eq
      exact hdev_iff.mp (hDX0.mp hD0)
    · intro horbit
      exact configPc_eq_of_orthoOrbit lam horbit

/-- The shell radius depends only on m and the signal strength, uniformly in the
ambient dimension, the reference regular simplex, and every configuration. -/
def UniformExactNormalShell (m : ℕ) [NeZero m] (lam : ℝ) : Prop :=
  ∃ rho0 > 0, ∀ d : ℕ, m ≤ d → ∀ V : Config m d, gram V=simplexGram m →
    ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖=1 ∧ (∀ i, inner ℝ (V i) z=0) ∧
      ∀ rho : ℝ, 0 < rho → rho < rho0 →
        let N := normalConfig (shellKappa m rho) (shellShift m rho) V z
        UnitConfig N ∧ procrustesSq N V=rho^2 ∧
        configPc N lam=configPc V (lam*shellKappa m rho) ∧
        ∀ X : Config m d, UnitConfig X → procrustesSq X V=rho^2 →
          configPc X lam ≤ configPc V (lam*shellKappa m rho) ∧
          (configPc X lam=configPc V (lam*shellKappa m rho) ↔ orthoOrbit X N)
theorem uniform_exactNormalShell_of_hessian {m : ℕ} [NeZero m] {lam c : ℝ}
    (hm : 3 ≤ m) (hlam : 0 < lam) (hc : 0 < c)
    (hcoer : ∀ H : shellSpace m, c*‖H‖^2 ≤
      fderiv ℝ (fderiv ℝ (shellLoss (m:=m) (muFromSNR m lam)))
        (0,0) (0,H) (0,H)) : UniformExactNormalShell m lam := by
  obtain ⟨r,hr,hopt⟩ := uniform_normalShell_maximizes_configPc hm hlam hc hcoer
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  refine ⟨min r (Real.sqrt (2*(m:ℝ))),
    lt_min hr (Real.sqrt_pos.mpr (by positivity)),?_⟩
  intro d hd V hV
  obtain ⟨z,hz,hperp⟩ := exists_unit_normal_of_simplexGram V hm hd hV
  refine ⟨z,hz,hperp,?_⟩
  intro rho hp hs
  have hs1 : rho < r := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : rho < Real.sqrt (2*(m:ℝ)) := lt_of_lt_of_le hs (min_le_right _ _)
  obtain ⟨hU,hdis,hval⟩ := normalShell_value_and_feasible hm V z hV hz hperp lam rho hp hs2
  refine ⟨hU,hdis,hval,?_⟩
  intro X hX hXdis
  simpa only [hval] using hopt d V z hV hz hperp rho hp hs1 X hX hXdis
/-- Full strict-normal theorem with radius independent of ambient dimension and
reference simplex. Every analytic and geometric hypothesis is instantiated. -/
theorem gaussian_uniform_exact_normal_shell_m4 {m : ℕ} [NeZero m] {lam : ℝ}
    (hm : 4 ≤ m) (hlam : 0 < lam)
    (hgap : (m:ℝ)/2 < a m (muFromSNR m lam)) : UniformExactNormalShell m lam := by
  have hmu : 0 < muFromSNR m lam := muFromSNR_pos (by omega) hlam
  obtain ⟨gamma,hgamma,hQ⟩ := gaussian_shell_coercive_m4 hm hmu hgap
  apply uniform_exactNormalShell_of_hessian (c:=2*gamma) (by omega) hlam
    (mul_pos two_pos hgamma)
  intro H
  rw [gaussian_shell_hessian (by omega) hmu H]
  have hh := hQ H
  nlinarith
theorem gaussian_uniform_exact_normal_shell_m3 {lam : ℝ} (hlam : 0 < lam)
    (hgap : 2 < a 3 (muFromSNR 3 lam)+b 3 (muFromSNR 3 lam)) :
    UniformExactNormalShell 3 lam := by
  have hmu : 0 < muFromSNR 3 lam := muFromSNR_pos (by decide) hlam
  obtain ⟨gamma,hgamma,hQ⟩ := gaussian_shell_coercive_m3 hmu hgap
  apply uniform_exactNormalShell_of_hessian (c:=2*gamma) (by decide) hlam
    (mul_pos two_pos hgamma)
  intro H
  rw [gaussian_shell_hessian (by decide) hmu H]
  have hh := hQ H
  nlinarith
/-- Unique threshold form of the uniform exact-normal theorem. -/
theorem gaussian_normal_threshold_uniform_shell_m4 (m : ℕ) [NeZero m] (hm : 4 ≤ m) :
    ∃ t0 > 0, a m t0=(m:ℝ)/2 ∧
      (∀ s : ℝ, 0 ≤ s → a m s=(m:ℝ)/2 → s=t0) ∧
      ∀ lam : ℝ, 0 < lam → t0 < muFromSNR m lam → UniformExactNormalShell m lam := by
  obtain ⟨t1,t0,t01,h1,h10,h001,he1,he0,he01,hu1,hu0,hu01⟩ :=
    SimplexFull.gaussian_ordered_crossings m hm
  refine ⟨t0,lt_trans h1 h10,he0,?_,?_⟩
  · intro s hs he
    exact hu0 s hs he
  · intro lam hlam hmu
    apply gaussian_uniform_exact_normal_shell_m4 hm hlam
    rw [← he0]
    exact (SimplexFull.strictMono_a m) hmu
theorem gaussian_normal_threshold_uniform_shell_m3 :
    ∃ t0 > 0, a 3 t0+b 3 t0=2 ∧
      (∀ s : ℝ, 0 ≤ s → a 3 s+b 3 s=2 → s=t0) ∧
      ∀ lam : ℝ, 0 < lam → t0 < muFromSNR 3 lam → UniformExactNormalShell 3 lam := by
  obtain ⟨t0,h0,he,hu,hlt,hgt⟩ := SimplexFull.gaussian_triangular_unique_crossing
  refine ⟨t0,h0,by linarith,?_,?_⟩
  · intro s hs heq
    exact hu s hs (by linarith)
  · intro lam hlam hmu
    apply gaussian_uniform_exact_normal_shell_m3 hlam
    have hg := hgt (muFromSNR 3 lam) hmu
    linarith
#print axioms uniform_normalShell_maximizes_configPc
#print axioms uniform_exactNormalShell_of_hessian
#print axioms gaussian_uniform_exact_normal_shell_m4
#print axioms gaussian_uniform_exact_normal_shell_m3
#print axioms gaussian_normal_threshold_uniform_shell_m4
#print axioms gaussian_normal_threshold_uniform_shell_m3
end SimplexFull.Geometry
