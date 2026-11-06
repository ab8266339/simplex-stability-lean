import SimplexFull.ActualShell
import SimplexFull.ShellLocalMinimum
import SimplexFull.ShellProbability

/-!
Normal-shell optimization. The point Hessian coercivity of `shellLoss` stays a
hypothesis; every other geometric or Gaussian fact is taken from a compiled module.
-/

noncomputable section

open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace SimplexFull.Geometry

/-- A vanishing actual shell deviation, fed through reconstruction and the normal
deviation identity, forces equal channel covariances and therefore an `O(d)` orbit. -/
theorem orthoOrbit_of_actualDeviation_eq_zero
    {m d : ℕ} (hm : 3 ≤ m) (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hk : 0 ≤ k) (hV : gram V = simplexGram m)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hkt : k ^ 2 + t ^ 2 = 1)
    (X : Config m d)
    (hrecX : shellCovariance m (procrustesSq (normalConfig k t V z) V)
        (actualDeviation X (procrustesSq (normalConfig k t V z) V)) = channelCovariance X)
    (hrecN : shellCovariance m (procrustesSq (normalConfig k t V z) V)
        (actualDeviation (normalConfig k t V z)
          (procrustesSq (normalConfig k t V z) V)) =
      channelCovariance (normalConfig k t V z))
    (hD : actualDeviation X (procrustesSq (normalConfig k t V z) V) = 0) :
    orthoOrbit X (normalConfig k t V z) := by
  have hDN : actualDeviation (normalConfig k t V z)
      (procrustesSq (normalConfig k t V z) V) = 0 :=
    actualDeviation_normalConfig hm k t V z hk hV hperp hz hkt
  have hm1 : 1 < m := by omega
  have hcov : channelCovariance X = channelCovariance (normalConfig k t V z) := by
    rw [← hrecX, ← hrecN, hD, hDN]
  exact (orthoOrbit_iff_channelCovariance hm1 X (normalConfig k t V z)).mpr hcov

/-- `actualDeviation` depends on the configuration only through its Gram matrix. -/
theorem actualDeviation_eq_of_gram_eq
    {m d : ℕ} (tau : ℝ) {X Y : Config m d} (h : gram X = gram Y) :
    actualDeviation X tau = actualDeviation Y tau := by
  unfold actualDeviation centeredRoot centeredGram
  rw [h]

/-- Gram invariance sends an orthogonal image of the normal configuration to the
same actual deviation, which is zero. -/
theorem actualDeviation_eq_zero_of_orthoOrbit
    {m d : ℕ} (hm : 3 ≤ m) (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hk : 0 ≤ k) (hV : gram V = simplexGram m)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hkt : k ^ 2 + t ^ 2 = 1)
    {X : Config m d} (horbit : orthoOrbit X (normalConfig k t V z)) :
    actualDeviation X (procrustesSq (normalConfig k t V z) V) = 0 := by
  have hgram : gram (normalConfig k t V z) = gram X := gram_orthoOrbit horbit
  rw [actualDeviation_eq_of_gram_eq _ hgram.symm]
  exact actualDeviation_normalConfig hm k t V z hk hV hperp hz hkt

/-- Zero actual deviation if and only if the configuration is on the normal orbit. -/
theorem actualDeviation_eq_zero_iff_orthoOrbit
    {m d : ℕ} (hm : 3 ≤ m) (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hk : 0 ≤ k) (hV : gram V = simplexGram m)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hkt : k ^ 2 + t ^ 2 = 1)
    (X : Config m d)
    (hrecX : shellCovariance m (procrustesSq (normalConfig k t V z) V)
        (actualDeviation X (procrustesSq (normalConfig k t V z) V)) = channelCovariance X)
    (hrecN : shellCovariance m (procrustesSq (normalConfig k t V z) V)
        (actualDeviation (normalConfig k t V z)
          (procrustesSq (normalConfig k t V z) V)) =
      channelCovariance (normalConfig k t V z)) :
    actualDeviation X (procrustesSq (normalConfig k t V z) V) = 0 ↔
      orthoOrbit X (normalConfig k t V z) := by
  constructor
  · intro hD
    exact orthoOrbit_of_actualDeviation_eq_zero hm k t V z hk hV hperp hz hkt X
      hrecX hrecN hD
  · intro horbit
    exact actualDeviation_eq_zero_of_orthoOrbit hm k t V z hk hV hperp hz hkt horbit

/-- Orthogonal motion preserves `configPc` because it preserves the Gram matrix. -/
theorem configPc_eq_of_orthoOrbit
    {m d : ℕ} [NeZero m] (lam : ℝ) {X Y : Config m d} (horbit : orthoOrbit X Y) :
    configPc X lam = configPc Y lam := by
  unfold configPc
  exact congrArg (fun R => SimplexFull.decodingSuccess R lam) (gram_orthoOrbit horbit).symm

/-- On a sufficiently small positive Procrustes sphere, the strict normal configuration
maximizes `configPc`. Equality holds exactly on its `O(d)` orbit.

`c` is the point Hessian coercivity of `shellLoss (muFromSNR m lam)` at the origin.
The radius is the minimum of the quadratic-minimum radii, the actual-shell radius,
the local decoding-probability radius, and `√(2m)`. -/
theorem normalShell_maximizes_configPc
    {m d : ℕ} [NeZero m] {lam c : ℝ} (hm : 3 ≤ m) (hlam : 0 < lam)
    (V : Config m d) (z : EuclideanSpace ℝ (Fin d))
    (hV : gram V = simplexGram m) (hz : ‖z‖ = 1) (hperp : ∀ i, inner ℝ (V i) z = 0)
    (hc : 0 < c)
    (hcoer : ∀ H : shellSpace m, c * ‖H‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (shellLoss (m := m) (muFromSNR m lam))) (0, 0) (0, H) (0, H)) :
    ∃ rho0 > 0, ∀ rho : ℝ, 0 < rho → rho < rho0 →
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
  obtain ⟨deltaPc, hdeltaPc, hPc⟩ :=
    exists_local_extendedLoss_configPc hm1 V hV lam
  obtain ⟨deltaS, hdeltaS, hShell⟩ := exists_actualShell hm V hV
  have h2m : 0 < 2 * (m : ℝ) := mul_pos two_pos (Nat.cast_pos.mpr hmpos)
  refine ⟨min (Real.sqrt epsQ)
      (min deltaQ (min (Real.sqrt deltaS)
        (min (Real.sqrt deltaPc) (Real.sqrt (2 * (m : ℝ)))))), ?_, ?_⟩
  · exact lt_min (Real.sqrt_pos.mpr hepsQ)
      (lt_min hdeltaQ (lt_min (Real.sqrt_pos.mpr hdeltaS)
        (lt_min (Real.sqrt_pos.mpr hdeltaPc) (Real.sqrt_pos.mpr h2m))))
  · intro rho hρ0 hρlt X hX hdist
    have hρ_eps : rho < Real.sqrt epsQ := lt_of_lt_of_le hρlt (min_le_left _ _)
    have hρ_tail : rho < min deltaQ (min (Real.sqrt deltaS)
        (min (Real.sqrt deltaPc) (Real.sqrt (2 * (m : ℝ))))) :=
      lt_of_lt_of_le hρlt (min_le_right _ _)
    have hρ_dQ : rho < deltaQ := lt_of_lt_of_le hρ_tail (min_le_left _ _)
    have hρ_tail2 : rho < min (Real.sqrt deltaS)
        (min (Real.sqrt deltaPc) (Real.sqrt (2 * (m : ℝ)))) :=
      lt_of_lt_of_le hρ_tail (min_le_right _ _)
    have hρ_dS : rho < Real.sqrt deltaS := lt_of_lt_of_le hρ_tail2 (min_le_left _ _)
    have hρ_tail3 : rho < min (Real.sqrt deltaPc) (Real.sqrt (2 * (m : ℝ))) :=
      lt_of_lt_of_le hρ_tail2 (min_le_right _ _)
    have hρ_dPc : rho < Real.sqrt deltaPc := lt_of_lt_of_le hρ_tail3 (min_le_left _ _)
    have hρ_2m : rho < Real.sqrt (2 * (m : ℝ)) := lt_of_lt_of_le hρ_tail3 (min_le_right _ _)
    have hτ_eps : rho ^ 2 < epsQ := (Real.lt_sqrt hρ0.le).mp hρ_eps
    have hτ_dS : rho ^ 2 < deltaS := (Real.lt_sqrt hρ0.le).mp hρ_dS
    have hτ_dPc : rho ^ 2 < deltaPc := (Real.lt_sqrt hρ0.le).mp hρ_dPc
    have hτ_abs : |rho ^ 2| < epsQ := by rwa [abs_of_nonneg (sq_nonneg rho)]
    have hVunit : UnitConfig V := unitConfig_of_simplexGram V hm1 hV
    have hsum : ∑ i, V i = 0 := config_barycenter_of_simplexGram V hm0 hV
    obtain ⟨hk, hkt⟩ := shellShift_sq rho hmpos hρ0 hρ_2m
    set N : Config m d := normalConfig (shellKappa m rho) (shellShift m rho) V z with hNeq
    obtain ⟨hNunit, _, hNdist⟩ :=
      normalShell_geometry rho V z hm hVunit hsum hperp hz hρ0 hρ_2m
    obtain ⟨hmemX, _, hcovX, _, hnormX⟩ := hShell X (rho ^ 2) hX hdist hτ_dS
    obtain ⟨_, _, hcovN, _, _⟩ := hShell N (rho ^ 2) hNunit hNdist hτ_dS
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
    have hpcX := hPc X (by rwa [hdist])
    have hpcN := hPc N (by rwa [hNdist])
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

/-- Existence of the unit normal supplied by `exists_unit_normal_of_simplexGram`. -/
theorem exists_normalShell_maximizes_configPc
    {m d : ℕ} [NeZero m] {lam c : ℝ} (hm : 3 ≤ m) (hd : m ≤ d) (hlam : 0 < lam)
    (V : Config m d) (hV : gram V = simplexGram m) (hc : 0 < c)
    (hcoer : ∀ H : shellSpace m, c * ‖H‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (shellLoss (m := m) (muFromSNR m lam))) (0, 0) (0, H) (0, H)) :
    ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 ∧ (∀ i, inner ℝ (V i) z = 0) ∧
      ∃ rho0 > 0, ∀ rho : ℝ, 0 < rho → rho < rho0 →
        ∀ X : Config m d, UnitConfig X → procrustesSq X V = rho ^ 2 →
          configPc X lam ≤
            configPc (normalConfig (shellKappa m rho) (shellShift m rho) V z) lam ∧
          (configPc X lam =
              configPc (normalConfig (shellKappa m rho) (shellShift m rho) V z) lam ↔
            orthoOrbit X (normalConfig (shellKappa m rho) (shellShift m rho) V z)) := by
  obtain ⟨z, hz, hperp⟩ := exists_unit_normal_of_simplexGram V hm hd hV
  obtain ⟨rho0, hrho0, hrho⟩ :=
    normalShell_maximizes_configPc hm hlam V z hV hz hperp hc hcoer
  exact ⟨z, hz, hperp, rho0, hrho0, hrho⟩

#print axioms orthoOrbit_of_actualDeviation_eq_zero
#print axioms actualDeviation_eq_of_gram_eq
#print axioms actualDeviation_eq_zero_of_orthoOrbit
#print axioms actualDeviation_eq_zero_iff_orthoOrbit
#print axioms configPc_eq_of_orthoOrbit
#print axioms normalShell_maximizes_configPc
#print axioms exists_normalShell_maximizes_configPc

end SimplexFull.Geometry
