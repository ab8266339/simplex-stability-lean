import SimplexFull.GeometryBase
import SimplexFull.Procrustes
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Strict-normal shell geometry over the compiled Procrustes distance.

`procrustesSq` is the infimum of `‖X - U ∘ V‖²` over `U : OrthogonalMotion d`.
For `X = normalConfig k t V z`, that infimum equals `2 m (1 - k)` by a direct
Cauchy estimate: the common normal cancels against `∑ V = 0`, and the identity
isometry attains the bound.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace SimplexFull.Geometry

theorem procrustesEnergy_normalConfig {m d : Nat} (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hV : UnitConfig V) (hsum : ∑ i, V i = 0)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hkt : k ^ 2 + t ^ 2 = 1)
    (U : OrthogonalMotion d) :
    procrustesEnergy (normalConfig k t V z) V U =
      2 * (m : ℝ) - 2 * k * ∑ i, inner ℝ (V i) (U (V i)) := by
  have hX : UnitConfig (normalConfig k t V z) :=
    unitConfig_normalConfig k t V z hV hperp hz hkt
  have hcross : ∑ i, inner ℝ z (U (V i)) = 0 := by
    have hflip : ∀ i, inner ℝ z (U (V i)) = inner ℝ (V i) (U.symm z) := by
      intro i
      rw [real_inner_comm, LinearIsometryEquiv.inner_map_eq_flip]
    simp_rw [hflip, ← sum_inner Finset.univ V (U.symm z), hsum, inner_zero_left]
  have hI : ∀ i, ‖normalConfig k t V z i - U (V i)‖ ^ 2 =
      2 - 2 * k * inner ℝ (V i) (U (V i)) - 2 * t * inner ℝ z (U (V i)) := by
    intro i
    rw [norm_sub_sq_real, hX i, LinearIsometryEquiv.norm_map, hV i, normalConfig,
      inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  simp only [procrustesEnergy]
  simp_rw [hI]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hconst : ∑ i : Fin m, (2 : ℝ) = 2 * (m : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  have hksum : ∑ i, 2 * k * inner ℝ (V i) (U (V i)) =
      2 * k * ∑ i, inner ℝ (V i) (U (V i)) := by
    rw [← Finset.mul_sum]
  have htsum : ∑ i, 2 * t * inner ℝ z (U (V i)) =
      2 * t * ∑ i, inner ℝ z (U (V i)) := by
    rw [← Finset.mul_sum]
  rw [hconst, hksum, htsum, hcross]
  ring

theorem procrustesEnergy_normalConfig_ge {m d : Nat} (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hV : UnitConfig V) (hsum : ∑ i, V i = 0)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hk : 0 ≤ k)
    (hkt : k ^ 2 + t ^ 2 = 1) (U : OrthogonalMotion d) :
    2 * (m : ℝ) * (1 - k) ≤ procrustesEnergy (normalConfig k t V z) V U := by
  rw [procrustesEnergy_normalConfig k t V z hV hsum hperp hz hkt U]
  have hle : ∀ i, inner ℝ (V i) (U (V i)) ≤ 1 := by
    intro i
    calc
      inner ℝ (V i) (U (V i)) ≤ ‖V i‖ * ‖U (V i)‖ := real_inner_le_norm _ _
      _ = ‖V i‖ * ‖V i‖ := by rw [LinearIsometryEquiv.norm_map]
      _ = 1 := by rw [hV i, one_mul]
  have hS : ∑ i, inner ℝ (V i) (U (V i)) ≤ (m : ℝ) := by
    have hsum1 : ∑ i, inner ℝ (V i) (U (V i)) ≤ ∑ i : Fin m, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hle i
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hsum1
  have hmul : 2 * k * ∑ i, inner ℝ (V i) (U (V i)) ≤ 2 * k * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hS (mul_nonneg zero_le_two hk)
  linarith

theorem procrustesEnergy_normalConfig_refl {m d : Nat} (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hV : UnitConfig V) (hsum : ∑ i, V i = 0)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hkt : k ^ 2 + t ^ 2 = 1) :
    procrustesEnergy (normalConfig k t V z) V (LinearIsometryEquiv.refl ℝ _) =
      2 * (m : ℝ) * (1 - k) := by
  rw [procrustesEnergy_normalConfig k t V z hV hsum hperp hz hkt]
  have hself :
      ∑ i, inner ℝ (V i) ((LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) (V i)) =
        ∑ i : Fin m, (1 : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearIsometryEquiv.coe_refl]
    change inner ℝ (V i) (V i) = 1
    rw [real_inner_self_eq_norm_sq, hV i, one_pow]
  rw [hself]
  have hcard : ∑ i : Fin m, (1 : ℝ) = (m : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hcard]
  ring

theorem procrustesSq_normalConfig {m d : Nat} (k t : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hV : UnitConfig V) (hsum : ∑ i, V i = 0)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hk : 0 ≤ k)
    (hkt : k ^ 2 + t ^ 2 = 1) :
    procrustesSq (normalConfig k t V z) V = 2 * (m : ℝ) * (1 - k) := by
  apply le_antisymm
  · calc
      procrustesSq (normalConfig k t V z) V ≤
          procrustesEnergy (normalConfig k t V z) V (LinearIsometryEquiv.refl ℝ _) :=
        procrustesSq_le_energy _ _ _
      _ = 2 * (m : ℝ) * (1 - k) :=
        procrustesEnergy_normalConfig_refl k t V z hV hsum hperp hz hkt
  · apply le_csInf (procrustesEnergy_range_nonempty _ _)
    rintro r ⟨U, rfl⟩
    exact procrustesEnergy_normalConfig_ge k t V z hV hsum hperp hz hk hkt U

/-- In-plane coefficient on the sphere of Procrustes radius `rho`. -/
def shellKappa (m : Nat) (rho : ℝ) : ℝ :=
  1 - rho ^ 2 / (2 * (m : ℝ))

/-- Common normal coefficient `√(1 - k²)` for `k = shellKappa m rho`. -/
def shellShift (m : Nat) (rho : ℝ) : ℝ :=
  Real.sqrt (1 - shellKappa m rho ^ 2)

theorem shellKappa_mem_Ioo {m : Nat} (rho : ℝ) (hm : 0 < m) (hρ0 : 0 < rho)
    (hρ : rho < Real.sqrt (2 * (m : ℝ))) :
    0 < shellKappa m rho ∧ shellKappa m rho < 1 := by
  have hsq : rho ^ 2 < 2 * (m : ℝ) := (Real.lt_sqrt hρ0.le).mp hρ
  have hposden : 0 < 2 * (m : ℝ) := by positivity
  have hfrac_pos : 0 < rho ^ 2 / (2 * (m : ℝ)) := by positivity
  have hfrac_lt : rho ^ 2 / (2 * (m : ℝ)) < 1 := by
    rwa [div_lt_one hposden]
  unfold shellKappa
  constructor <;> linarith

theorem shellShift_sq {m : Nat} (rho : ℝ) (hm : 0 < m) (hρ0 : 0 < rho)
    (hρ : rho < Real.sqrt (2 * (m : ℝ))) :
    0 ≤ shellKappa m rho ∧ shellKappa m rho ^ 2 + shellShift m rho ^ 2 = 1 := by
  obtain ⟨hk0, hk1⟩ := shellKappa_mem_Ioo rho hm hρ0 hρ
  have hfac : 1 - shellKappa m rho ^ 2 =
      (1 - shellKappa m rho) * (1 + shellKappa m rho) := by ring
  have hnn : 0 ≤ 1 - shellKappa m rho ^ 2 := by
    rw [hfac]
    exact mul_nonneg (by linarith) (by linarith)
  refine ⟨hk0.le, ?_⟩
  unfold shellShift
  rw [Real.sq_sqrt hnn]
  ring

theorem shell_radius_eq (m : Nat) (rho : ℝ) (hm : m ≠ 0) :
    2 * (m : ℝ) * (1 - shellKappa m rho) = rho ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have h2 : 2 * (m : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hmR
  unfold shellKappa
  calc
    2 * (m : ℝ) * (1 - (1 - rho ^ 2 / (2 * (m : ℝ)))) =
        2 * (m : ℝ) * (rho ^ 2 / (2 * (m : ℝ))) := by ring
    _ = rho ^ 2 := by rw [mul_div_cancel₀ _ h2]

theorem unitConfig_of_simplexGram {m d : Nat} (V : Config m d) (hm : 1 < m)
    (hG : gram V = simplexGram m) : UnitConfig V := by
  intro i
  have hii : ‖V i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, ← gram_apply, hG, simplexGram_diagonal m hm i]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [one_pow] using hii)

theorem not_linearIndependent_simplexGram {m d : Nat} (V : Config m d) (hm : m ≠ 0)
    (hG : gram V = simplexGram m) : ¬ LinearIndependent ℝ V := by
  rw [Fintype.not_linearIndependent_iffₛ]
  have hsum := config_barycenter_of_simplexGram V hm hG
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  refine ⟨fun _ => 1, fun _ => 0, ?_, ⟨⟨0, hm0⟩, one_ne_zero⟩⟩
  simp only [one_smul, zero_smul, Finset.sum_const_zero]
  exact hsum

/-- A simplex Gram in ambient dimension `d ≥ m ≥ 3` leaves a unit normal direction. -/
theorem exists_unit_normal_of_simplexGram {m d : Nat} (V : Config m d) (hm : 3 ≤ m)
    (hd : m ≤ d) (hG : gram V = simplexGram m) :
    ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 ∧ ∀ i, inner ℝ (V i) z = 0 := by
  have hm0 : m ≠ 0 := (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hm).ne'
  have hdep := not_linearIndependent_simplexGram V hm0 hG
  have hrank : (Set.range V).finrank ℝ < m := by
    rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin] at hdep
    exact lt_of_not_ge hdep
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ (Set.range V)
  have hK : Module.finrank ℝ K < d := by
    have hKm : Module.finrank ℝ K < m := by
      simpa [K, Set.finrank] using hrank
    exact lt_of_lt_of_le hKm hd
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have horth : 0 < Module.finrank ℝ Kᗮ := by
    have hadd := Submodule.finrank_add_finrank_orthogonal K
    rw [hE] at hadd
    have hne : Module.finrank ℝ Kᗮ ≠ 0 := by
      intro hz
      rw [hz, add_zero] at hadd
      exact (Nat.ne_of_lt hK) hadd
    exact Nat.pos_of_ne_zero hne
  obtain ⟨w, hw⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := Kᗮ)).mp horth
  set u : EuclideanSpace ℝ (Fin d) := ↑w
  have hu : u ≠ 0 := by
    intro h
    exact hw (Subtype.ext h)
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)
  · intro i
    have hVi : V i ∈ K := Submodule.subset_span (Set.mem_range_self i)
    have hzu : ‖u‖⁻¹ • u ∈ Kᗮ := Submodule.smul_mem _ _ w.property
    exact Submodule.inner_right_of_mem_orthogonal hVi hzu

theorem normalShell_geometry {m d : Nat} (rho : ℝ) (V : Config m d)
    (z : EuclideanSpace ℝ (Fin d)) (hm : 3 ≤ m) (hV : UnitConfig V) (hsum : ∑ i, V i = 0)
    (hperp : ∀ i, inner ℝ (V i) z = 0) (hz : ‖z‖ = 1) (hρ0 : 0 < rho)
    (hρ : rho < Real.sqrt (2 * (m : ℝ))) :
    UnitConfig (normalConfig (shellKappa m rho) (shellShift m rho) V z) ∧
      gram (normalConfig (shellKappa m rho) (shellShift m rho) V z) =
        (shellKappa m rho) ^ 2 • gram V + (shellShift m rho) ^ 2 • onesMatrix m ∧
      procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V = rho ^ 2 := by
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hm
  have hm0 : m ≠ 0 := hmpos.ne'
  obtain ⟨hk, hkt⟩ := shellShift_sq rho hmpos hρ0 hρ
  refine ⟨?_, ?_, ?_⟩
  · exact unitConfig_normalConfig _ _ V z hV hperp hz hkt
  · exact gram_normalConfig _ _ V z hperp hz
  · rw [procrustesSq_normalConfig _ _ V z hV hsum hperp hz hk hkt, shell_radius_eq m rho hm0]

theorem exists_normalShell {m d : Nat} (rho : ℝ) (V : Config m d) (hm : 3 ≤ m) (hd : m ≤ d)
    (hG : gram V = simplexGram m) (hρ0 : 0 < rho) (hρ : rho < Real.sqrt (2 * (m : ℝ))) :
    ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 ∧ (∀ i, inner ℝ (V i) z = 0) ∧
      UnitConfig (normalConfig (shellKappa m rho) (shellShift m rho) V z) ∧
      gram (normalConfig (shellKappa m rho) (shellShift m rho) V z) =
        (shellKappa m rho) ^ 2 • simplexGram m + (shellShift m rho) ^ 2 • onesMatrix m ∧
      procrustesSq (normalConfig (shellKappa m rho) (shellShift m rho) V z) V = rho ^ 2 := by
  obtain ⟨z, hz, hperp⟩ := exists_unit_normal_of_simplexGram V hm hd hG
  have hm1 : 1 < m := Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_of_succ_le hm)
  have hm0 : m ≠ 0 := (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hm).ne'
  have hV := unitConfig_of_simplexGram V hm1 hG
  have hsum := config_barycenter_of_simplexGram V hm0 hG
  obtain ⟨hunit, hgram, hdist⟩ := normalShell_geometry rho V z hm hV hsum hperp hz hρ0 hρ
  refine ⟨z, hz, hperp, hunit, ?_, hdist⟩
  rw [hgram, hG]

#print axioms procrustesEnergy_normalConfig
#print axioms procrustesEnergy_normalConfig_ge
#print axioms procrustesEnergy_normalConfig_refl
#print axioms procrustesSq_normalConfig
#print axioms shellKappa_mem_Ioo
#print axioms shellShift_sq
#print axioms shell_radius_eq
#print axioms unitConfig_of_simplexGram
#print axioms not_linearIndependent_simplexGram
#print axioms exists_unit_normal_of_simplexGram
#print axioms normalShell_geometry
#print axioms exists_normalShell

end SimplexFull.Geometry
