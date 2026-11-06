import SimplexFull.GeometryBase
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
namespace SimplexFull.Geometry

abbrev OrthogonalMotion (d : ℕ) :=
  EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)

def procrustesEnergy {m d : ℕ} (X V : Config m d) (U : OrthogonalMotion d) : ℝ :=
  ∑ i, ‖X i - U (V i)‖ ^ 2

def procrustesSq {m d : ℕ} (X V : Config m d) : ℝ :=
  sInf (Set.range (procrustesEnergy X V))

theorem procrustesEnergy_nonneg {m d : ℕ} (X V : Config m d) (U : OrthogonalMotion d) :
    0 ≤ procrustesEnergy X V U :=
  Finset.sum_nonneg fun i _ => sq_nonneg ‖X i - U (V i)‖

theorem procrustesEnergy_range_nonempty {m d : ℕ} (X V : Config m d) :
    (Set.range (procrustesEnergy X V)).Nonempty :=
  ⟨_, ⟨LinearIsometryEquiv.refl ℝ _, rfl⟩⟩

theorem procrustesEnergy_bddBelow {m d : ℕ} (X V : Config m d) :
    BddBelow (Set.range (procrustesEnergy X V)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨U, rfl⟩
  exact procrustesEnergy_nonneg X V U

theorem procrustesSq_nonneg {m d : ℕ} (X V : Config m d) :
    0 ≤ procrustesSq X V := by
  apply le_csInf (procrustesEnergy_range_nonempty X V)
  rintro r ⟨U, rfl⟩
  exact procrustesEnergy_nonneg X V U

theorem procrustesSq_le_energy {m d : ℕ} (X V : Config m d) (U : OrthogonalMotion d) :
    procrustesSq X V ≤ procrustesEnergy X V U :=
  csInf_le (procrustesEnergy_bddBelow X V) ⟨U, rfl⟩

theorem procrustesSq_eq_zero_of_alignment {m d : ℕ} (X V : Config m d)
    (U : OrthogonalMotion d) (h : ∀ i, X i = U (V i)) : procrustesSq X V = 0 := by
  apply le_antisymm _ (procrustesSq_nonneg X V)
  calc
    procrustesSq X V ≤ procrustesEnergy X V U := procrustesSq_le_energy X V U
    _ = 0 := by simp [procrustesEnergy, h]

theorem procrustesSq_self {m d : ℕ} (V : Config m d) : procrustesSq V V = 0 :=
  procrustesSq_eq_zero_of_alignment V V (LinearIsometryEquiv.refl ℝ _) (fun _ => rfl)

#print axioms procrustesSq_nonneg
#print axioms procrustesSq_le_energy
#print axioms procrustesSq_self
def synthesis {m d : ℕ} (X : Config m d) : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun a := ∑ i, a i • X i
  map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro c a; simp [Finset.smul_sum, mul_smul]

@[simp] theorem synthesis_apply {m d : ℕ} (X : Config m d) (a : Fin m → ℝ) :
    synthesis X a = ∑ i, a i • X i := rfl

@[simp] theorem synthesis_single {m d : ℕ} (X : Config m d) (i : Fin m) :
    synthesis X (Pi.single i 1) = X i := by
  simp [synthesis_apply, Pi.single_apply]

theorem synthesis_norm_eq_of_gram_eq {m d : ℕ} (X Y : Config m d)
    (h : gram X = gram Y) (a : Fin m → ℝ) : ‖synthesis X a‖ = ‖synthesis Y a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [synthesis_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  have hg : ∀ i j, inner ℝ (X i) (X j) = inner ℝ (Y i) (Y j) :=
    fun i j => congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M i j) h
  simp_rw [hg]

#print axioms synthesis_norm_eq_of_gram_eq
theorem exists_orthogonal_of_gram_eq {m d : ℕ} (X Y : Config m d)
    (h : gram X = gram Y) : ∃ U : OrthogonalMotion d, ∀ i, U (X i) = Y i := by
  let F := synthesis X
  let G := synthesis Y
  have hn : ∀ a, ‖F a‖ = ‖G a‖ := synthesis_norm_eq_of_gram_eq X Y h
  have hk : LinearMap.ker F ≤ LinearMap.ker G := by
    intro a ha
    change F a = 0 at ha
    change G a = 0
    apply norm_eq_zero.mp
    rw [← hn a, ha, norm_zero]
  let L : LinearMap.range F →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    ((LinearMap.ker F).liftQ G hk).comp F.quotKerEquivRange.symm.toLinearMap
  have hL (a : Fin m → ℝ) : L ⟨F a, LinearMap.mem_range_self F a⟩ = G a := by
    change (LinearMap.ker F).liftQ G hk
      (F.quotKerEquivRange.symm ⟨F a, LinearMap.mem_range_self F a⟩) = G a
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hLn : ∀ z : LinearMap.range F, ‖L z‖ = ‖z‖ := by
    rintro ⟨z, a, rfl⟩
    rw [hL]
    exact (hn a).symm
  let LI : LinearMap.range F →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    { toLinearMap := L, norm_map' := hLn }
  let U : OrthogonalMotion d := LI.extend.toLinearIsometryEquiv rfl
  refine ⟨U, ?_⟩
  intro i
  have hx : F (Pi.single i 1) = X i := synthesis_single X i
  have hy : G (Pi.single i 1) = Y i := synthesis_single Y i
  change LI.extend (X i) = Y i
  rw [← hx]
  exact (LI.extend_apply ⟨_, LinearMap.mem_range_self F _⟩).trans ((hL _).trans hy)

#print axioms exists_orthogonal_of_gram_eq
theorem orthoOrbit_iff_gram_eq {m d : ℕ} (X Y : Config m d) :
    orthoOrbit X Y ↔ gram X = gram Y := by
  constructor
  · intro h
    exact (gram_orthoOrbit h).symm
  · intro h
    obtain ⟨U, hU⟩ := exists_orthogonal_of_gram_eq X Y h
    exact ⟨U, fun i => (hU i).symm⟩

#print axioms orthoOrbit_iff_gram_eq
end SimplexFull.Geometry