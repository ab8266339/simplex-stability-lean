import SimplexFull.ActualShell
noncomputable section
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

lemma gram_entry_bound_of_unit {m d : ℕ} (V X : Config m d)
    (hV : UnitConfig V) (hX : UnitConfig X) {eta : ℝ}
    (hclose : ∀ i, ‖X i - V i‖ ≤ eta) (i j : Fin m) :
    |(gram X - gram V) i j| ≤ 2*eta := by
  have he : (gram X - gram V) i j =
      inner ℝ (X i-V i) (X j) + inner ℝ (V i) (X j-V j) := by
    simp only [Matrix.sub_apply, gram_apply, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ (X i-V i) (X j)| + |inner ℝ (V i) (X j-V j)| := abs_add_le _ _
    _ ≤ ‖X i-V i‖*‖X j‖ + ‖V i‖*‖X j-V j‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ 2*eta := by rw [hX j, hV i]; nlinarith [hclose i, hclose j]

lemma gram_frob_bound_of_unit {m d : ℕ} (V X : Config m d)
    (hV : UnitConfig V) (hX : UnitConfig X) {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ∀ i, ‖X i - V i‖ ≤ eta) :
    frobSq (gram X-gram V) ≤ (m:ℝ)^2*(2*eta)^2 := by
  have he (i j : Fin m) : ((gram X-gram V) i j)^2 ≤ (2*eta)^2 := by
    have hh := gram_entry_bound_of_unit V X hV hX hclose i j
    have hh2 := mul_self_le_mul_self (abs_nonneg ((gram X-gram V) i j)) hh
    simpa only [← pow_two, sq_abs] using hh2
  calc
    frobSq (gram X-gram V) ≤ ∑ i : Fin m, ∑ j : Fin m, (2*eta)^2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
    _ = (m:ℝ)^2*(2*eta)^2 := by simp; ring


theorem exists_uniform_gram_radius (m : ℕ) (hm : 3 ≤ m) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ d (V X : Config m d), UnitConfig V → UnitConfig X →
      procrustesSq X V < delta → ‖gram X-gram V‖ < eps := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
  let eta : ℝ := eps/(4*(m:ℝ))
  have heta : 0 < eta := div_pos heps (by positivity)
  refine ⟨eta^2, sq_pos_of_pos heta, ?_⟩
  intro d V X hV hX hclose
  obtain ⟨r, ⟨U,rfl⟩, hU⟩ := exists_lt_of_csInf_lt
    (procrustesEnergy_range_nonempty X V) hclose
  have hn := aligned_norm_lt_of_energy_lt X V U heta hU
  have hp : ∀ i, ‖act U.symm X i-V i‖ ≤ eta := by
    intro i
    exact ((pi_norm_lt_iff heta).mp hn i).le
  have hUX : UnitConfig (act U.symm X) := by
    intro i
    change ‖U.symm (X i)‖=1
    rw [U.symm.norm_map, hX i]
  have hf := gram_frob_bound_of_unit V (act U.symm X) hV hUX heta.le hp
  rw [gram_act] at hf
  have he : (m:ℝ)^2*(2*eta)^2=eps^2/4 := by
    dsimp [eta]
    field_simp
    ring
  rw [he] at hf
  have hop := l2_opNorm_sq_le_frobSq (gram X-gram V)
  nlinarith [norm_nonneg (gram X-gram V), sq_pos_of_pos heps]
#print axioms exists_uniform_gram_radius
end SimplexFull.Geometry