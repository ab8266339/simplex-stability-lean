import SimplexFull.EvenTaylor
import SimplexFull.SignalSmooth
import SimplexFull.TaylorShell
import SimplexFull.TaylorParity
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]
lemma simplexSuccess_contDiff (hm : 3 ≤ m) : ContDiff ℝ 3 (simplexSuccess m) := by
  unfold simplexSuccess
  exact SimplexFull.contDiff_simplexSuccess hm
/-- Concrete sixth-order remainder, with constants depending only on m and lambda. -/
theorem normalTaylor_bound (hm : 3 ≤ m) (lam : ℝ) :
    ∃ C > 0, ∃ r > 0, ∀ rho : ℝ, |rho|<r →
      |normalTaylorRemainder m lam rho| ≤ C*|rho|^6 := by
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  simpa only [normalTaylorRemainder,normalDeficit,normalTaylorPolynomial,shellKappa] using
    (SimplexFull.Taylor.evenTaylor_bound (p:=simplexSuccess m) (lam:=lam) (m:=(m:ℝ))
      hmR (simplexSuccess_contDiff hm).contDiffAt)
/-- The manuscript's exact p-prime/p-double-prime polynomial has O(rho^6) error. -/
theorem normalTaylor_isBigO (hm : 3 ≤ m) (lam : ℝ) :
    (normalTaylorRemainder m lam) =O[𝓝 (0:ℝ)] (fun rho : ℝ => rho^6) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  unfold normalTaylorRemainder normalDeficit normalTaylorPolynomial shellKappa
  exact (SimplexFull.Taylor.evenTaylor_isBigO (p:=simplexSuccess m) (lam:=lam) (m:=(m:ℝ))
      hmR (simplexSuccess_contDiff hm).contDiffAt)
theorem gaussian_uniform_taylor_shell_m4 {lam : ℝ} (hm : 4 ≤ m) (hlam : 0 < lam)
    (hgap : (m:ℝ)/2 < a m (muFromSNR m lam)) : UniformTaylorNormalShell m lam :=
  uniformTaylorNormalShell_of_bound (gaussian_uniform_exact_normal_shell_m4 hm hlam hgap)
    (normalTaylor_bound (by omega) lam)
theorem gaussian_uniform_taylor_shell_m3 {lam : ℝ} (hlam : 0 < lam)
    (hgap : 2 < a 3 (muFromSNR 3 lam)+b 3 (muFromSNR 3 lam)) : UniformTaylorNormalShell 3 lam :=
  uniformTaylorNormalShell_of_bound (gaussian_uniform_exact_normal_shell_m3 hlam hgap)
    (normalTaylor_bound (by decide) lam)
#print axioms normalTaylor_bound
#print axioms normalTaylor_isBigO
#print axioms gaussian_uniform_taylor_shell_m4
#print axioms gaussian_uniform_taylor_shell_m3
theorem gaussian_threshold_uniform_taylor_shell_m4 (m : ℕ) [NeZero m] (hm : 4 ≤ m) :
    ∃ t0 > 0, a m t0=(m:ℝ)/2 ∧
      (∀ s : ℝ, 0 ≤ s → a m s=(m:ℝ)/2 → s=t0) ∧
      ∀ lam : ℝ, 0 < lam → t0 < muFromSNR m lam → UniformTaylorNormalShell m lam := by
  obtain ⟨t0,ht0,he,hu,hopt⟩ := gaussian_normal_threshold_uniform_shell_m4 m hm
  refine ⟨t0,ht0,he,hu,?_⟩
  intro lam hlam hmu
  exact uniformTaylorNormalShell_of_bound (hopt lam hlam hmu) (normalTaylor_bound (by omega) lam)
theorem gaussian_threshold_uniform_taylor_shell_m3 :
    ∃ t0 > 0, a 3 t0+b 3 t0=2 ∧
      (∀ s : ℝ, 0 ≤ s → a 3 s+b 3 s=2 → s=t0) ∧
      ∀ lam : ℝ, 0 < lam → t0 < muFromSNR 3 lam → UniformTaylorNormalShell 3 lam := by
  obtain ⟨t0,ht0,he,hu,hopt⟩ := gaussian_normal_threshold_uniform_shell_m3
  refine ⟨t0,ht0,he,hu,?_⟩
  intro lam hlam hmu
  exact uniformTaylorNormalShell_of_bound (hopt lam hlam hmu) (normalTaylor_bound (by decide) lam)
#print axioms gaussian_threshold_uniform_taylor_shell_m4
#print axioms gaussian_threshold_uniform_taylor_shell_m3
end SimplexFull.Geometry


