import SimplexFull.NormalShellValue
import SimplexFull.GaussianShellHessian
import SimplexFull.GaussianShapeCoercivity
import SimplexFull.GaussianCrossings
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
open SimplexFull.Covariance
/-- Strict Gaussian normal regime: every sufficiently small actual Procrustes
shell has the exact scaled-SNR optimum, attained precisely on one O(d) orbit.
There are no abstract derivative, realization, or optimization hypotheses. -/
theorem gaussian_exact_normal_shell_m4 {m d : ℕ} [NeZero m] {lam : ℝ}
    (hm : 4 ≤ m) (hd : m ≤ d) (hlam : 0 < lam)
    (V : Config m d) (hV : gram V=simplexGram m)
    (hgap : (m:ℝ)/2 < a m (muFromSNR m lam)) : ExactNormalShell V lam := by
  have hmu : 0 < muFromSNR m lam := muFromSNR_pos (by omega) hlam
  obtain ⟨gamma,hgamma,hQ⟩ := gaussian_shell_coercive_m4 hm hmu hgap
  apply exactNormalShell_of_hessian (c:=2*gamma) (by omega) hd hlam V hV
    (mul_pos two_pos hgamma)
  intro H
  rw [gaussian_shell_hessian (by omega) hmu H]
  have hh := hQ H
  nlinarith
/-- The triangular case uses its sole irreducible curvature gap. -/
theorem gaussian_exact_normal_shell_m3 {d : ℕ} {lam : ℝ}
    (hd : 3 ≤ d) (hlam : 0 < lam) (V : Config 3 d) (hV : gram V=simplexGram 3)
    (hgap : 2 < a 3 (muFromSNR 3 lam)+b 3 (muFromSNR 3 lam)) :
    ExactNormalShell V lam := by
  have hmu : 0 < muFromSNR 3 lam := muFromSNR_pos (by decide) hlam
  obtain ⟨gamma,hgamma,hQ⟩ := gaussian_shell_coercive_m3 hmu hgap
  apply exactNormalShell_of_hessian (c:=2*gamma) (by decide) hd hlam V hV
    (mul_pos two_pos hgamma)
  intro H
  rw [gaussian_shell_hessian (by decide) hmu H]
  have hh := hQ H
  nlinarith
#print axioms gaussian_exact_normal_shell_m4
#print axioms gaussian_exact_normal_shell_m3
/-- The unique positive normal threshold controls the concrete optimal shell. -/
theorem gaussian_normal_threshold_exact_shell_m4 (m : ℕ) [NeZero m] (hm : 4 ≤ m) :
    ∃ t0 > 0, a m t0=(m:ℝ)/2 ∧
      (∀ s : ℝ, 0 ≤ s → a m s=(m:ℝ)/2 → s=t0) ∧
      ∀ (d : ℕ) (lam : ℝ), m ≤ d → 0 < lam →
        ∀ V : Config m d, gram V=simplexGram m →
          t0 < muFromSNR m lam → ExactNormalShell V lam := by
  obtain ⟨t1,t0,t01,h1,h10,h001,he1,he0,he01,hu1,hu0,hu01⟩ :=
    SimplexFull.gaussian_ordered_crossings m hm
  refine ⟨t0,lt_trans h1 h10,he0,?_,?_⟩
  · intro s hs he
    exact hu0 s hs he
  · intro d lam hd hlam V hV hmu
    apply gaussian_exact_normal_shell_m4 hm hd hlam V hV
    rw [← he0]
    exact (SimplexFull.strictMono_a m) hmu
/-- The triangular unique threshold controls its concrete optimal shell. -/
theorem gaussian_normal_threshold_exact_shell_m3 :
    ∃ t0 > 0, a 3 t0+b 3 t0=2 ∧
      (∀ s : ℝ, 0 ≤ s → a 3 s+b 3 s=2 → s=t0) ∧
      ∀ (d : ℕ) (lam : ℝ), 3 ≤ d → 0 < lam →
        ∀ V : Config 3 d, gram V=simplexGram 3 →
          t0 < muFromSNR 3 lam → ExactNormalShell V lam := by
  obtain ⟨t0,h0,he,hu,hlt,hgt⟩ := SimplexFull.gaussian_triangular_unique_crossing
  refine ⟨t0,h0,by linarith,?_,?_⟩
  · intro s hs heq
    exact hu s hs (by linarith)
  · intro d lam hd hlam V hV hmu
    apply gaussian_exact_normal_shell_m3 hd hlam V hV
    have hg := hgt (muFromSNR 3 lam) hmu
    linarith
#print axioms gaussian_normal_threshold_exact_shell_m4
#print axioms gaussian_normal_threshold_exact_shell_m3
end SimplexFull.Geometry
