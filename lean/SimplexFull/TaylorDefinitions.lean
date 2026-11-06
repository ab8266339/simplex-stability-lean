import SimplexFull.NormalShellValue
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]
def simplexSuccess (m : ℕ) [NeZero m] (lam : ℝ) : ℝ :=
  SimplexFull.decodingSuccess (simplexGram m) lam
def normalDeficit (m : ℕ) [NeZero m] (lam rho : ℝ) : ℝ :=
  simplexSuccess m lam-simplexSuccess m (lam*shellKappa m rho)
def normalTaylorPolynomial (m : ℕ) [NeZero m] (lam rho : ℝ) : ℝ :=
  lam*deriv (simplexSuccess m) lam/(2*(m:ℝ))*rho^2-
  lam^2*deriv (deriv (simplexSuccess m)) lam/(8*(m:ℝ)^2)*rho^4
def normalTaylorRemainder (m : ℕ) [NeZero m] (lam rho : ℝ) : ℝ :=
  normalDeficit m lam rho-normalTaylorPolynomial m lam rho
lemma configPc_eq_simplexSuccess {d : ℕ} (V : Config m d) (hV : gram V=simplexGram m) (lam : ℝ) :
    configPc V lam=simplexSuccess m lam := by
  simp only [configPc,simplexSuccess,hV]
lemma normalDeficit_neg (lam rho : ℝ) : normalDeficit m lam (-rho)=normalDeficit m lam rho := by
  simp only [normalDeficit,shellKappa,neg_sq]
lemma normalTaylorPolynomial_neg (lam rho : ℝ) :
    normalTaylorPolynomial m lam (-rho)=normalTaylorPolynomial m lam rho := by
  unfold normalTaylorPolynomial
  ring
lemma normalTaylorRemainder_neg (lam rho : ℝ) :
    normalTaylorRemainder m lam (-rho)=normalTaylorRemainder m lam rho := by
  simp only [normalTaylorRemainder,normalDeficit_neg,normalTaylorPolynomial_neg]
lemma normalDeficit_zero (lam : ℝ) : normalDeficit m lam 0=0 := by
  simp [normalDeficit,shellKappa]
#print axioms normalDeficit_neg
end SimplexFull.Geometry

