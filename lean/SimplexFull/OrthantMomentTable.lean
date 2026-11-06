import SimplexFull.OrthantProduct
import SimplexFull.OrthantLimits

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SimplexFull.Covariance
variable {m : ℕ}

def normMoment (n : ℕ) (c : ℝ) := moment1D n c / Phi c
lemma normMoment_zero (c : ℝ) : normMoment 0 c = 1 := by
  unfold normMoment
  rw [moment1D_zero, div_self (Phi_pos c).ne']
lemma normMoment_one (c : ℝ) : normMoment 1 c = -q c := by
  simp only [normMoment, moment1D_one, q, neg_div]
lemma normMoment_two (c : ℝ) : normMoment 2 c = (q c)^2+sigma c := by
  unfold normMoment
  rw [moment1D_two]
  simp only [sigma, h, q]
  have hp := (Phi_pos c).ne'
  field_simp
  ring

theorem integral_orthant_monomial_normalized (alpha : Fin m → ℕ) (c : ℝ) :
    ∫ x in orthantIic c, rho 1 x*coordMonomial alpha x =
      Phi c^m*∏ i, normMoment (alpha i) c := by
  rw [integral_orthant_coordMonomial]
  simp only [normMoment, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp := (Phi_pos c).ne'
  field_simp

def singleCount (i : Fin m) (n : ℕ) (t : Fin m) : ℕ := if t=i then n else 0

lemma monomial_singleCount (i : Fin m) (n : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    coordMonomial (singleCount i n) x = (x i)^n := by
  classical
  unfold coordMonomial
  rw [Finset.prod_eq_single i]
  · simp [singleCount]
  · intro j _ hji
    simp [singleCount, hji]
  · simp

lemma prod_normMoment_singleCount (i : Fin m) (n : ℕ) (c : ℝ) :
    ∏ t, normMoment (singleCount i n t) c = normMoment n c := by
  classical
  rw [Finset.prod_eq_single i]
  · simp [singleCount]
  · intro j _ hji
    simp [singleCount, hji, normMoment_zero]
  · simp

lemma normMoment_add_disjoint {a b : ℕ} (hab : a=0 ∨ b=0) (c : ℝ) :
    normMoment (a+b) c = normMoment a c*normMoment b c := by
  rcases hab with rfl | rfl <;> simp [normMoment_zero]

lemma coordMonomial_add_counts (alpha beta : Fin m → ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    coordMonomial (fun t => alpha t+beta t) x = coordMonomial alpha x*coordMonomial beta x := by
  simp only [coordMonomial, pow_add, Finset.prod_mul_distrib]

lemma prod_normMoment_add_counts (alpha beta : Fin m → ℕ)
    (hh : ∀ t, alpha t=0 ∨ beta t=0) (c : ℝ) :
    (∏ t, normMoment (alpha t+beta t) c) =
      (∏ t, normMoment (alpha t) c)*(∏ t, normMoment (beta t) c) := by
  simp_rw [normMoment_add_disjoint (hh _), Finset.prod_mul_distrib]

lemma singleCount_disjoint {i j : Fin m} (hij : i ≠ j) (n k : ℕ) (t : Fin m) :
    singleCount i n t=0 ∨ singleCount j k t=0 := by
  by_cases hi : t=i
  · right
    simp [singleCount, hi, hij]
  · left
    simp [singleCount, hi]

theorem integral_orthant_pair_distinct_normalized (c : ℝ) {i j : Fin m} (hij : i ≠ j) :
    ∫ x in orthantIic c, rho 1 x*(x i*x j) = Phi c^m*(q c)^2 := by
  let alpha := fun t => singleCount i 1 t+singleCount j 1 t
  have he : ∀ x : EuclideanSpace ℝ (Fin m), coordMonomial alpha x = x i*x j := by
    intro x
    dsimp [alpha]
    rw [coordMonomial_add_counts, monomial_singleCount, monomial_singleCount]
    simp
  have ht := integral_orthant_monomial_normalized alpha c
  simp_rw [he] at ht
  rw [ht]
  dsimp [alpha]
  rw [prod_normMoment_add_counts _ _ (singleCount_disjoint hij 1 1),
    prod_normMoment_singleCount, prod_normMoment_singleCount, normMoment_one]
  ring

theorem integral_orthant_pair_same_normalized (c : ℝ) (i : Fin m) :
    ∫ x in orthantIic c, rho 1 x*(x i*x i) = Phi c^m*((q c)^2+sigma c) := by
  have ht := integral_orthant_monomial_normalized (singleCount i 2) c
  simp_rw [monomial_singleCount] at ht
  rw [prod_normMoment_singleCount, normMoment_two] at ht
  simpa [pow_two] using ht

theorem integral_orthant_twoPowers (c : ℝ) {i j : Fin m} (hij : i ≠ j) (a b : ℕ) :
    ∫ x in orthantIic c, rho 1 x*((x i)^a*(x j)^b) =
      Phi c^m*(normMoment a c*normMoment b c) := by
  have ht := integral_orthant_monomial_normalized (fun t => singleCount i a t+singleCount j b t) c
  simp_rw [coordMonomial_add_counts, monomial_singleCount] at ht
  rw [prod_normMoment_add_counts _ _ (singleCount_disjoint hij a b),
    prod_normMoment_singleCount, prod_normMoment_singleCount] at ht
  exact ht

lemma singleCount_sum_disjoint {i j k : Fin m} (hik : i ≠ k) (hjk : j ≠ k)
    (a b d : ℕ) (t : Fin m) :
    singleCount i a t+singleCount j b t=0 ∨ singleCount k d t=0 := by
  by_cases ht : t=k
  · left
    simp [singleCount, ht, hik.symm, hjk.symm]
  · right
    simp [singleCount, ht]

theorem integral_orthant_threePowers (c : ℝ) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b d : ℕ) :
    ∫ x in orthantIic c, rho 1 x*((x i)^a*(x j)^b*(x k)^d) =
      Phi c^m*(normMoment a c*normMoment b c*normMoment d c) := by
  have ht := integral_orthant_monomial_normalized
    (fun t => (singleCount i a t+singleCount j b t)+singleCount k d t) c
  simp_rw [coordMonomial_add_counts, monomial_singleCount] at ht
  rw [prod_normMoment_add_counts _ _ (singleCount_sum_disjoint hik hjk a b d),
    prod_normMoment_add_counts _ _ (singleCount_disjoint hij a b),
    prod_normMoment_singleCount, prod_normMoment_singleCount, prod_normMoment_singleCount] at ht
  exact ht

lemma singleCount_three_disjoint {i j k l : Fin m} (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (a b d e : ℕ) (t : Fin m) :
    (singleCount i a t+singleCount j b t)+singleCount k d t=0 ∨ singleCount l e t=0 := by
  by_cases ht : t=l
  · left
    simp [singleCount, ht, hil.symm, hjl.symm, hkl.symm]
  · right
    simp [singleCount, ht]

theorem integral_orthant_fourPowers (c : ℝ) {i j k l : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (a b d e : ℕ) :
    ∫ x in orthantIic c, rho 1 x*((x i)^a*(x j)^b*(x k)^d*(x l)^e) =
      Phi c^m*(normMoment a c*normMoment b c*normMoment d c*normMoment e c) := by
  have ht := integral_orthant_monomial_normalized
    (fun t => ((singleCount i a t+singleCount j b t)+singleCount k d t)+singleCount l e t) c
  simp_rw [coordMonomial_add_counts, monomial_singleCount] at ht
  rw [prod_normMoment_add_counts _ _ (singleCount_three_disjoint hil hjl hkl a b d e),
    prod_normMoment_add_counts _ _ (singleCount_sum_disjoint hik hjk a b d),
    prod_normMoment_add_counts _ _ (singleCount_disjoint hij a b),
    prod_normMoment_singleCount, prod_normMoment_singleCount,
    prod_normMoment_singleCount, prod_normMoment_singleCount] at ht
  exact ht

#print axioms integral_orthant_twoPowers
#print axioms integral_orthant_fourPowers
end SimplexFull.Covariance