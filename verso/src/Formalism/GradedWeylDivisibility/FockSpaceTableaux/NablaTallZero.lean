import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_one]`. Use `split_ifs with hk`. Substitute `hk` using the available equality. Simplify using `using isWeightedHomogeneous_one (R := ℚ) (w := (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)))`.

Conclude with `fun d hd => (hd (coeff_zero d)).elim`.
-/
private lemma isWH_coeff_one_polynomial {r n : ℕ} (δ : ℕ) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ))
      ((1 : Polynomial (MvPolynomial (Fin r × Fin n) ℚ)).coeff k) (0 + k * δ) := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with hk
  · subst hk
    simpa using isWeightedHomogeneous_one (R := ℚ) (w := (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)))
  · exact fun d hd => (hd (coeff_zero d)).elim

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Use `IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_` and prove the remaining obligations. Establish `h` using `(hp x.1).mul (hq x.2)`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[← hx]`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma isWH_coeff_mul_of_isWH_coeff {r n : ℕ} (δ : ℕ) (p q : Polynomial (MvPolynomial (Fin r × Fin n) ℚ)) (d e : ℕ)
    (hp : ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) (p.coeff k) (d + k * δ))
    (hq : ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) (q.coeff k) (e + k * δ)) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((p * q).coeff k) (d + e + k * δ) := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have h := (hp x.1).mul (hq x.2)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]
  convert h using 1
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isWH_coeff_one_polynomial (r := r) (n := n) δ`. Consider the case `@insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `isWH_coeff_mul_of_isWH_coeff δ _ _ _ _ (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
private lemma isWH_coeff_prod_of_isWH_coeff {r n : ℕ} (δ : ℕ) {ι : Type} (s : Finset ι)
    (p : ι → Polynomial (MvPolynomial (Fin r × Fin n) ℚ)) (d : ι → ℕ)
    (h : ∀ i ∈ s, ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((p i).coeff k) (d i + k * δ)) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((∏ i ∈ s, p i).coeff k) (∑ i ∈ s, d i + k * δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWH_coeff_one_polynomial (r := r) (n := n) δ
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isWH_coeff_mul_of_isWH_coeff δ _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Formalism.GradedWeylDivisibility
