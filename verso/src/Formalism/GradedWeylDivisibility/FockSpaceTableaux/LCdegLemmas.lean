import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Rewrite using `[degreeOf_eq_sup]`. Use `Finset.sup_le fun m hm => ?_` and prove the remaining obligations. Establish `hm' : m ∈ (monomial (Finsupp.single j 1) (1 : R)).support` using `hm`. Take `rfl` from `Finset.mem_singleton.mp (support_monomial_subset hm')`. Rewrite using `[Finsupp.single_apply]`.
-/
theorem lcdeg_degreeOf_X_le {σ R : Type*} [CommRing R] [DecidableEq σ] (i j : σ) :
    degreeOf i (X j : MvPolynomial σ R) ≤ if j = i then 1 else 0 := by
  rw [degreeOf_eq_sup]
  refine Finset.sup_le fun m hm => ?_
  have hm' : m ∈ (monomial (Finsupp.single j 1) (1 : R)).support := hm
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hm')
  rw [Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq]`. Establish `key : ∀ m ∈ p.support, degreeOf c (algebraMap R (MvPolynomial τ R) (coeff m p) * ∏ v ∈ m.support, f v ^ m v) ≤ d`. Introduce `m hm`. Rewrite using `[algebraMap_eq]`. Use `(degreeOf_C_mul_le _ _ _).trans ?_` and prove the remaining obligations.

Conclude with `(degreeOf_prod_le _ _ _).trans ((Finset.sum_le_sum fun v _ => degreeOf_pow_le _ _ _).trans (h m hm))`. Use `clear h`. Generalize the expression as in `p.support = s at key ⊢`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(degreeOf_add_le _ _ _).trans (max_le (key a (Finset.mem_insert_self _ _)) (ih fun m hm => key m (Finset.mem_insert_of_mem hm)))`.
-/
theorem lcdeg_degreeOf_aeval_le {σ τ R : Type*} [CommRing R] (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (c : τ) (d : ℕ)
    (h : ∀ m ∈ p.support, ∑ v ∈ m.support, m v * degreeOf c (f v) ≤ d) :
    degreeOf c (aeval f p) ≤ d := by
  classical
  rw [aeval_def, eval₂_eq]
  have key : ∀ m ∈ p.support, degreeOf c (algebraMap R (MvPolynomial τ R) (coeff m p) *
      ∏ v ∈ m.support, f v ^ m v) ≤ d := by
    intro m hm
    rw [algebraMap_eq]
    refine (degreeOf_C_mul_le _ _ _).trans ?_
    exact (degreeOf_prod_le _ _ _).trans
      ((Finset.sum_le_sum fun v _ => degreeOf_pow_le _ _ _).trans (h m hm))
  clear h
  generalize p.support = s at key ⊢
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (degreeOf_add_le _ _ _).trans (max_le (key a (Finset.mem_insert_self _ _))
      (ih fun m hm => key m (Finset.mem_insert_of_mem hm)))

end Formalism.GradedWeylDivisibility
