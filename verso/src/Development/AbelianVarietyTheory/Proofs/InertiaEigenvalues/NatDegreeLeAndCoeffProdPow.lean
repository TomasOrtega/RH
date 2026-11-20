import Mathlib

universe u_1 u_2

namespace GlobalTheory.ProductDegreeCoefficient

open Polynomial

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Take `⟨ih1, ih2⟩` from `ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]`.

Establish `h1 : (p a ^ e a).natDegree ≤ e a`. Use `Polynomial.natDegree_pow_le_of_le (e a) (h a)` as an intermediate fact. Simplify using `using this`. Establish `h2 : (p a ^ e a).coeff (e a) = (p a).coeff 1 ^ e a`. Use `Polynomial.coeff_pow_of_natDegree_le (m := e a) (h a)` as an intermediate fact.

Simplify using `using this`. Use `⟨Polynomial.natDegree_mul_le_of_le h1 ih1, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih1, h2, ih2]`.
-/
theorem natDegree_le_and_coeff_prod_pow {B : Type u_1} [CommRing B] {T : Type u_2}
    (s : Finset T) (p : T → Polynomial B) (e : T → ℕ)
    (h : ∀ t : T, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a ^ e a).natDegree ≤ e a := by
      have := Polynomial.natDegree_pow_le_of_le (e a) (h a)
      simpa using this
    have h2 : (p a ^ e a).coeff (e a) = (p a).coeff 1 ^ e a := by
      have := Polynomial.coeff_pow_of_natDegree_le (m := e a) (h a)
      simpa using this
    refine ⟨Polynomial.natDegree_mul_le_of_le h1 ih1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih1, h2, ih2]

end GlobalTheory.ProductDegreeCoefficient
