import Formalism.FockGram.StatementFock

open MvPolynomial

namespace Formalism.E

/- English proof (translation)
Introduce `R τ _ _ f g`. Unfold `Formalism.E.fock`. Rewrite using `[star_sum]`. Establish `hf : ∀ m ∉ f.support, f.coeff m = 0` using `fun m h => by simpa using h`. Establish `hg : ∀ m ∉ g.support, g.coeff m = 0` using `fun m h => by simpa using h`.

Establish `e1 : ∑ m ∈ f.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) = ∑ m ∈ f.support ∪ g.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R))` using `Finset.sum_subset Finset.subset_union_left (fun m _ hm => by simp [hf m hm])`. Establish `e2 : ∑ m ∈ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) = ∑ m ∈ f.support ∪ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R)` using `Finset.sum_subset Finset.subset_union_right (fun m _ hm => by simp [hg m hm])`. Rewrite using `[e1, e2]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `[star_mul, mul_comm, mul_left_comm]`.
-/
theorem fischerInnerConjSymm_holds : FockHerm := by
  intro R τ _ _ f g
  classical
  unfold Formalism.E.fock
  rw [star_sum]
  have hf : ∀ m ∉ f.support, f.coeff m = 0 := fun m h => by simpa using h
  have hg : ∀ m ∉ g.support, g.coeff m = 0 := fun m h => by simpa using h
  have e1 : ∑ m ∈ f.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) =
      ∑ m ∈ f.support ∪ g.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) :=
    Finset.sum_subset Finset.subset_union_left (fun m _ hm => by simp [hf m hm])
  have e2 : ∑ m ∈ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) =
      ∑ m ∈ f.support ∪ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) :=
    Finset.sum_subset Finset.subset_union_right (fun m _ hm => by simp [hg m hm])
  rw [e1, e2]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [star_mul, mul_comm, mul_left_comm]

end Formalism.E
