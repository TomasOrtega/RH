import Mathlib

universe u_1 u_2

namespace GlobalTheory.AdditiveValuationProduct

/- English proof (translation)
Introduce `R _ _ _ ι s a`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j t hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]`.
-/
theorem addVal_prod : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ι : Type u_2} (s : Finset ι) (a : ι → R), (IsDiscreteValuationRing.addVal R : R → ℕ∞) (∏ i ∈ s, a i) = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R : R → ℕ∞) (a i) := by
  intro R _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

end GlobalTheory.AdditiveValuationProduct
