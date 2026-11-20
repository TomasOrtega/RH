import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `B B' _ _ ρ ι J _ _ I _ a v`. Establish `hf : ∀ c : ι → B, Polynomial.map (MvPolynomial.map ρ) (form c) = form (fun k => ρ (c k))`. Introduce `c`. Simplify using `[form, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]`. Establish `key : ∀ (m : J → Multiset (ι → B')) (s : Finset J), (Multiset.map form (∑ j ∈ s, a j • m j)).prod = ∏ j ∈ s, (Multiset.map form (m j)).prod ^ a j`.

Introduce `m s`. Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add, Multiset.prod_add, ih, Multiset.map_nsmul, Multiset.prod_nsmul]`. Simplify using `only [pts, mapP]`.

Rewrite using `[key, Polynomial.map_prod]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.map_pow, Polynomial.map_prod, Multiset.map_map]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_multiset_prod]`.

Simplify using `[Function.comp_def, hf]`.
-/
theorem UpperTheory.Gal.crystallineComparison.ptsProd_of :
    PtsProd := by
  intro B B' _ _ ρ ι J _ _ I _ a v
  have hf : ∀ c : ι → B, Polynomial.map (MvPolynomial.map ρ) (form c) = form (fun k => ρ (c k)) := by
    intro c
    simp [form, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  have key : ∀ (m : J → Multiset (ι → B')) (s : Finset J),
      (Multiset.map form (∑ j ∈ s, a j • m j)).prod = ∏ j ∈ s, (Multiset.map form (m j)).prod ^ a j := by
    intro m s
    classical
    refine Finset.induction_on s (by simp) ?_
    intro j s hj ih
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add, Multiset.prod_add, ih,
      Multiset.map_nsmul, Multiset.prod_nsmul]
  simp only [pts, mapP]
  rw [key, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_pow, Polynomial.map_prod, Multiset.map_map]
  congr 1
  rw [Finset.prod_eq_multiset_prod]
  simp [Function.comp_def, hf]
