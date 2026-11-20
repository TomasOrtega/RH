import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open Polynomial

namespace UpperTheory.V.Cj.S

/- English proof (translation)
Establish `key : ∀ (k : Multiset ℂ) (u : ℂ), (((k.map fun x => -x).map fun x => X - C x).prod).eval u = (k.map (u + ·)).prod`. Introduce `k u`. Rewrite using `[eval_multiset_prod, Multiset.map_map, Multiset.map_map]`. Use `congr 1`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hp : ((m.map fun x => -x).map fun x => X - C x).prod = ((n.map fun x => -x).map fun x => X - C x).prod` using `Polynomial.funext fun u => by rw [key, key, h]`. Establish `hr` using `congrArg Polynomial.roots hp`. Rewrite `hr` using `[roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C]`. Conclude with `Multiset.map_injective neg_injective hr`.
-/
private theorem eq_of_prod_eq (m n : Multiset ℂ) (h : ∀ u : ℂ, (m.map (u + ·)).prod = (n.map (u + ·)).prod) : m = n := by
  have key : ∀ (k : Multiset ℂ) (u : ℂ),
      (((k.map fun x => -x).map fun x => X - C x).prod).eval u = (k.map (u + ·)).prod := by
    intro k u
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  have hp : ((m.map fun x => -x).map fun x => X - C x).prod = ((n.map fun x => -x).map fun x => X - C x).prod :=
    Polynomial.funext fun u => by rw [key, key, h]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

/- English proof (translation)
Introduce `m m₁ m₂ α β h`. Use `eq_of_prod_eq _ _ fun u => ?_` and prove the remaining obligations. Rewrite using `[← h u, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]`. Use `congr 2`. Conclude with `Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring`.

Conclude with `Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring`.
-/
theorem capArith : CapArith := by
  intro m m₁ m₂ α β h
  refine eq_of_prod_eq _ _ fun u => ?_
  rw [← h u, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring

end UpperTheory.V.Cj.S
