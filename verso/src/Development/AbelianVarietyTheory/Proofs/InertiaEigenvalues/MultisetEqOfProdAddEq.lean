import Mathlib

namespace GlobalTheory.MultisetOfProduct

open Polynomial

/- English proof (translation)
Rewrite using `[Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)` and prove the remaining obligations. Simplify using `[sub_neg_eq_add]`.
-/
theorem eval_prod_neg (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
  simp [sub_neg_eq_add]

/- English proof (translation)
Establish `hp : ((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod = ((m'.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[eval_prod_neg, eval_prod_neg]`. Conclude with `h u`.

Establish `hr` using `congrArg Polynomial.roots hp`. Rewrite `hr` using `[Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C]`. Conclude with `Multiset.map_injective neg_injective hr`.
-/
theorem multiset_eq_of_prod_add_eq {m m' : Multiset ℂ}
    (h : ∀ (u : ℂ), Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m)
      = Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m')) : m = m' := by

  have hp : ((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod =
      ((m'.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_neg, eval_prod_neg]
    exact h u
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

end GlobalTheory.MultisetOfProduct
