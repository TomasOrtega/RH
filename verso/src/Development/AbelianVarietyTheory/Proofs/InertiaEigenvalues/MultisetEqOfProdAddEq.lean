import Mathlib

namespace GlobalTheory.MultisetOfProduct

open Polynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem eval_prod_neg (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
  simp [sub_neg_eq_add]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
