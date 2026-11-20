import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `F _ _ n χ hχ`. Use `⟨fun τ i => ((Polynomial.map τ χ).roots.toList).getD i 0, ?_⟩` and prove the remaining obligations. Introduce `τ`. Establish `hc : ((Polynomial.map τ χ).roots.toList).length = n`. Rewrite using `[Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, hχ]`.

Establish `hl : List.ofFn (fun i : Fin n => ((Polynomial.map τ χ).roots.toList).getD i 0) = (Polynomial.map τ χ).roots.toList`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using `[hc]`. Introduce `i h1 h2`. Simplify using `[List.getElem?_eq_getElem h2]`.

Use `show (Polynomial.map τ χ).roots = _`. Rewrite using `[Fin.univ_val_map, hl, Multiset.coe_toList]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.listsEx_of :
    ListsEx := by
  intro F _ _ n χ hχ
  classical
  refine ⟨fun τ i => ((Polynomial.map τ χ).roots.toList).getD i 0, ?_⟩
  intro τ
  have hc : ((Polynomial.map τ χ).roots.toList).length = n := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, hχ]
  have hl : List.ofFn (fun i : Fin n => ((Polynomial.map τ χ).roots.toList).getD i 0)
      = (Polynomial.map τ χ).roots.toList := by
    apply List.ext_getElem
    · simp [hc]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]
  show (Polynomial.map τ χ).roots = _
  rw [Fin.univ_val_map, hl, Multiset.coe_toList]
