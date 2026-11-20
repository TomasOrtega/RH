import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
