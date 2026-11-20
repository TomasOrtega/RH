import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.J.muLe :
    UpperTheory.V.J.MuLe := by
  intro O Λ B K _ _ _ _ _ _ _ _ lam M _ _ _ _ _ hs y t
  unfold UpperTheory.V.J.mu
  refine (Submodule.finrank_mono (iInf_le _ t)).trans ?_
  rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.charpoly_baseChange]
  rfl
