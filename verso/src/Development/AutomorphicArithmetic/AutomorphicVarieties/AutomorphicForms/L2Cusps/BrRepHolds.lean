import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.KernelIndexFullLattice.brRep_holds :
    UpperTheory.V.KernelIndexFullLattice.BrRep := by
  intro E _ _ _ a π₀
  refine ⟨UpperTheory.V.Cm.ofRep π₀, ?_⟩
  change (π₀.carrier.map (UpperTheory.V.Cm.ofCusp E a)).map _ = _
  rw [← Submodule.map_comp]
  rfl
