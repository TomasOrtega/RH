import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

/- English proof (translation)
Introduce `E _ _ _ a π₀`. Use `⟨UpperTheory.V.Cm.ofRep π₀, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(π₀.carrier.map (UpperTheory.V.Cm.ofCusp E a)).map _ = _`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.KernelIndexFullLattice.brRep_holds :
    UpperTheory.V.KernelIndexFullLattice.BrRep := by
  intro E _ _ _ a π₀
  refine ⟨UpperTheory.V.Cm.ofRep π₀, ?_⟩
  change (π₀.carrier.map (UpperTheory.V.Cm.ofCusp E a)).map _ = _
  rw [← Submodule.map_comp]
  rfl
