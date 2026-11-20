import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.satK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.SatK := by
  intro P K _ _ _ n M π hπ w hw
  obtain ⟨⟨σ, hσ⟩, h⟩ := locCompC P K n π w
  exact sat_of_isotypic (satLoc P) π.finPart hπ w hw σ (h σ hσ)
