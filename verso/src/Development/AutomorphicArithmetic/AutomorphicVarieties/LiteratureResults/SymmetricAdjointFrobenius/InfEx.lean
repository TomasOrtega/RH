import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.infEx :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lit.InfEx :=
  fun _ _ _ _ _ _ π v => UpperTheory.V.TR.Cen.exists_hasInfChar π v
