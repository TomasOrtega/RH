import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

/- English proof (translation)
Introduce `_ _ _ _ _ _ π v` and use `UpperTheory.V.TR.Cen.exists_hasInfChar π v`.
-/
theorem UpperTheory.V.Lit.infEx :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lit.InfEx :=
  fun _ _ _ _ _ _ π v => UpperTheory.V.TR.Cen.exists_hasInfChar π v
