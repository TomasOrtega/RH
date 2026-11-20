import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep
open NumberField GlobalTheory.CuspRep UpperTheory.V

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.newformRep :
    UpperTheory.V.Published.NewformRep :=
  UpperTheory.V.Af.newformRepOf UpperTheory.V.Af.cuspSemisimpleReal UpperTheory.V.Af.admissibleReal
