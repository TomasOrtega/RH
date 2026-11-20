import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedSs

/- English proof (translation)
The claim follows from `UpperTheory.V.Lev.fixedSs UpperTheory.V.Lev.flagPol (UpperTheory.V.Lev.fixedDvd P) (UpperTheory.V.Lev.fixedUnr P)`.
-/
theorem UpperTheory.V.Lev.fixedAll (P : UpperTheory.V.Af.Hypotheses₂) : UpperTheory.V.Lev.FixedSs :=
  UpperTheory.V.Lev.fixedSs UpperTheory.V.Lev.flagPol (UpperTheory.V.Lev.fixedDvd P) (UpperTheory.V.Lev.fixedUnr P)
