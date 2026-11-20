import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPOfDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports

namespace UpperTheory.V.Z.Int

/- English proof (translation)
The claim follows from `intP_of_desc UpperTheory.Gal.Desc.descOffT`.
-/
theorem intP_holds : UpperTheory.V.Br.IntP := intP_of_desc UpperTheory.Gal.Desc.descOffT

/- English proof (translation)
The claim follows from `intK_of_desc UpperTheory.Gal.Desc.descOffT`.
-/
theorem intK_holds : UpperTheory.V.Af.IntK := intK_of_desc UpperTheory.Gal.Desc.descOffT

/- English proof (translation)
Introduce `_` and use `intP_holds`.
-/
theorem intP' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := fun _ => intP_holds

/- English proof (translation)
Introduce `_` and use `intK_holds`.
-/
theorem intK' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := fun _ => intK_holds

/- English proof (translation)
The claim follows from `@intK'`.
-/
example : type_of% @UpperTheory.V.Af.intK := @intK'

/- English proof (translation)
The claim follows from `@intP'`.
-/
example : type_of% @UpperTheory.V.Br.intP := @intP'

end UpperTheory.V.Z.Int
