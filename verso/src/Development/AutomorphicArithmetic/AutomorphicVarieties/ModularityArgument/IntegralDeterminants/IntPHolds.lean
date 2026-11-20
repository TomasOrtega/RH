import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPOfDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports

namespace UpperTheory.V.Z.Int

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intP_holds : UpperTheory.V.Br.IntP := intP_of_desc UpperTheory.Gal.Desc.descOffT

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intK_holds : UpperTheory.V.Af.IntK := intK_of_desc UpperTheory.Gal.Desc.descOffT

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intP' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := fun _ => intP_holds

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intK' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := fun _ => intK_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
example : type_of% @UpperTheory.V.Af.intK := @intK'

/- English proof (translation)
A detailed English derivation is pending.
-/
example : type_of% @UpperTheory.V.Br.intP := @intP'

end UpperTheory.V.Z.Int
