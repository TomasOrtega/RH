import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewformAOfEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV

namespace UpperTheory.V.Z.Win.RR

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h rc hrc a σ hp` and use `Gu.plainGd E Ω A w h rc hrc a σ hp`.
-/
theorem gd : GdOf := fun E Ω _ _ _ _ _ A w h rc hrc a σ hp => Gu.plainGd E Ω A w h rc hrc a σ hp

end UpperTheory.V.Z.Win.RR
