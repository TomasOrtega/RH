import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEmbSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.MapUnivAdd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatId
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpOfHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PBaseNG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExHolds

namespace UpperTheory.Gal.TP.Sub

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem upOf : UpOf := upOf_holds embSplit_holds wtId_holds satId_holds UpperTheory.Gal.TP.Loc.liftSatU_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem baseNG : BaseNG := baseNG_holds UpperTheory.Gal.TP.Skew.skewLine_holds

end UpperTheory.Gal.TP.Sub
