import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.ConjAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.IdeleStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.InvFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdLine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.MemOrd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.MemDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.LineEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.PosEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.StdHerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.LineSkew
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.BaseEx

namespace UpperTheory.Gal.TP.Skew

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineEx_holds : LineEx := lineEx ordAut (ordLine conjAut (ideleStep conjAut) ordEmb invFun ordAut) memOrd memDual

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem spacesEx_holds : SpacesEx := spacesEx_of lineEx_holds posEx stdHerm lineSkew

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem baseEx_holds : BaseEx := baseEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem skewLine_holds : SkewLine := skewLine_of spacesEx_holds baseEx_holds

end UpperTheory.Gal.TP.Skew
