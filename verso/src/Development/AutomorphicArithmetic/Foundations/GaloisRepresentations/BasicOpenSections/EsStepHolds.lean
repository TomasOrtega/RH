import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGalEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHopOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EtOfRestrict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PLiesOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFixDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PTowES
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PPlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGrPass
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsGenAll

namespace UpperTheory.Gal.Mod

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hopOp_holds : HopOp := hopOp @galEx @corrOpEq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem towES_holds : TowES := towES esGen_all bcEx (liesOp hopOp_holds @opCover) (fixDesc hopOp_holds)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem esStep_holds : UpperTheory.Gal.Int.Geo.ESStep := esStep towES_holds placeData grPass

end UpperTheory.Gal.Mod
