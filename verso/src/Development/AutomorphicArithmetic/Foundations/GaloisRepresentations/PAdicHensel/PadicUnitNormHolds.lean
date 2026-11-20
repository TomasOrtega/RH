import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocFour
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PHenselV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBlockMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicUnitNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicSqFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PTrivMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCongrScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PInfCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDefSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRelOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocRoot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZUnitNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZSqFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAdFour
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PUnitCls
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PNormTwo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCls
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PIsoEx

namespace UpperTheory.Gal.G1

/- English proof (translation)
The claim follows from `pLocFour`.
-/
theorem LocFour_holds : LocFour := pLocFour
/- English proof (translation)
The claim follows from `pHenselV`.
-/
theorem HenselV_holds : HenselV := pHenselV
/- English proof (translation)
The claim follows from `pSplitRep`.
-/
theorem SplitRep_holds : SplitRep := pSplitRep
/- English proof (translation)
The claim follows from `pBlockMat`.
-/
theorem BlockMat_holds : BlockMat := pBlockMat
/- English proof (translation)
The claim follows from `pPadMap`.
-/
theorem PadMap_holds : PadMap := pPadMap
/- English proof (translation)
The claim follows from `pScale`.
-/
theorem Scale_holds : Scale := pScale
/- English proof (translation)
The claim follows from `pPadicUnitNorm`.
-/
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
/- English proof (translation)
The claim follows from `pPadicSqFin`.
-/
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
/- English proof (translation)
The claim follows from `pTrivMat`.
-/
theorem TrivMat_holds : TrivMat := pTrivMat
/- English proof (translation)
The claim follows from `pCongrScale`.
-/
theorem CongrScale_holds : CongrScale := pCongrScale
/- English proof (translation)
The claim follows from `pSplitCongr`.
-/
theorem SplitCongr_holds : SplitCongr := pSplitCongr
/- English proof (translation)
The claim follows from `pInfCongr`.
-/
theorem InfCongr_holds : InfCongr := pInfCongr
/- English proof (translation)
The claim follows from `pDefSign`.
-/
theorem DefSign_holds : DefSign := pDefSign
/- English proof (translation)
The claim follows from `pRelOf`.
-/
theorem RelOf_holds : RelOf := pRelOf
/- English proof (translation)
The claim follows from `pLocUnit HenselV_holds`.
-/
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
/- English proof (translation)
The claim follows from `pLocRoot HenselV_holds`.
-/
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
/- English proof (translation)
The claim follows from `pZUnitNorm PadicUnitNorm_holds`.
-/
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
/- English proof (translation)
The claim follows from `pZSqFin PadicSqFin_holds`.
-/
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
/- English proof (translation)
The claim follows from `pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds`.
-/
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
/- English proof (translation)
The claim follows from `pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds`.
-/
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
/- English proof (translation)
The claim follows from `pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds`.
-/
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
/- English proof (translation)
The claim follows from `pNormTwo AdFour_holds`.
-/
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
/- English proof (translation)
The claim follows from `pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds`.
-/
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
/- English proof (translation)
The claim follows from `pIsoEx NormTwo_holds BlockMat_holds`.
-/
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
