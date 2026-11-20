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
A detailed English derivation is pending.
-/
theorem LocFour_holds : LocFour := pLocFour
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HenselV_holds : HenselV := pHenselV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SplitRep_holds : SplitRep := pSplitRep
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockMat_holds : BlockMat := pBlockMat
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PadMap_holds : PadMap := pPadMap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Scale_holds : Scale := pScale
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TrivMat_holds : TrivMat := pTrivMat
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CongrScale_holds : CongrScale := pCongrScale
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SplitCongr_holds : SplitCongr := pSplitCongr
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem InfCongr_holds : InfCongr := pInfCongr
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DefSign_holds : DefSign := pDefSign
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelOf_holds : RelOf := pRelOf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
