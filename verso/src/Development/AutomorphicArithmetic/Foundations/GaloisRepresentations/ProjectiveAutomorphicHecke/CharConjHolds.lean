import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PVecWt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PThLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrRho
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrSch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSchHom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCharConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PAutEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtAtOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PEpsIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpCore

namespace UpperTheory.Gal.CertificateRingHomMap

/- English proof (translation)
The claim follows from `pTrRho_of`.
-/
theorem trRho_holds : TrRho := pTrRho_of
/- English proof (translation)
The claim follows from `pTrSch_of`.
-/
theorem trSch_holds : TrSch := pTrSch_of
/- English proof (translation)
The claim follows from `pSchHom_of`.
-/
theorem schHom_holds : SchHom := pSchHom_of
/- English proof (translation)
The claim follows from `pCharConj_of`.
-/
theorem charConj_holds : CharConj := pCharConj_of
/- English proof (translation)
The claim follows from `pWtCore_of trRho_holds trSch_holds schHom_holds charConj_holds`.
-/
theorem wtCore_holds : WtCore := pWtCore_of trRho_holds trSch_holds schHom_holds charConj_holds
/- English proof (translation)
The claim follows from `pAutEx_of`.
-/
theorem autEx_holds : AutEx := pAutEx_of
/- English proof (translation)
The claim follows from `pWtAt_of`.
-/
theorem wtAt_holds : WtAt := pWtAt_of
/- English proof (translation)
The claim follows from `pEpsIff_of`.
-/
theorem epsIff_holds : EpsIff := pEpsIff_of
/- English proof (translation)
The claim follows from `pExpSum_of`.
-/
theorem expSum_holds : ExpSum := pExpSum_of
/- English proof (translation)
The claim follows from `pExpCore_of expSum_holds`.
-/
theorem expCore_holds : ExpCore := pExpCore_of expSum_holds

end UpperTheory.Gal.CertificateRingHomMap

namespace UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
The claim follows from `vecEx_of CertificateRingHomMap.seedGU_holds CertificateRingHomMap.wtAt_holds`.
-/
theorem vecEx_holds : VecEx := vecEx_of CertificateRingHomMap.seedGU_holds CertificateRingHomMap.wtAt_holds

/- English proof (translation)
The claim follows from `wtOf_of CertificateRingHomMap.wtCore_holds`.
-/
theorem wtOf_holds : WtOf := wtOf_of CertificateRingHomMap.wtCore_holds

/- English proof (translation)
The claim follows from `expOf_of CertificateRingHomMap.expCore_holds CertificateRingHomMap.autEx_holds CertificateRingHomMap.wtAt_holds CertificateRingHomMap.epsIff_holds`.
-/
theorem expOf_holds : ExpOf := expOf_of CertificateRingHomMap.expCore_holds CertificateRingHomMap.autEx_holds CertificateRingHomMap.wtAt_holds CertificateRingHomMap.epsIff_holds

end UpperTheory.Gal.Int.Geo.Pl
