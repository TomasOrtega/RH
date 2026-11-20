import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PLevBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PThLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSiteFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDenom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCenFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStabKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenShape
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenActs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PActsConv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.FinsumInvT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiTy
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTyFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSumDoset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemDeck
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfIdem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetCosets
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSphComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIdx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPPart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHasEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStdForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMuStar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRelOf

namespace UpperTheory.Gal.W2.Seed

open UpperTheory.Gal.Int.Geo.Pl (dict_holds sides_holds levBasic_holds)
open UpperTheory.Gal.CertificateRingHomMap (pLocComm_of pThLoc_of)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tfCen_holds : TfCen := pTfCen pAvgK pTfAdm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tfAct_holds : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tfIdem_holds : TfIdem := pTfIdem pTfAdm tfCen_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tfMulL_holds : TfMulL := pTfMulL pTfAdm tfAct_holds pDosetIff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tfMulR_holds : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tfLoc_holds : TfLoc := pTfLoc pTfAdm tfAct_holds pDosetIff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem knIff_holds : KNIff := pKNIff latCoord_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem atApart_holds : AtApart := pAtApart pJEq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levFact_holds : LevFact := pLevFact atApart_holds pIntConj
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem knIdx_holds : KNIdx := pKNIdx (pKNOpen knIff_holds)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pPart_holds : PPart := pPPart pJEq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem memAct_holds : MemAct := pMemAct pMemSum pSumDoset tfAct_holds pDosetCosets
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem memDeck_holds : MemDeck := pMemDeck pMemSum tfCen_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levSec_holds : LevSec := pLevSec pIntConj
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem knFact_holds : KNFact :=
  pKNFact knIff_holds pFacEq atApart_holds pCongGrpEx (pCongConj pLocComm_of) pLocComm pLocComm_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siteFact_holds : SiteFact := pSiteFact dict_holds sides_holds pIntConj pLocComm_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stabKer_holds : StabKer := pStabKer pFacEq knFact_holds pCongGrpEx
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem seenShape_holds : SeenShape := pSeenShape stabKer_holds siteFact_holds (pCenFacts sides_holds) levBasic_holds pLocComm_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem seenActs_holds : SeenActs := pSeenActs pMemSum memAct_holds memDeck_holds seenShape_holds levBasic_holds knIdx_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem actsConv_holds : ActsConv := pActsConv pTfAdm tfIdem_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phiTy_holds : PhiTy := pPhiTy pPart_holds levSec_holds pFacEq pLocComm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tyFact_holds : Spc.TyFact :=
  pTyFact pFacEq levSec_holds levFact_holds atApart_holds pCongGrpEx pDenom pLocComm pLocComm_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem memFn_holds : Spc.MemFn := pMemFn seenShape_holds seenActs_holds actsConv_holds tyFact_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phiEx_holds : Spc.PhiEx :=
  pPhiEx phiTy_holds seenShape_holds seenActs_holds tyFact_holds tfAct_holds tfCen_holds (tEig_of_thLoc (pThLoc_of pLocComm_of CertificateRingHomMap.pOfUBij_of)) atApart_holds pFacEq pJEq
    pLocComm

end UpperTheory.Gal.W2.Seed
