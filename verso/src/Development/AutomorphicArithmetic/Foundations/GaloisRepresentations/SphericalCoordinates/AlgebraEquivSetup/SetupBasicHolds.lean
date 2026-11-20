import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PBarEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDeltaEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDiagTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormOKSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHdSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLiftEx
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSqrtNeg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrbEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTraceType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PUnitMod
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKqEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrient
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSigSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtPEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDomSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPosGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupEx

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
The claim follows from `pBarEx`.
-/
theorem BarEx_holds : BarEx := pBarEx
/- English proof (translation)
The claim follows from `pCEx`.
-/
theorem CEx_holds : CEx := pCEx
/- English proof (translation)
The claim follows from `pCodiffGen`.
-/
theorem CodiffGen_holds : CodiffGen := pCodiffGen
/- English proof (translation)
The claim follows from `pDeltaEx`.
-/
theorem DeltaEx_holds : DeltaEx := pDeltaEx
/- English proof (translation)
The claim follows from `pDiagTrace`.
-/
theorem DiagTrace_holds : DiagTrace := pDiagTrace
/- English proof (translation)
The claim follows from `pFormOKSt`.
-/
theorem FormOKSt_holds : FormOKSt := pFormOKSt
/- English proof (translation)
The claim follows from `pFormPerfSt`.
-/
theorem FormPerfSt_holds : FormPerfSt := pFormPerfSt
/- English proof (translation)
The claim follows from `pHdSign`.
-/
theorem HdSign_holds : HdSign := pHdSign
/- English proof (translation)
The claim follows from `pIdemEx`.
-/
theorem IdemEx_holds : IdemEx := pIdemEx
/- English proof (translation)
The claim follows from `pLiftEx`.
-/
theorem LiftEx_holds : LiftEx := pLiftEx
/- English proof (translation)
The claim follows from `pOrbEx`.
-/
theorem OrbEx_holds : OrbEx := pOrbEx
/- English proof (translation)
The claim follows from `pPerfCof`.
-/
theorem PerfCof_holds : PerfCof := pPerfCof
/- English proof (translation)
The claim follows from `pPerfOf`.
-/
theorem PerfOf_holds : PerfOf := pPerfOf
/- English proof (translation)
The claim follows from `pQuadEx`.
-/
theorem QuadEx_holds : QuadEx := pQuadEx
/- English proof (translation)
The claim follows from `pRepAdj`.
-/
theorem RepAdj_holds : RepAdj := pRepAdj
/- English proof (translation)
The claim follows from `pRepEx`.
-/
theorem RepEx_holds : RepEx := pRepEx
/- English proof (translation)
The claim follows from `pRepLaws`.
-/
theorem RepLaws_holds : RepLaws := pRepLaws
/- English proof (translation)
The claim follows from `pSetupBasic`.
-/
theorem SetupBasic_holds : SetupBasic := pSetupBasic
/- English proof (translation)
The claim follows from `pTraceType`.
-/
theorem TraceType_holds : TraceType := pTraceType
/- English proof (translation)
The claim follows from `pUEx`.
-/
theorem UEx_holds : UEx := pUEx
/- English proof (translation)
The claim follows from `pUnitMod`.
-/
theorem UnitMod_holds : UnitMod := pUnitMod
/- English proof (translation)
The claim follows from `pCodiffUnit UnitMod_holds`.
-/
theorem CodiffUnit_holds : CodiffUnit := pCodiffUnit UnitMod_holds
/- English proof (translation)
The claim follows from `pFormCoord TraceType_holds`.
-/
theorem FormCoord_holds : FormCoord := pFormCoord TraceType_holds
/- English proof (translation)
The claim follows from `pKqEx TraceType_holds`.
-/
theorem KqEx_holds : KqEx := pKqEx TraceType_holds
/- English proof (translation)
The claim follows from `pOrient TraceType_holds HdSign_holds`.
-/
theorem Orient_holds : Orient := pOrient TraceType_holds HdSign_holds
/- English proof (translation)
The claim follows from `pRealIso TraceType_holds`.
-/
theorem RealIso_holds : RealIso := pRealIso TraceType_holds
/- English proof (translation)
The claim follows from `pSigSt HdSign_holds`.
-/
theorem SigSt_holds : SigSt := pSigSt HdSign_holds
/- English proof (translation)
The claim follows from `pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds`.
-/
theorem AtPEx_holds : AtPEx := pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds
/- English proof (translation)
The claim follows from `pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds`.
-/
theorem DomSt_holds : DomSt := pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds
/- English proof (translation)
The claim follows from `pPosGen CodiffUnit_holds`.
-/
theorem PosGen_holds : PosGen := pPosGen CodiffUnit_holds
/- English proof (translation)
The claim follows from `pRealGen CodiffGen_holds CodiffUnit_holds`.
-/
theorem RealGen_holds : RealGen := pRealGen CodiffGen_holds CodiffUnit_holds
/- English proof (translation)
The claim follows from `pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds`.
-/
theorem SetupEx_holds : SetupEx := pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds

end UpperTheory.Gal.W2.Seed
