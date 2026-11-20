import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTwo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCertProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTracePow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCentralEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtHecke
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFormGU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ZetaMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCentralEig2Of
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig2Of
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocAdj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PRootsAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFinToHecke
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PClassFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PXiScalar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PXiZeta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLevOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntCompact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLevCompact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ExistsOpenAvoid
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PNbhdU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSphType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PStepAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MemLevUpdateOfErase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSatVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKerFormU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PHeckePres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKapOf

namespace UpperTheory.Gal.CertificateRingHomMap

universe u v

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem projOne_holds : ProjOne.{u} := pProjOne_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem projTwo_holds : ProjTwo.{u, v} := pProjTwo_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem certProj_holds : CertProj.{u} := pCertProj_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem projTrace_holds : ProjTrace.{u} := pProjTrace_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tracePow_holds : TracePow.{u} := pTracePow_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extZero_holds : ExtZero := pExtZero_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem centralEig_holds : CentralEig := pCentralEig_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extEig_holds : ExtEig := pExtEig_holds extZero_holds centralEig_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extHecke_holds : ExtHecke := pExtHecke_holds extEig_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem centralEig2_holds : CentralEig2 := pCentralEig2_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extEig2_holds : ExtEig2 := pExtEig2_of extZero_holds centralEig2_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locAdj_holds : LocAdj := pLocAdj_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootsAlg_holds : RootsAlg := pRootsAlg_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finToHecke_holds : FinToHecke := pFinToHecke_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classFin_holds : ClassFin := pClassFin_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiScalar_holds : XiScalar := pXiScalar_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiZeta_holds : XiZeta := pXiZeta_of xiScalar_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intConj_holds : IntConj := pIntConj_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intSim_holds : IntSim := pIntSim_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ofUBij_holds : OfUBij := pOfUBij_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locComm_holds : LocComm := pLocComm_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locMem_holds : LocMem := pLocMem_of intConj_holds locComm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levOpen_holds : LevOpen := pLevOpen_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intCompact_holds : IntCompact := pIntCompact_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levCompact_holds : LevCompact := pLevCompact_of intCompact_holds intConj_holds locComm_holds levOpen_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nhds_basis_levelSubgroup : Nbhd2 := pNbhd2_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nbhdU_holds : NbhdU := pNbhdU_of nhds_basis_levelSubgroup intConj_holds locComm_holds ofUBij_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphType_holds : SphType := pSphType_of intConj_holds locComm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepAt_holds : StepAt := pStepAt_of locAdj_holds locComm_holds ofUBij_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem vecU_holds : VecU := pVecU_of nbhdU_holds stepAt_holds sphType_holds locComm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satVal_holds : SatVal := pSatVal_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kerFormU_holds : KerFormU := pKerFormU_of ofUBij_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heckePres_holds : HeckePres := pHeckePres_of locComm_holds locMem_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kapOf_holds : KapOf := pKapOf_of finToHecke_holds xiZeta_holds intSim_holds levOpen_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formGU_holds : FormGU :=
  pFormGU_of extEig2_holds classFin_holds xiZeta_holds kerFormU_holds heckePres_holds satVal_holds locMem_holds locComm_holds
    levOpen_holds ofUBij_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem seedGU_holds : SeedGU :=
  seedGU_of zetaEx_holds vecU_holds sphType_holds formGU_holds kapOf_holds levOpen_holds levCompact_holds

end UpperTheory.Gal.CertificateRingHomMap
