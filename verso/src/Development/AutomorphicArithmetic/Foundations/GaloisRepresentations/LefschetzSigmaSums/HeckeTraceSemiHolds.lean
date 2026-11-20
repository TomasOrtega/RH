import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvRoots
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvPolProps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PListsEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PRootW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHExpInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PUnifBound
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLefSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCoeffOcc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMarkRoots
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDPairPol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDSumCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGroupTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PConjRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHeckeTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGoodConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolyFnConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSpecConj

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
The claim follows from `invRoots_of`.
-/
theorem InvRoots_holds : InvRoots := invRoots_of
/- English proof (translation)
The claim follows from `invPolProps_of InvRoots_holds`.
-/
theorem InvPolProps_holds : InvPolProps := invPolProps_of InvRoots_holds
/- English proof (translation)
The claim follows from `rootW_of UpperTheory.Gal.W2.RootSumW_holds UpperTheory.Gal.W2.RootSumWOff_holds listsEx_of schWEq_of`.
-/
theorem RootW_holds : RootW :=
  rootW_of UpperTheory.Gal.W2.RootSumW_holds UpperTheory.Gal.W2.RootSumWOff_holds listsEx_of schWEq_of
/- English proof (translation)
The claim follows from `eigOf_of UpperTheory.Gal.CertificateRingHomMap.pProjOne_holds`.
-/
theorem EigOf_holds : EigOf := eigOf_of UpperTheory.Gal.CertificateRingHomMap.pProjOne_holds
/- English proof (translation)
The claim follows from `cxLin_of cxFlat_of`.
-/
theorem CxLin_holds : CxLin := cxLin_of cxFlat_of
/- English proof (translation)
The claim follows from `groupTop_of h₁ h₂ RootW_holds InvRoots_holds InvPolProps_holds markRoots_of dPairPol_of dSumCongr_of testOf_of testOne_of`.
-/
theorem GroupTop_of (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) : GroupTop :=
  groupTop_of h₁ h₂ RootW_holds InvRoots_holds InvPolProps_holds markRoots_of dPairPol_of dSumCongr_of testOf_of testOne_of
/- English proof (translation)
The claim follows from `heckeTraceSemi_of traceSemi_of`.
-/
theorem HeckeTraceSemi_holds : HeckeTraceSemi := heckeTraceSemi_of traceSemi_of
/- English proof (translation)
The claim follows from `specConj_of traceSemi_of conjRep_of HeckeTraceSemi_holds goodConj_of (schWConj_of schWEq_of) polyFnConj_of`.
-/
theorem SpecConj_holds : SpecConj :=
  specConj_of traceSemi_of conjRep_of HeckeTraceSemi_holds goodConj_of (schWConj_of schWEq_of) polyFnConj_of

end UpperTheory.Gal.LocalSmoothExtension
