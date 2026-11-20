import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanDeriv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatAffine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PConjCharpoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatPre
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPbFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExpImm0Of
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExpImm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHolPi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerCoordLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBaseImm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtHol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtImm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtFibre
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTriCharpoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetOfCharpoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCorrChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocTan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTorusCount
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPiLattice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSimDiag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExtendEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKillsMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HSepOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDiagExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTypeCount
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTraceLat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTraceDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PNewtonPoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowSumRat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootsFull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMarkDiag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTspDiag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBallChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCspDim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFibDet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ProdTy
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEvIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumWOff

namespace UpperTheory.Gal.W2

/- English proof (translation)
The claim follows from `tanDeriv_of`.
-/
theorem TanDeriv_holds : TanDeriv := tanDeriv_of

/- English proof (translation)
The claim follows from `flatAffine_of`.
-/
theorem FlatAffine_holds : FlatAffine := flatAffine_of

/- English proof (translation)
The claim follows from `conjCharpoly_of`.
-/
theorem ConjCharpoly_holds : ConjCharpoly := conjCharpoly_of

/- English proof (translation)
The claim follows from `tanChart_of TanDeriv_holds FlatAffine_holds ConjCharpoly_holds`.
-/
theorem TanChart_holds : TanChart := tanChart_of TanDeriv_holds FlatAffine_holds ConjCharpoly_holds

/- English proof (translation)
The claim follows from `tanExists_of`.
-/
theorem TanExists_holds : TanExists := tanExists_of

/- English proof (translation)
The claim follows from `flatComp_of`.
-/
theorem FlatComp_holds : FlatComp := flatComp_of

/- English proof (translation)
The claim follows from `flatPre_of`.
-/
theorem FlatPre_holds : FlatPre := flatPre_of

/- English proof (translation)
The claim follows from `pbFlat_of FlatAffine_holds`.
-/
theorem PbFlat_holds : PbFlat := pbFlat_of FlatAffine_holds

/- English proof (translation)
The claim follows from `expImm0_of`.
-/
theorem ExpImm0_holds : ExpImm0 := expImm0_of

/- English proof (translation)
The claim follows from `expImm_of FlatComp_holds FlatPre_holds PbFlat_holds ExpImm0_holds`.
-/
theorem ExpImm_holds : ExpImm := expImm_of FlatComp_holds FlatPre_holds PbFlat_holds ExpImm0_holds

/- English proof (translation)
The claim follows from `holPi_of`.
-/
theorem HolPi_holds : HolPi := holPi_of

/- English proof (translation)
The claim follows from `perNear_of`.
-/
theorem PerNear_holds : PerNear := perNear_of

/- English proof (translation)
The claim follows from `perCoordLoc_of`.
-/
theorem PerCoordLoc_holds : PerCoordLoc := perCoordLoc_of

/- English proof (translation)
The claim follows from `perLin_of`.
-/
theorem PerLin_holds : PerLin := perLin_of

/- English proof (translation)
The claim follows from `adExists_of`.
-/
theorem AdExists_holds : AdExists := adExists_of

/- English proof (translation)
The claim follows from `baseImm_of PerNear_holds PerCoordLoc_holds`.
-/
theorem BaseImm_holds : BaseImm := baseImm_of PerNear_holds PerCoordLoc_holds

/- English proof (translation)
The claim follows from `ptFibre_of`.
-/
theorem PtFibre_holds : PtFibre := ptFibre_of

/- English proof (translation)
The claim follows from `ptHol_of HolPi_holds PtFibre_holds`.
-/
theorem PtHol_holds : PtHol := ptHol_of HolPi_holds PtFibre_holds

/- English proof (translation)
The claim follows from `ptImm_of FlatComp_holds FlatPre_holds PtFibre_holds ExpImm_holds`.
-/
theorem PtImm_holds : PtImm := ptImm_of FlatComp_holds FlatPre_holds PtFibre_holds ExpImm_holds

/- English proof (translation)
The claim follows from `triCharpoly_of`.
-/
theorem TriCharpoly_holds : TriCharpoly := triCharpoly_of

/- English proof (translation)
The claim follows from `detOfCharpoly_of`.
-/
theorem DetOfCharpoly_holds : DetOfCharpoly := detOfCharpoly_of

/- English proof (translation)
The claim follows from `corrChart_of AdExists_holds PerLin_holds PtFibre_holds`.
-/
theorem CorrChart_holds : CorrChart := corrChart_of AdExists_holds PerLin_holds PtFibre_holds

/- English proof (translation)
The claim follows from `locTan_of TanChart_holds PerNear_holds BaseImm_holds PtHol_holds PtImm_holds PtFibre_holds CorrChart_holds TriCharpoly_holds`.
-/
theorem LocTan_holds : LocTan := locTan_of TanChart_holds PerNear_holds BaseImm_holds PtHol_holds PtImm_holds PtFibre_holds CorrChart_holds TriCharpoly_holds

/- English proof (translation)
The claim follows from `detReal_of`.
-/
theorem DetReal_holds : DetReal := detReal_of

/- English proof (translation)
The claim follows from `torusCount_of DetReal_holds`.
-/
theorem TorusCount_holds : TorusCount := torusCount_of DetReal_holds

/- English proof (translation)
The claim follows from `piLattice_of`.
-/
theorem PiLattice_holds : PiLattice := piLattice_of

/- English proof (translation)
The claim follows from `locSum_of LocTan_holds TorusCount_holds PiLattice_holds PtFibre_holds CorrChart_holds DetOfCharpoly_holds`.
-/
theorem LocSum_holds : LocSum := locSum_of LocTan_holds TorusCount_holds PiLattice_holds PtFibre_holds CorrChart_holds DetOfCharpoly_holds

/- English proof (translation)
The claim follows from `simDiag_of`.
-/
theorem SimDiag_holds : SimDiag := simDiag_of

/- English proof (translation)
The claim follows from `extendEmb_of`.
-/
theorem ExtendEmb_holds : ExtendEmb := extendEmb_of

/- English proof (translation)
The claim follows from `killsMat_of`.
-/
theorem KillsMat_holds : KillsMat := killsMat_of

/- English proof (translation)
The claim follows from `hSep_of`.
-/
theorem HSep_holds : HSep := hSep_of

/- English proof (translation)
The claim follows from `diagExists_of SimDiag_holds ExtendEmb_holds KillsMat_holds HSep_holds`.
-/
theorem DiagExists_holds : DiagExists := diagExists_of SimDiag_holds ExtendEmb_holds KillsMat_holds HSep_holds

/- English proof (translation)
The claim follows from `typeCount_of`.
-/
theorem TypeCount_holds : TypeCount := typeCount_of

/- English proof (translation)
The claim follows from `traceLat_of`.
-/
theorem TraceLat_holds : TraceLat := traceLat_of

/- English proof (translation)
The claim follows from `traceDual_of`.
-/
theorem TraceDual_holds : TraceDual := traceDual_of

/- English proof (translation)
The claim follows from `newtonPoly_of`.
-/
theorem NewtonPoly_holds : NewtonPoly := newtonPoly_of

/- English proof (translation)
The claim follows from `powSumRat_of TraceLat_holds TraceDual_holds`.
-/
theorem PowSumRat_holds : PowSumRat := powSumRat_of TraceLat_holds TraceDual_holds

/- English proof (translation)
The claim follows from `rootsFull_of TypeCount_holds PowSumRat_holds NewtonPoly_holds KillsMat_holds`.
-/
theorem RootsFull_holds : RootsFull := rootsFull_of TypeCount_holds PowSumRat_holds NewtonPoly_holds KillsMat_holds

/- English proof (translation)
The claim follows from `markDiag_of TypeCount_holds`.
-/
theorem MarkDiag_holds : MarkDiag := markDiag_of TypeCount_holds

/- English proof (translation)
The claim follows from `tspDiag_of`.
-/
theorem TspDiag_holds : TspDiag := tspDiag_of

/- English proof (translation)
The claim follows from `ballChar_of TypeCount_holds TspDiag_holds`.
-/
theorem BallChar_holds : BallChar := ballChar_of TypeCount_holds TspDiag_holds

/- English proof (translation)
The claim follows from `cspDim_of SimDiag_holds ExtendEmb_holds TypeCount_holds MarkDiag_holds BallChar_holds`.
-/
theorem CspDim_holds : CspDim := cspDim_of SimDiag_holds ExtendEmb_holds TypeCount_holds MarkDiag_holds BallChar_holds

/- English proof (translation)
The claim follows from `fibDet_of`.
-/
theorem FibDet_holds : FibDet := fibDet_of

/- English proof (translation)
The claim follows from `fibW_of`.
-/
theorem FibW_holds : FibW := fibW_of

/- English proof (translation)
The claim follows from `evIntegral_of`.
-/
theorem EvIntegral_holds : EvIntegral := evIntegral_of

/- English proof (translation)
The claim follows from `eigTop_of AdExists_holds DiagExists_holds TypeCount_holds RootsFull_holds MarkDiag_holds BallChar_holds FibDet_holds FibW_holds EvIntegral_holds`.
-/
theorem EigTop_holds : EigTop := eigTop_of AdExists_holds DiagExists_holds TypeCount_holds RootsFull_holds MarkDiag_holds BallChar_holds FibDet_holds FibW_holds EvIntegral_holds

/- English proof (translation)
The claim follows from `rootSumW_of`.
-/
theorem RootSumW_holds : RootSumW := rootSumW_of

/- English proof (translation)
The claim follows from `rootSumWOff_of`.
-/
theorem RootSumWOff_holds : RootSumWOff := rootSumWOff_of

end UpperTheory.Gal.W2
