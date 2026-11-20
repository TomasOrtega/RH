import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.RationalSuccAbove.SChainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.SEvOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SeparationCase.SSepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.SBridgeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.SStabOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.FiniteIndexCase.SFinOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveSubmatrices.PrimPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SAffOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.SPrimeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.SHeckeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SStokesOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.SHtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.SPUOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SMomOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ActHomApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.SCenOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.SGapOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SLocOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MeanLatticeCounts.CountableLatS

namespace PositivityTheory.KB

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sChain : SChain := sChain_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sEv : SEv := sEv_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sSep' : SSep := sSep_of sChain
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sBridge : SBridge := sBridge_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sStab : SStab := sStab_of sChain sBridge
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sFin : SFin := sFin_of sBridge
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sPsi : SPsi := sPsi_of sChain
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sAff : SAff := sAff_of sChain sEv sSep' sBridge
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sHecke : SHecke := sHecke_of sChain sEv sSep' sStab sFin sAff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sPU : SPU := sPU_of sHt_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sMom : SMom := TwSMInt2.sMom_of sHt_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sWhit : SWhit := sWhit_of sEv sStokes_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sCen : SCen := sCen_of sEv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sLoc : SLoc := sLoc_of sEv

end PositivityTheory.KB
