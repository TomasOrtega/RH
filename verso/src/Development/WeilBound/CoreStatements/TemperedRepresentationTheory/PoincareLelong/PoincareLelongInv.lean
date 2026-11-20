import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableAbsFibreSumOfIsCxVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDivisorCompare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIdentityAll

namespace PositivityTheory.Tls2.Pl

/- English proof (translation)
The claim follows from `poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches GlobalT …`.
-/
theorem poincareLelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

/- English proof (translation)
The claim follows from `poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches Glob …`.
-/
theorem poincareLelongInv : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv :=
  poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

end PositivityTheory.Tls2.Pl
