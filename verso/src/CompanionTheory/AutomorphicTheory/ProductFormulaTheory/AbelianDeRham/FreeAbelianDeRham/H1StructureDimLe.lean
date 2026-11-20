import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QIsoAtRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinOfBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalKrullDimLeOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAndFinrankLe

namespace MainStatements.Hodge.Free

/- English proof (translation)
Establish `hCx` using `GlobalTheory.CompanionTheory.HodgeCx.cxSt`. Establish `hDict` using `GlobalTheory.CompanionTheory.Dict.dictSt`. Establish `hLow` using `GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt hDict`. Establish `hHtpy` using `GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt hCx`. Establish `hQ` using `GlobalTheory.CompanionTheory.QCalc.qCalcSt hCx`.

Establish `hFub` using `GlobalTheory.CompanionTheory.NerveCoh.fubiniSt hCx`. Establish `hAff` using `GlobalTheory.CompanionTheory.AffAcyc.main hCx hHtpy`. Establish `hDesc` using `GlobalTheory.CompanionTheory.Descent.descentSt hCx hHtpy hQ hFub hAff`. Establish `hBC` using `GlobalTheory.CompanionTheory.SysBC.sysBCSt hDesc hLow`. Establish `hStein` using `GlobalTheory.CompanionTheory.Hodge.stein_holds`.

Establish `hAx` using `GlobalTheory.CompanionTheory.Axis.axOSt hDesc hLow hBC hStein`. Establish `hVan` using `GlobalTheory.CompanionTheory.Hodge.vanSt hCx (GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt hCx)`. Establish `hHopf` using `GlobalTheory.CompanionTheory.HopfSys.hopfSt hHtpy hQ hFub hAff hDesc hLow hAx`. Establish `hHopfLe` using `GlobalTheory.CompanionTheory.HopfLe.hopfLeSt hCx hDict hLow`. Conclude with `GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds.h1Le hDesc hLow hStein hVan hHopf hHopfLe`.
-/
theorem h1Le : CompanionTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  have hCx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
  have hDict := GlobalTheory.CompanionTheory.Dict.dictSt
  have hLow := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt hDict
  have hHtpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt hCx
  have hQ := GlobalTheory.CompanionTheory.QCalc.qCalcSt hCx
  have hFub := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt hCx
  have hAff := GlobalTheory.CompanionTheory.AffAcyc.main hCx hHtpy
  have hDesc := GlobalTheory.CompanionTheory.Descent.descentSt hCx hHtpy hQ hFub hAff
  have hBC := GlobalTheory.CompanionTheory.SysBC.sysBCSt hDesc hLow
  have hStein := GlobalTheory.CompanionTheory.Hodge.stein_holds
  have hAx := GlobalTheory.CompanionTheory.Axis.axOSt hDesc hLow hBC hStein
  have hVan := GlobalTheory.CompanionTheory.Hodge.vanSt hCx (GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt hCx)
  have hHopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt hHtpy hQ hFub hAff hDesc hLow hAx
  have hHopfLe := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt hCx hDict hLow
  exact GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds.h1Le hDesc hLow hStein hVan hHopf hHopfLe

end MainStatements.Hodge.Free
