import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.HeadOfSiegel
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelDeg

/- English proof (translation)
The claim follows from `PositivityTheory.PfWsf.Top.head_of_deg GlobalTheory.CompanionTheory.WeilSiegel.Deg.siegelDeg`.
-/
theorem PositivityTheory.Rg.Wsf.weilSiegelFormula : GlobalTheory.Published.WeilSiegelFormula :=
  PositivityTheory.PfWsf.Top.head_of_deg GlobalTheory.CompanionTheory.WeilSiegel.Deg.siegelDeg
