import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsoOfThickenings.lean&line=363#L363)
-/
theorem _root_.GlobalTheory.T.iso_of_thickenings : IsoOfThick := by
  first | exact @GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | exact GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | (intros; apply GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick <;> assumption)
