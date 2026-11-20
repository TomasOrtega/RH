import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemes
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFormalAlgebraisationSchemes.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.formal_algebraisation_schemes : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | exact GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj <;> assumption)
