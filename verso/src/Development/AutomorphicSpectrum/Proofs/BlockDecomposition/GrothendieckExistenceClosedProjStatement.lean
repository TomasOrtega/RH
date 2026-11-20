import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedProj
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGrothendieckExistenceClosedProj.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.grothendieck_existence_closed_proj : GEClosedProj := by
  first | exact @GlobalTheory.CompanionTheory.GE.geClosedProj | exact GlobalTheory.CompanionTheory.GE.geClosedProj | (intros; apply GlobalTheory.CompanionTheory.GE.geClosedProj <;> assumption)
