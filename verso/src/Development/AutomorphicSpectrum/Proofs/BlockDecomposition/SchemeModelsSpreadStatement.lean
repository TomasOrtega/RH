import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSchemeModelsSpread.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.scheme_models_spread : GlobalTheory.SpreadingModels.SchemeModels := by
  first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)
