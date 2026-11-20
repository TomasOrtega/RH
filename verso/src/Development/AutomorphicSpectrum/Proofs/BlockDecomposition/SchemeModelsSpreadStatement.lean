import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.scheme_models_spread : GlobalTheory.SpreadingModels.SchemeModels := by
  first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)
