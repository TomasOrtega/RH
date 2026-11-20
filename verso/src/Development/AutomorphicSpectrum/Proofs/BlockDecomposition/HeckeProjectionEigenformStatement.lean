import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeProjectionEigenform.lean&line=396#L396)
-/
theorem _root_.GlobalTheory.T.hecke_projection_eigenform : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.G6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 | exact GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 <;> assumption)
