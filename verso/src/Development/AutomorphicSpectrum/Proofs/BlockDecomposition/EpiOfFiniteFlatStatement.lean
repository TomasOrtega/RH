import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Dblock.epiOfFF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEpiOfFiniteFlat.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.epi_of_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)
