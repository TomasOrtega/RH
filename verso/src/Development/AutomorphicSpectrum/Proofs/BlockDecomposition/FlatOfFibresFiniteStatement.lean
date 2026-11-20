import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFlatOfFibresFinite.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)
