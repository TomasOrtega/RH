import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteOfFiniteFibres.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.finite_of_finite_fibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)
