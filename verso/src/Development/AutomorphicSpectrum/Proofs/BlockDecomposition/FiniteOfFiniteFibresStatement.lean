import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.finite_of_finite_fibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)
