import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)
