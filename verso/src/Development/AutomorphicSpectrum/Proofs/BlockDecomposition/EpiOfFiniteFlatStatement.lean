import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.epi_of_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)
