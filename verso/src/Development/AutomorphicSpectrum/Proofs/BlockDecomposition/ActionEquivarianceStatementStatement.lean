import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.action_equivariance_statement : PositivityTheory.RgDs.K.ActEquiv := by
  first | exact @GlobalTheory.CompanionTheory.ActEquivK.actEquiv | exact GlobalTheory.CompanionTheory.ActEquivK.actEquiv | (intros; apply GlobalTheory.CompanionTheory.ActEquivK.actEquiv <;> assumption)
