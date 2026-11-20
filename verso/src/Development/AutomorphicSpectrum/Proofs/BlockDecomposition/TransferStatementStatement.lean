import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatement
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.transfer_statement : PositivityTheory.RgDs.K.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | exact GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgKeyTransfer.transfer <;> assumption)
